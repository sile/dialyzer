%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2006-2010. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

-module(dialyzer_worker).

-export([launch/3]).

-type worker() :: pid().

-record(state, {
	  mode             :: dialyzer_coordinator:mode(),
	  scc         = [] :: mfa_or_funlbl(),
	  depends_on  = [] :: list(),
	  coordinator      :: dialyzer_coordinator:coordinator(),
	  servers          :: dialyzer_typesig:servers(),
	  scc_data         :: dialyzer_typesig:scc_data()
	 }).

-include("dialyzer.hrl").

%% -define(DEBUG, true).

-ifdef(DEBUG).
-define(debug(X__, Y__), io:format(X__, Y__)).
-else.
-define(debug(X__, Y__), ok).
-endif.

%%--------------------------------------------------------------------

-spec launch(dialyzer_coordinator:mode(), [mfa_or_funlbl()],
	     dialyzer_typesig:servers()) -> worker().

launch(Mode, SCC, Servers) ->
  State = #state{mode        = Mode,
		 scc         = SCC,
		 servers     = Servers,
		 coordinator = self()},
  spawn(fun() -> loop(initializing, State) end).

%%--------------------------------------------------------------------

loop(updating, State) ->
  ?debug("Update: ~p\n",[State#state.scc]),
  NextStatus =
    case waits_more_success_typings(State) of
      true -> waiting;
      Other ->
	case has_data(State) of
	  false -> getting_data;
	  true ->
	    case Other of
	      imminent -> waiting;
	      false -> running
	    end
	end
    end,
  loop(NextStatus, State);
loop(initializing, #state{scc = SCC, servers = Servers} = State) ->
  DependsOn = dialyzer_succ_typings:find_depends_on(SCC, Servers),
  WithoutSelf = DependsOn -- [SCC],
  ?debug("Deps ~p: ~p\n",[State#state.scc, WithoutSelf]),
  loop(updating, State#state{depends_on = WithoutSelf});
loop(waiting, State) ->
  ?debug("Wait: ~p\n",[State#state.scc]),
  NewState = wait_for_success_typings(State),
  loop(updating, NewState);
loop(getting_data, State) ->
  ?debug("Data: ~p\n",[State#state.scc]),
  loop(updating, get_data(State));
loop(running, State) ->
  ?debug("Run: ~p\n",[State#state.scc]),
  ok = ask_coordinator_for_callers(State),
  NotFixpoint = do_work(State),
  Callers = get_callers_reply_from_coordinator(),
  ok = broadcast_done(State, Callers),
  report_to_coordinator(NotFixpoint, State).

waits_more_success_typings(#state{depends_on = Depends}) ->
  case Depends of
    [] -> false;
    [_] -> imminent;
    _ -> true
  end.

has_data(#state{scc_data = Data}) ->
  case Data of
    undefined -> false;
    _ -> true
  end.

get_data(#state{mode = Mode, scc = SCC, servers = Servers} = State) ->
  Data =
    case Mode of
      typesig -> dialyzer_succ_typings:collect_scc_data(SCC, Servers);
      dataflow -> dialyzer_succ_typings:collect_refine_scc_data(SCC, Servers)
    end,
  State#state{scc_data = Data}.

ask_coordinator_for_callers(#state{scc = SCC,
				   servers = Servers,
				   coordinator = Coordinator}) ->
  RequiredBy = dialyzer_succ_typings:find_required_by(SCC, Servers),
  WithoutSelf = RequiredBy -- [SCC],
  ?debug("Waiting for me~p: ~p\n",[SCC, WithoutSelf]),
  dialyzer_coordinator:sccs_to_pids_request(WithoutSelf, Coordinator).

get_callers_reply_from_coordinator() ->
  dialyzer_coordinator:sccs_to_pids_reply().

broadcast_done(#state{scc = SCC}, Callers) ->
  ?debug("Sending ~p: ~p\n",[SCC, Callers]),
  SendSTFun = fun(PID) -> PID ! {done, SCC} end,
  lists:foreach(SendSTFun, Callers).

wait_for_success_typings(#state{depends_on = DependsOn} = State) ->
  receive
    {done, SCC} ->
      ?debug("GOT ~p: ~p\n",[State#state.scc, SCC]),
      State#state{depends_on = DependsOn -- [SCC]}
  after
    5000 ->
      ?debug("Still Waiting ~p: ~p\n",[State#state.scc, DependsOn]),
      State
  end.

do_work(#state{mode = Mode, scc_data = SCCData}) ->
  case Mode of
    typesig -> dialyzer_succ_typings:find_succ_types_for_scc(SCCData);
    dataflow -> dialyzer_succ_typings:refine_one_module(SCCData)
  end.

report_to_coordinator(NotFixpoint,
		      #state{scc = SCC, coordinator = Coordinator}) ->
  ?debug("Done: ~p\n",[SCC]),
  dialyzer_coordinator:scc_done(SCC, NotFixpoint, Coordinator).

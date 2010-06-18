-module(r9c_tests_SUITE).

-include_lib("test_server/include/test_server.hrl").

-export([all/0, groups/0, init_per_group/2, end_per_group/2,
         init_per_testcase/2, fin_per_testcase/2]).

-export([asn1/1, inets/1, mnesia/1]).

-define(default_timeout, ?t:minutes(6)).
-define(dialyzer_options, ?config(dialyzer_options, Config)).
-define(datadir, ?config(data_dir, Config)).
-define(privdir, ?config(priv_dir, Config)).

groups() -> [].

init_per_group(_GroupName, Config) -> Config.

end_per_group(_GroupName, Config) -> Config.

init_per_testcase(_Case, Config) ->
    ?line Dog = ?t:timetrap(?default_timeout),
    [{dialyzer_options, [{defines,[{vsn,42}]}]}, {watchdog, Dog} | Config].

fin_per_testcase(_Case, _Config) ->
    Dog = ?config(watchdog, _Config),
    ?t:timetrap_cancel(Dog),
    ok.

all() ->
    [asn1,inets,mnesia].

asn1(Config) when is_list(Config) ->
    ?line run(Config, {asn1, dir}),
    ok.

inets(Config) when is_list(Config) ->
    ?line run(Config, {inets, dir}),
    ok.

mnesia(Config) when is_list(Config) ->
    ?line run(Config, {mnesia, dir}),
    ok.

run(Config, TestCase) ->
    case run_test(Config, TestCase) of
        ok -> ok;
        {fail, Reason} ->
            ?t:format("~s",[Reason]),
            fail()
    end.

run_test(Config, {TestCase, Kind}) ->
    Dog = ?config(watchdog, Config),
    Options = ?dialyzer_options,
    Dir = ?datadir,
    OutDir = ?privdir,
    case dialyzer_test:dialyzer_test(Options, TestCase, Kind,
                                     Dir, OutDir, Dog) of
        same -> ok;
        {differ, DiffList} ->
            {fail,
               io_lib:format("\nTest ~p failed:\n~p\n",
                            [TestCase, DiffList])}
    end.

fail() ->
    io:format("failed\n"),
    ?t:fail().

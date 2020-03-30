-module(bert_java).
-include("bert.hrl").
-export([parse_transform/2]).

parse_transform(Forms, Options) ->
    Dest = proplist:get_value(bert_java, Options, ?JAVA),
    File = filename:join([Dest, "java.java"]),
    io:format("Generated Java: ~p~n", [File]),
    Forms.

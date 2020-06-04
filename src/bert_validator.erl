-module(bert_validator).
-include("bert.hrl").
-author('Dmytro Boiko').
-export([parse_transform/2]).
-compile(export_all).

-define(Valid_Start,
  "\n    ErrFields = lists:flatten("
  "\n                [case {RecField, F} of\n                     ").
-define(Valid_End(Name),
  "\n                     _ -> RecField"
  "\n                 end || {RecField, F} <- lists:zip(record_info(fields, '"++Name++"'), tl(tuple_to_list(D)))]),").
-define(Valid_fun,
  "\n    case validate(lists:zip3(CondFuns, FieldNames, Fields), [{ErrFields, D} | Acc]) of"
  "\n        ok -> validate(lists:zip(FieldNames, Fields), [{ErrFields, D} | Acc]);"
  "\n        Err -> Err"
  "\n    end;").
-define(Valid_fun_empty,
  "\n    CondFuns = [],"
  "\n    Fields = [],"
  "\n    FieldNames = [],"
  "\n    case validate(lists:zip3(CondFuns, FieldNames, Fields), [{ErrFields, D} | Acc]) of"
  "\n        ok -> validate(lists:zip(FieldNames, Fields), [{ErrFields, D} | Acc]);"
  "\n        Err -> Err"
  "\n    end;").

to_upper(Name) ->
  [Hd | Tail] = Name,
  [string:to_upper(Hd)] ++ Tail.

to_lower(Name) ->
  [Hd | Tail] = Name,
  [string:to_lower(Hd)] ++ Tail.


%% Insane, creating an Erlang file as side effect
parse_transform(Forms, Options) ->
    AF = erl_syntax_lib:analyze_forms(Forms),
    Module = proplists:get_value(module, AF),
    CompileOpts =
        lists:foldl(fun({compile, Opts}, Acc) when is_list(Opts) -> Acc ++ Opts;
                       ({compile, Opt}, Acc) -> Acc ++ [Opt];
                       (_, Acc) -> Acc
                    end, Options, proplists:get_value(attributes, AF, [])),
    Dest = proplists:get_value(bert_erl, CompileOpts, ?ERL),

    Context = #{dest_dir => filename:join(Dest, Module),
                module => Module,
                imports => [],
                disallowed => proplists:get_value(bert_disallowed, Options, [])},

    %% file:delete("temp.txt"),
    Bin = directives(Forms, Context),
    File = filename:join(Dest, lists:concat([Module, "_validator",".erl"])),
    filelib:ensure_dir(File),
    io:format("Generated Models Validator: ~p~n", [File]),
    file:write_file(File, Bin),
    Forms.

directives(Forms, Context) ->
    %% NewForms = lists:foldl(fun(F, Acc) ->
    %%                           Acc ++ [form(F, Context)]
    %%                        end, [], Forms),
    R = lists:flatten([form(F, Context) || F <- Forms]),
    iolist_to_binary([prelude(Context),
                      lists:sublist(R, 1, length(R) - 1) ++ "."]).

form({attribute,_, record, {Name, T}}, _Context) -> [validate(Name, T)];
form(_Form, _) -> []. %% [Form].

validate(List, T) ->
  Class = lists:concat([List]),
  Fields = [case Data of
              {_,{_,_,{atom,_,Field},_Value},{type,_,Name,Args}} -> {lists:concat([Field]),{Name,Args}};
              {_,{_,_,{atom,_,Field}},{type,_,Name,Args}}        -> {lists:concat([Field]),{Name,Args}};
              {_,{_,_,{atom,_,Field},{_,_,_Value}},Args}         -> {lists:concat([Field]),Args};
              _                                                  -> []
            end || Data <- T],
    case valid(Fields, Class, []) of
        {[_ | _] = _Model, [_ | _] = When, [_ | _] = Validation} ->
            D = lists:flatten([Item || Item <- Validation, is_tuple(Item)]),
            V0 = "\n    CondFuns = ["   ++ string:join(["?COND_FUN(is_record(Rec, '"++ atom_to_list(C) ++ "'))" || {_,C} <- D], ", ") ++ "],",
            V  = "\n    Fields = [" ++ string:join([begin
                                                      Name = case F of {I,_} -> I; I -> I end,
                                                      "D#'" ++ Class ++ "'." ++ to_lower(Name)
                                                    end || F <- D, F /= []], ", ") ++ "],",
            V1 = "\n    FieldNames = [" ++ string:join([case F of {I,_} -> to_lower(I); I -> to_lower(I) end || F <- D, F /= []], ", ") ++ "],",
            "\nvalidate(D = #'" ++ Class ++ "'{}, Acc) ->" ++ ?Valid_Start ++ When ++ ?Valid_End(Class) ++ V0 ++ V ++ V1 ++ ?Valid_fun;
        {[_ | _] = _Model, [], [_ | _] = Validation} ->
            V = "\nvalidate([" ++ string:join([Item || Item <- Validation, Item /= []], ", ") ++ "])",
            "\nvalidate(D = #'" ++ Class ++ "'{}, Acc) ->" ++ V ++ ";";
        {[_ | _] = _Model, [], []} ->
            "\nvalidate(_D = #'" ++ Class ++ "'{}, _Acc) -> ok;";
        {[_ | _] = _Model, [_ | _] = When, []} ->
            "\nvalidate(D = #'" ++ Class ++ "'{}, Acc) ->" ++ ?Valid_Start ++ When ++ ?Valid_End(Class) ++ ?Valid_fun_empty;
        _ -> ""
    end.

valid([],_Class, Acc) ->
  {Model, Data} = lists:unzip(Acc),
  {When, Validation} = lists:unzip(Data),
  {string:join([Item || Item <- Model, Item /= []], ", "), string:join([Item || Item <- When, Item /= []], " -> [];\n                     ") ++ " -> [];", [Item || Item <- Validation, Item /= []]};
valid([Field | Rest], Class, Acc) ->
  case Field of
    {Name, Type} ->
      case Res = get_data(Type,Class, Name) of
        [] -> valid(Rest,Class, Acc);
        _ -> valid(Rest,Class, Acc ++ [Res])
      end;
    _ -> []
  end.

get_data(Type, Class, Name) ->
    {get_fields(Name, Type), get_type(Type, to_upper(Name), Class)}.

get_type({integer,_},Name,_)                                -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_integer("++Name++")",[]};
get_type({list,[{type,_,record,[{atom,_,C}]}]},Name,_)      -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_list("++Name++")",{Name,C}};
get_type({list,[{type,_,union, R}]},Name,_) when is_list(R) -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_list("++Name++")",Name};%split(R,Name,{[],[]});
get_type({list,_},Name,_)                                   -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_list("++Name++")",[]};
get_type({record,[{atom,_,Record}]},Name,_Class)            -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_record("++Name++",'"++atom_to_list(Record)++"')",[]};
get_type({term,[]},Name,_)                                  -> {"{"++to_lower(Name)++",_}",[]};
get_type({union,R},Name,Class) when is_list(R)              -> split(R,Name,Class,{[],[]});
get_type({tuple,_},Name,_)                                  -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_tuple("++Name++")",[]};
get_type({atom,_},Name,_)                                   -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_atom("++Name++")",[]};
get_type({binary,_},Name,_)                                 -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_binary("++Name++")",[]};
get_type(atom,Name,_)                                       -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_atom("++Name++")",[]};
get_type(integer,Name,_)                                    -> {"{" ++to_lower(Name) ++ ", " ++ Name ++ "} when is_integer("++Name++")",[]};
get_type(Type,Name,_)                                       -> get_records(Type,Name).

split([],Name,_,Acc) ->
  case Acc of
    {[],[]} -> {[],[]};
    {C, []} -> {[],"(" ++ string:join(["is_record("++Name++",'"++lists:concat([Item])++"')"||Item<-C,Item/=[]]," orelse ")++")"};
    {[], T} -> {"{"++to_lower(Name) ++ ", " ++ Name ++ "} when (" ++ string:join([Item||Item<-T,Item/=[]]," orelse ") ++ ")",[]};
    {_,  T} -> {"{"++to_lower(Name) ++ ", " ++ Name ++ "} when (" ++ string:join([lists:concat([Item])||Item<-T,Item/=[]]," orelse ")++")",Name}
  end;
split([Head | Tail], Name,C, Acc) ->
  Classes = element(1,Acc),
  Types = element(2,Acc),
  case get_records(Head, Name) of
    {[],   []}   -> split(Tail,Name,C,Acc);
    {Class,[]}   -> split(Tail,Name,C,{[Class|Classes],Types});
    {[],   Type} -> split(Tail,Name,C,{Classes,[Type|Types]});
    {Class,Type} -> split(Tail,Name,C,{[Class|Classes],[Type|Types]})end.

get_records({type,_,record,[{_,_,Class}]},Name) -> {atom_to_list(Class),"is_record("++Name++", '"++atom_to_list(Class)++"')"};
get_records({type,_,binary,_},Name)             -> {[],"is_binary("++Name++")"};
get_records({type,_,integer,_},Name)            -> {[],"is_integer("++Name++")"};
get_records({type,_,nil,_},Name)                -> {[],Name++" == []"};
get_records({type,_,tuple,_},Name)              -> {[],"is_tuple("++Name++")"};
get_records({type,_,list,_},Name)               -> {[],"is_list("++Name++")"};
get_records({type,_,atom,_},Name)               -> {[],"is_atom("++Name++")"};
get_records({atom,_,V},Name)                    -> {[],Name++" == '" ++ atom_to_list(V)++"'"};
get_records(_,_)                                -> {[],[]}.

get_fields(Name, Type) ->
  Res = case Type of
          binary -> "<<_/binary>>";
          _ -> to_upper(Name)
        end,
  lists:concat([Name, " = ", Res]).

prelude(#{imports := Imports, module := Module}) ->
  S = lists:flatten([io_lib:format("-include(\"~s\").~n",[X]) || X <- lists:usort(Imports)]),
  TimeStamp = calendar:system_time_to_rfc3339(erlang:system_time(second)),
  lists:concat([
                "-module(", Module, "_validator).\n"
                "%% Generate at ",  TimeStamp, "\n",
                S,
                "-compile(export_all).\n"
                "-define(COND_FUN(Cond), fun(Rec) when Cond -> true; (_) -> false end).\n"
                "validate(Obj) ->\n"
                "    case validate(Obj, []) of\n"
                "        ok -> [];\n"
                "        Err -> Err\n"
                "    end.\n\n"
                "validate(_, [{[_ | _] , _R} | _] = Acc) -> {error, Acc};\n"
                "validate([], _) -> ok;\n"
                "validate(Objs, [{[] , R} | T]) -> validate(Objs, [R|T]);\n"
                "validate([{CondFun, _, []} | T], Acc) when is_function(CondFun) -> validate(T, Acc);\n"
                "validate([{CondFun, Field, [Obj | TObjs]} | T], Acc) when is_function(CondFun) ->\n"
                "    case CondFun(Obj) of\n"
                "        true -> validate([{CondFun, Field, TObjs} | T], Acc);\n"
                "        false -> {error, [Field, Obj | Acc]} end;\n"
                "validate([{CondFun, Field, Obj} | T], Acc) when is_function(CondFun) ->\n"
                "    case CondFun(Obj) of true -> validate(T, Acc); false -> {error, [Field, Obj | Acc]} end;\n"
                "validate([{_Field, []} | T], Acc) -> validate(T, Acc);\n"
                "validate([{Field, [Obj | TObjs]} | T], Acc) ->\n"
                "    case validate(Obj, [Field | Acc]) of\n"
                "        ok -> validate([{Field, TObjs} | T], Acc);\n"
                "        Err -> Err\n"
                "    end;\n"]).

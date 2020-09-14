-module(bert_record_validator).
-include("bert.hrl").
%%  - Extend the source code with a validate/1 and validate/2 function.
%%  - Add a function that return all records that are validated with this program
-export([parse_transform/2]).
-include_lib("syntax_tools/include/merl.hrl").
-define(QUOTE(X), ?Q(??X)).
-compile(export_all).

to_upper(Name) when is_atom(Name) ->
    to_upper(atom_to_list(Name));
to_upper(Name) ->
    [Hd | Tail] = Name,
    [string:to_upper(Hd)] ++ Tail.

%% Add vlidation functions for header files included in source
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

    {Records, Validate} = directives(Forms, Context),
    File = filename:join(Dest, lists:concat([?MODULE, ".erl"])),
    filelib:ensure_dir(File),
    ExtraForms =
        erl_syntax:revert_forms(
          [?QUOTE(validate(Obj) ->
                         case invalid_fields(Obj, []) of
                             [] -> [];
                             Errors -> {error, Errors}
                         end.),
           ?QUOTE(validatable() -> _@Records@.),
           Validate]),
    NewForms = lists:keydelete(eof, 1, Forms) ++ [?QUOTE(-export([validate/1, validatable/0]).)] ++ ExtraForms,
    file:write_file(File, erl_prettypr:format(erl_syntax:form_list(NewForms))),
    io:format("Generated Models Validator: ~p~n", [File]),
    NewForms.

%% The validate/2 function returns a list of [{Fields, Obj}] for the fields that have the wrong type
%% in the record Obj. If a field itself contains a record, it decents and shows the fields that
%% are wrong in that record.
directives(Forms, Context) ->
     Clauses =
        [?QUOTE((_, [{[_ | _] , _R} | _] = Acc) -> Acc),
         ?QUOTE(([], _) -> []),
         ?QUOTE((Objs, [{[] , R} | T]) -> invalid_fields(Objs, [R|T])),
              %% all fields are of right type, now check objects
         ?QUOTE(([{_Field, []} | T], Acc) -> invalid_fields(T, Acc)),
         ?QUOTE(([{Field, [Obj | TObjs]} | T], Acc) ->
                       case invalid_fields(Obj, [Field | Acc]) of
                           [] -> invalid_fields([{Field, TObjs} | T], Acc);
                           Err -> Err
                       end)
        ],
    {Records, ExtraClauses} =
        lists:foldl(fun({attribute,_, record, {Name, T}}, {Recs, Cls} = A) ->
                            case fields(Name, T) of
                                [] ->
                                    A;
                                Fields ->
                                    {Recs ++ [Name], Cls ++ [validate(Name, Fields)]}
                            end;
                       (_, A)  ->
                            A
                    end, {[], []}, Forms),
    {Records, erl_syntax:function(erl_syntax:atom(invalid_fields), Clauses ++ ExtraClauses)}.

fields(RecordName, T) ->
    try
        [ case Data of
              {_,{_,_,{atom,_,Field},_Value},{type,_,Name,Args}} -> {Field,{Name,Args}};
              {_,{_,_,{atom,_,Field}},{type,_,Name,Args}}        -> {Field,{Name,Args}};
              {_,{_,_,{atom,_,Field},{_,_,_Value}},Args}         -> {Field,Args}
          end || Data <- T]
    catch _:Reason ->
            _Warning = io_lib:format("warning: no validator generated for ~p (~p)\n", [RecordName, Reason]),
            []
    end.

%% Generate zero or more clauses to handle the types
validate(List, Fields) ->
    Class = lists:concat([List]),
    case valid(Fields, Class) of
        {[], []} ->
            ?QUOTE((D, _Acc) when is_record(D, _@List@) -> ok);
        {Clauses, Validation} ->
            RecursiveValidate = [ begin
                                      Obj = erl_syntax:record_access(?QUOTE(D), ?QUOTE(_@List@), ?QUOTE(_@Field@)),
                                      ?QUOTE({ _@Field@, _@Obj })
                                  end || {Field, _} <- Validation ],
            Case = erl_syntax:case_expr(?QUOTE({RecField, F}), Clauses ++ [?QUOTE((_) -> RecField)]),
            ?QUOTE((D, Acc) when is_record(D, _@List@) ->
                          begin
                              ErrFields = lists:flatten(
                                            [ _@Case || {RecField, F} <-
                                                            lists:zip(record_info(fields, _@List@), tl(tuple_to_list(D)))]),
                              invalid_fields([_@@RecursiveValidate], [{ErrFields, D} | Acc])
                          end)
    end.

valid(Fields, Class) ->
    WV = [ get_type(Type, Name, erl_syntax:variable(to_upper(Name))) || {Name, Type} <- Fields],
    {When, Validation} = lists:unzip(WV),
    {When, [Item || Item <- Validation, Item /= []]}.


%%
get_type({atom,_}, Name, Var) ->
    get_type(atom, Name, Var);
get_type(atom, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_atom(_@Var) -> []),
    {Clause, []};
get_type({integer, _}, Name, Var) ->
    get_type(integer, Name, Var);
get_type(integer, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_integer(_@Var) -> []),
    {Clause, []};
get_type({non_neg_integer, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_integer(_@Var) andalso _@Var >= 0 -> []),
    {Clause, []};
get_type({pos_integer, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_integer(_@Var) andalso _@Var > 0 -> []),
    {Clause, []};
get_type({neg_integer, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_integer(_@Var) andalso _@Var < 0 -> []),
    {Clause, []};
get_type({boolean, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_boolean(_@Var) -> []),
    {Clause, []};
get_type({pid, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_pid(_@Var) -> []),
    {Clause, []};
get_type({node, _}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_atom(_@Var) -> []),
    {Clause, []};
get_type({list,[{type,_,record,[{atom,_,C}]}]}, Name, Var) ->
    RecVar = erl_syntax:variable(lists:concat([ erl_syntax:variable_literal(Var), "_", C ])),
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_list(_@Var) ->
                           [ {_@Name@, _@RecVar} || _@RecVar <- _@Var, not is_record(_@RecVar, _@C@)]),
    %% io:format("Clause Rec = ~s\n", [erl_prettypr:format(Clause)]),
    {Clause, {Name, C}};  %% These are handled later
get_type({list,[{type,_,union, Union}]}, Name, Var) when is_list(Union) ->
    UVar = erl_syntax:variable(lists:concat([ erl_syntax:variable_literal(Var), "Element"])),
    Clause =
        case orelse_it([ type_validate(E, UVar) || E <- Union ]) of
            [] ->
                ?QUOTE(({_@Name@, _@Var}) when is_list(_@Var) -> []);
            Guard ->
                ?QUOTE(({_@Name@, _@Var}) when is_list(_@Var) ->
                                       [ {_@Name@, _@UVar} || _@UVar <- _@Var, not (_@Guard) ])
        end,
    %% io:format("Clause Union = ~s\n", [erl_prettypr:format(Clause)]),
    {Clause, []};
get_type({list,_}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_list(_@Var) -> []),
    {Clause, []};
get_type({record,[{atom,_,Record}]}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_record(_@Var, _@Record@) -> []),
    {Clause, []};
get_type({term, []}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _}) -> []),
    {Clause, []};
get_type({tuple,_}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_tuple(_@Var) -> []),
    {Clause, []};
get_type({binary,_}, Name, Var) ->
    Clause = ?QUOTE(({_@Name@, _@Var}) when is_binary(_@Var) -> []),
    {Clause, []};
get_type({union, Union}, Name, Var) when is_list(Union) ->
    Clause =
        case orelse_it([ type_validate(E, Var) || E <- Union ]) of
            [] ->
                ?QUOTE(({_@Name@, _}) -> []);
            Guard ->
                erl_syntax:clause([?QUOTE({_@Name@, _@Var})], Guard, [?QUOTE([])])
        end,
    {Clause, []};
get_type(_Type, _Name, _Var) ->
    %% Extend program when this would happen
    %% Type not yet implemented
    {[], []}.


type_validate({type,_,record,[{_,_,Class}]}, Var) -> ?QUOTE(is_record(_@Var, _@Class@));
type_validate({type,_,binary,_}, Var)             -> ?QUOTE(is_binary(_@Var));
type_validate({type,_,integer,_}, Var)            -> ?QUOTE(is_integer(_@Var));
type_validate({type,_,nil,_}, Var)                -> ?QUOTE(_@Var == []);
type_validate({type,_,tuple,_}, Var)              -> ?QUOTE(is_tuple(_@Var));
type_validate({type,_,list,_}, Var)               -> ?QUOTE(is_list(_@Var));
type_validate({type,_,atom,_}, Var)               -> ?QUOTE(is_atom(_@Var));
type_validate({atom,_,V}, Var)                    -> ?QUOTE(_@Var == _@V@);
type_validate({integer,_,V}, Var)                 -> ?QUOTE(_@Var == _@V@);
type_validate(_Type, _)                            ->
    %% Could be extended
    undefined.

%% If the type check is undefined, we assume it is of right type (no guard)
orelse_it(Guards) ->
    case lists:member(undefined, Guards) orelse Guards == [] of
        true -> [];
        false ->
            lists:foldl(fun(Term, Acc) ->
                                ?QUOTE(_@Acc orelse _@Term)
                        end, hd(Guards), tl(Guards))
    end.

-module(spec_proc).
-compile(export_all).

-include("user.hrl").
-include("spec.hrl").

get_spec_type(Module_name, Fun_name, Arity) ->
	Mod = ?Query:exec(?Mod:find(Module_name)),
	Spec = ?Query:exec(Mod, ?Spec:find(Fun_name, Arity)),

    case Spec of 
        [] -> [];
        _  ->   Form = ?Query:exec(Spec, [{specdef, back}]),
                [_, Tattr2] = ?Query:exec(Form, [tattr]),

                case ?Typexp:type(Tattr2) of
                    fun_sig    -> process_funsig(Tattr2);
                    spec_guard -> Type_vars = process_spec_guard(Tattr2)
                end
    end.


find_first_match([], _) -> [];
find_first_match([{Var_name1, Type1} | Xs], Var_name2) ->
	case Var_name1 == Var_name2 of
		true  -> {Var_name1, Type1};
		false -> find_first_match(Xs, Var_name2)
	end.

replace_noneguard_vars([], _) -> [];
replace_noneguard_vars([{variable, [Type]} | Vars], Guard_vars) -> 
	Replaced_var = replace_type_var({variable, [Type]}, Guard_vars, []),
	[{Type, Replaced_var} | replace_noneguard_vars(Vars, Guard_vars)];
replace_noneguard_vars([{Type, Values} | Vars], Guard_vars) -> 
	Replaced_var = replace_type_var({Type, Values}, Guard_vars, []),
	[Replaced_var | replace_noneguard_vars(Vars, Guard_vars)];
replace_noneguard_vars([Var | Vars], Guard_vars) ->
	[Var | replace_noneguard_vars(Vars, Guard_vars)].

replace_type_vars([], All_vars) ->
	All_vars;
replace_type_vars([{Var_name, Type} | Vars_to_replace], [Var | All_vars]) ->
	New_value = replace_type_var(Type, [Var | All_vars], Var_name),

	if 
		Type == New_value -> replace_type_vars(Vars_to_replace, lists:append(All_vars, [{Var_name, New_value}]));
		true              -> replace_type_vars([{Var_name, New_value} | Vars_to_replace], [{Var_name, New_value} | All_vars])
	end.

replace_type_var({variable, [Value]}, All_vars, Value) ->
	{variable, [Value]};
replace_type_var({variable, [Value]}, All_vars, _Replaced_var) ->
	{Var, Type} = find_first_match(All_vars, Value),
	Type;
replace_type_var({func, [Args, Ret_val]}, All_vars, Replaced_var) ->
	{func, [replace_values(Args, All_vars, Replaced_var), replace_values(Ret_val, All_vars, Replaced_var)]};
replace_type_var({Type, Value}, All_vars, Replaced_var) when is_list(Value) ->
	{Type, replace_values(Value, All_vars, Replaced_var)};
replace_type_var(Var, All_vars, _Replaced_var) ->
	Var.

replace_values([], _, _) ->
	[];
replace_values([{Type, Value} | Values], All_vars, Replaced_var) ->
	[replace_type_var({Type, Value}, All_vars, Replaced_var) | replace_values(Values, All_vars, Replaced_var)];
replace_values([Value | Values], All_vars, Replaced_var) ->
	[Value | replace_values(Values, All_vars, Replaced_var)]. 

process_spec_guard(Tattr) ->
	[Funsig, Guard] = ?Query:exec(Tattr, ?Typexp:children()),
	Guard_children = 
		case ?Typexp:type(Guard) of
			guardlist  -> ?Query:exec(Guard, ?Typexp:children());
			vardef -> [Guard]
		end,
	Guard_types = get_args_type(Guard_children),
	Guard_replaced_type = replace_type_vars(Guard_types, Guard_types),
	{Args, Ret_type} = process_funsig(Funsig),
	{Replaced_args, Replaced_return_val} = {replace_noneguard_vars(Args, Guard_replaced_type), replace_noneguard_vars(Ret_type, Guard_replaced_type)},
	Args_type = lists:map(fun({Var_name, Type}) -> Type end, Replaced_args),
	Return_type = lists:map(fun({Var_name, Type}) -> Type end, Replaced_return_val),
	{Args_type, Return_type},
	{Replaced_args, Replaced_return_val}.%Only for testing purposes

process_funsig(Funsig_expr) ->
	[Arglist, Return] = ?Query:exec(Funsig_expr, ?Typexp:children()),
	Args = ?Query:exec(Arglist, ?Typexp:children()),
	{get_args_type(Args), get_args_type([Return])}.
	
get_args_type([]) ->
	[];
get_args_type([Arg | Args]) ->
	[get_spec_elem_type(Arg) | get_args_type(Args)].

get_vardef_inf(Arg) ->
	[Name, Type] = ?Query:exec(Arg, ?Typexp:children()),
	{?Typexp:tag(Name), get_spec_elem_type(Type)}.

get_spec_elem_type(Elem) ->
	case ?Typexp:type(Elem) of
		union    -> get_union_type(Elem);
		func     -> get_anonfunc_type(Elem);
		list     -> get_list_type(Elem);
		tuple    -> get_tuple_type(Elem);
		vardef   -> get_vardef_inf(Elem);
		variable -> get_var_type(Elem);
		call     -> get_call_type(Elem);
		paren    -> get_paren_type(Elem);
		_        -> get_simple_type(Elem)
	end.

get_anonfunc_type(Elem) ->
	[Fun_sig] = ?Query:exec(Elem, ?Typexp:children()),
	{Args, Ret_type} = process_funsig(Fun_sig),
	{func, [drop_var_names(Args), drop_var_names(Ret_type)]}.

drop_var_name({Var_name, {Type, Value}}) ->
	{Type, Value};
drop_var_name(Var) ->
	Var.

drop_var_names([]) -> [];
drop_var_names([Var | Vars]) ->
	[drop_var_name(Var) | drop_var_names(Vars)].

get_call_type(Call) ->
	[Type, Arg_list] = ?Query:exec(Call, ?Typexp:children()),
	Children = ?Query:exec(Arg_list, ?Typexp:children()),
	{?Typexp:tag(Type), get_args_type(Children)}.
	

get_list_type(List) ->
	case ?Typexp:tag(List) of
		empty        -> {list, []};
		any          -> Children = ?Query:exec(List, ?Typexp:children()),
				 		{list, get_args_type(Children)};
		nonempty     -> Children = ?Query:exec(List, ?Typexp:children()),
				 		{list, get_args_type(Children) ++ ['...']}
	end.
		
get_tuple_type(Arg) ->
	Children = ?Query:exec(Arg, ?Typexp:children()),
	{tuple, get_args_type(Children)}.

get_paren_type(Arg) ->
	Children = ?Query:exec(Arg, ?Typexp:children()),
	{paren, get_args_type(Children)}.

get_simple_type(Elem) ->
    Tag = ?Typexp:tag(Elem),
    [Elem_parent] = ?Typexp:parent(Elem),

    case ?Typexp:type(Elem_parent) of
        call ->  case Tag of
                    atom    -> atom;
                    integer -> integer;
                    float   -> float;
                    boolean -> boolean;
                    term    -> term;
                    number  -> number
                end;
        _   -> get_literal_type(Elem)
    end.

get_literal_type(Elem) ->
	case ?Typexp:type(Elem) of
		negate -> [Child] = ?Query:exec(Elem, ?Typexp:children()),
			      {Type, Value} = get_spec_elem_type(Child),
			      {Type, -Value};
		_      -> {?Typexp:type(Elem), ?Typexp:tag(Elem)}
	end.

get_union_type(Arg) ->
	Children = ?Query:exec(Arg, ?Typexp:children()),
	Union_type = get_args_type(Children),
	{union, Union_type}.

get_var_type(Var) -> 
	{variable, [?Typexp:tag(Var)]}.









%----------------For testing purposes--------------------------------------------------
get_all_specs(Module_name) ->
    Mod = ?Query:exec(?Mod:find(Module_name)),
    ?Query:exec(Mod, ?Mod:specs()).

test(Module_name) ->
    All_specs = get_all_specs(Module_name),
    get_funcs_sig(All_specs).

get_funcs_sig([]) -> " ";
get_funcs_sig([Spec | Specs]) ->
    Name = ?Spec:name(Spec),
    erlang:display(Name),
    erlang:display(" "),
    Arity = ?Spec:arity(Spec),
    [Mod] = ?Query:exec(Spec, ?Spec:module()),
    Mod_name = ?Mod:name(Mod),
    Res = get_spec_type(Mod_name, Name, Arity),
    erlang:display(Res),
    erlang:display("-----------------------------------"),
    get_funcs_sig(Specs).

test2() ->
    All_specs = get_all_specs(lists),
    Test_cases = f(),
    get_funcs_sig2(All_specs, Test_cases).

get_funcs_sig2([], _) -> " ";
get_funcs_sig2([Spec | Specs], [T | Ts]) ->
    Name = ?Spec:name(Spec),
    Arity = ?Spec:arity(Spec),
    [Mod] = ?Query:exec(Spec, ?Spec:module()),
    Mod_name = ?Mod:name(Mod),
    Res = get_spec_type(Mod_name, Name, Arity),
    erlang:display(Res == T),
    get_funcs_sig2(Specs, Ts).

%gfdsf

f() ->
    [
        %keyfind
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList",{list,[{tuple,[]}]}}],[{union,[{tuple,[]},{atom,false}]}]},
        %keymember
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList",{list,[{tuple,[]}]}}],[{boolean,[]}]},
        %keysearch
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList",{list,[{tuple,[]}]}}],[{union,[{tuple,[{atom,value},{tuple,[]}]},{atom,false}]}]},
        %member
        {[{"Elem",{term,[]}},{"List",{list,[{term,[]}]}}],[{boolean,[]}]},
        %reverse
        {[{"List1",{list,[{term,[]}]}},{"Tail",{term,[]}}],[{"List2",{list,[{term,[]}]}}]},
        %append
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{term,[]}]}}]},
        %append
        {[{"ListOfLists",{list,[{list,[{term,[]}]}]}}],[{"List1",{list,[{term,[]}]}}]},
        %subtract
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{term,[]}]}}]},
        %reverse
        {[{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %nth
        {[{"N",{pos_integer,[]}},{"List",{list,[{term,[]},'...']}}],[{"Elem",{term,[]}}]},
        %nthtail
        {[{"N",{non_neg_integer,[]}},{"List",{list,[{term,[]},'...']}}],[{"Tail",{list,[{term,[]}]}}]},
        %prefix
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{boolean,[]}]},
        %suffix
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{boolean,[]}]},
        %droplast
        {[{"List",{list,[{term,[]},'...']}}],[{"InitList",{list,[{term,[]}]}}]},
        %last
        {[{"List",{list,[{term,[]},'...']}}],[{"Last",{term,[]}}]},
        %seq
        {[{"From",{integer,[]}},{"To",{integer,[]}}],[{"Seq",{list,[{integer,[]}]}}]},
        %seq
        {[{"From",{integer,[]}},{"To",{integer,[]}},{"Incr",{integer,[]}}],[{"Seq",{list,[{integer,[]}]}}]},
        %sum
        {[{"List",{list,[{number,[]}]}}],[{number,[]}]},
        %duplicate
        {[{"N",{non_neg_integer,[]}},{"Elem",{term,[]}}],[{"List",{list,[{term,[]}]}}]},
        %min
        {[{"List",{list,[{term,[]},'...']}}],[{"Min",{term,[]}}]},
        %max
        {[{"List",{list,[{term,[]},'...']}}],[{"Max",{term,[]}}]},
        %sublist
        {[{"List1",{list,[{term,[]}]}},{"Start",{pos_integer,[]}},{"Len",{non_neg_integer,[]}}],[{"List2",{list,[{term,[]}]}}]},
        %sublist
        {[{"List1",{list,[{term,[]}]}},{"Len",{non_neg_integer,[]}}],[{"List2",{list,[{term,[]}]}}]},
        %delete
        {[{"Elem",{term,[]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %zip
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{tuple,[{term,[]},{term,[]}]}]}}]},
        %unzip
        {[{"List1",{list,[{tuple,[{term,[]},{term,[]}]}]}}],[{tuple,[{list,[{term,[]}]},{list,[{term,[]}]}]}]},
        %zip3
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}},{"List3",{list,[{term,[]}]}}],[{"List4",{list,[{tuple,[{term,[]},{term,[]},{term,[]}]}]}}]},
        %unzip3
        {[{"List1",{list,[{tuple,[{term,[]},{term,[]},{term,[]}]}]}}],[{tuple,[{list,[{term,[]}]},{list,[{term,[]}]},{list,[{term,[]}]}]}]},
        %zipwith
        {[{"Combine",{func,[[{term,[]},{term,[]}],[{term,[]}]]}},{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{term,[]}]}}]},
        %zipwith3
        {[{"Combine",{func,[[{term,[]},{term,[]},{term,[]}],[{term,[]}]]}},{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}},{"List3",{list,[{term,[]}]}}],[{"List4",{list,[{term,[]}]}}]},
        %sort
        {[{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %merge
        {[{"ListOfLists",{list,[{list,[{term,[]}]}]}}],[{"List1",{list,[{term,[]}]}}]},
        %merge3
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}},{"List3",{list,[{term,[]}]}}],[{"List4",{list,[{paren,[{union,[{term,[]},{term,[]},{term,[]}]}]}]}}]},
        %rmerge3
        {[{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]},{list,[{variable,["Z"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]},{variable,["Z"]}]}]}]}]},
        %merge
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{paren,[{union,[{term,[]},{term,[]}]}]}]}}]},
        %rmerge
        {[{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]}]}]}]}]},
        %concat
        {[{"Things",{list,[{union,[{atom,[]},{integer,[]},{float,[]},{string,[]}]}]}}],[{string,[]}]},
        %flatten
        {[{"DeepList",{list,[{union,[{term,[]},{variable,["DeepList"]}]}]}}],[{"List",{list,[{term,[]}]}}]},
        %flatten
        {[{"DeepList",{list,[{union,[{term,[]},{variable,["DeepList"]}]}]}},{"Tail",{list,[{term,[]}]}}],[{"List",{list,[{term,[]}]}}]},
        %flatlength
        {[{"DeepList",{list,[{union,[{term,[]},{variable,["DeepList"]}]}]}}],[{non_neg_integer,[]}]},
        %keydelete
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}}],[{"TupleList2",{list,[{tuple,[]}]}}]},
        %keyreplace
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}},{"NewTuple",{tuple,[]}}],[{"TupleList2",{list,[{tuple,[]}]}}]},
        %keytake
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}}],[{union,[{tuple,[{atom,value},{tuple,[]},{list,[{tuple,[]}]}]},{atom,false}]}]},
        %keystore
        {[{"Key",{term,[]}},{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}},{"NewTuple",{tuple,[]}}],[{"TupleList2",{list,[{tuple,[]},'...']}}]},
        %keysort
        {[{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}}],[{"TupleList2",{list,[{tuple,[]}]}}]},
        %keymerge
        {[{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}},{"TupleList2",{list,[{tuple,[]}]}}],[{"TupleList3",{list,[{paren,[{union,[{tuple,[]},{tuple,[]}]}]}]}}]},
        %rkeymerge
        {[{pos_integer,[]},{list,[{tuple,[]}]},{list,[{tuple,[]}]}],[{list,[{tuple,[]}]}]},
        %ukeysort
        {[{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}}],[{"TupleList2",{list,[{tuple,[]}]}}]},
        %ukeymerge
        {[{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}},{"TupleList2",{list,[{tuple,[]}]}}],[{"TupleList3",{list,[{paren,[{union,[{tuple,[]},{tuple,[]}]}]}]}}]},
        %rukeymerge
        {[{pos_integer,[]},{list,[{tuple,[]}]},{list,[{tuple,[]}]}],[{list,[{paren,[{union,[{tuple,[]},{tuple,[]}]}]}]}]},
        %keymap
        {[{"Fun",{func,[[{term,[]}],[{term,[]}]]}},{"N",{pos_integer,[]}},{"TupleList1",{list,[{tuple,[]}]}}],[{"TupleList2",{list,[{tuple,[]}]}}]},
        %sort
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %merge
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{paren,[{union,[{term,[]},{term,[]}]}]}]}}]},
        %rmerge
        {[{func,[[{variable,["X"]},{variable,["Y"]}],[{boolean,[]}]]},{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]}]}]}]}]},
        %usort
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %umerge
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{paren,[{union,[{term,[]},{term,[]}]}]}]}}]},
        %rumerge
        {[{func,[[{variable,["X"]},{variable,["Y"]}],[{boolean,[]}]]},{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]}]}]}]}]},
        %usort
        {[{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %umerge
        {[{"ListOfLists",{list,[{list,[{term,[]}]}]}}],[{"List1",{list,[{term,[]}]}}]},
        %umerge3
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}},{"List3",{list,[{term,[]}]}}],[{"List4",{list,[{paren,[{union,[{term,[]},{term,[]},{term,[]}]}]}]}}]},
        %rumerge3
        {[{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]},{list,[{variable,["Z"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]},{variable,["Z"]}]}]}]}]},
        %umerge
        {[{"List1",{list,[{term,[]}]}},{"List2",{list,[{term,[]}]}}],[{"List3",{list,[{paren,[{union,[{term,[]},{term,[]}]}]}]}}]},
        %rumerge
        {[{list,[{variable,["X"]}]},{list,[{variable,["Y"]}]}],[{list,[{paren,[{union,[{variable,["X"]},{variable,["Y"]}]}]}]}]},
        %all
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List",{list,[{term,[]}]}}],[{boolean,[]}]},
        %any
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List",{list,[{term,[]}]}}],[{boolean,[]}]},
        %map
        {[{"Fun",{func,[[{term,[]}],[{term,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %flatmap
        {[{"Fun",{func,[[{term,[]}],[{list,[{term,[]}]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %foldl
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{term,[]}]]}},{"Acc0",{term,[]}},{"List",{list,[{term,[]}]}}],[{"Acc1",{term,[]}}]},
        %foldr
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{term,[]}]]}},{"Acc0",{term,[]}},{"List",{list,[{term,[]}]}}],[{"Acc1",{term,[]}}]},
        %filter
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %partition
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List",{list,[{term,[]}]}}],[{tuple,[{list,[{term,[]}]},{list,[{term,[]}]}]}]},
        %filtermap
        {[{"Fun",{func,[[{term,[]}],[{union,[{boolean,[]},{tuple,[{atom,true},{term,[]}]}]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{union,[{term,[]},{term,[]}]}]}}]},
        %zf
        {[{func,[[{variable,["T"]}],[{union,[{boolean,[]},{tuple,[{atom,true},{variable,["X"]}]}]}]]},{list,[{variable,["T"]}]}],[{list,[{paren,[{union,[{variable,["T"]},{variable,["X"]}]}]}]}]},
        %foreach
        {[{"Fun",{func,[[{term,[]}],[{term,[]}]]}},{"List",{list,[{term,[]}]}}],[{atom,ok}]},
        %mapfoldl
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{tuple,[{term,[]},{term,[]}]}]]}},{"Acc0",{term,[]}},{"List1",{list,[{term,[]}]}}],[{tuple,[{list,[{term,[]}]},{term,[]}]}]},
        %mapfoldr
        {[{"Fun",{func,[[{term,[]},{term,[]}],[{tuple,[{term,[]},{term,[]}]}]]}},{"Acc0",{term,[]}},{"List1",{list,[{term,[]}]}}],[{tuple,[{list,[{term,[]}]},{term,[]}]}]},
        %takewhile
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %dropwhile
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]},
        %splitwith
        {[{"Pred",{func,[[{term,[]}],[{boolean,[]}]]}},{"List",{list,[{term,[]}]}}],[{tuple,[{list,[{term,[]}]},{list,[{term,[]}]}]}]},
        %split
        {[{"N",{non_neg_integer,[]}},{"List1",{list,[{term,[]}]}}],[{tuple,[{list,[{term,[]}]},{list,[{term,[]}]}]}]},
        %join
        {[{"Sep",{term,[]}},{"List1",{list,[{term,[]}]}}],[{"List2",{list,[{term,[]}]}}]}
    ].



-module(refined_genspec).

%Если придётся переустанавливать refactorerl, в модуле reflib_spec, функции find нужно заменить type на spec, как сделано ниже.
%find(Name, Arity) ->
%    [{spec, {{name, '==', Name}, 'and', {arity, '==', Arity}}}].

%Сравнить результат тайпера и рузультат моего алгоритма. Отрбасывать все варианты тайпера, которые совсем не совпадают с результатом моего алгоритма. Например Если результат моего алгоритма выдаёт "integer | list", а тайпер "number | list | atom", то оставляем только "number | list". 

%------TODO list----------------
%1)Исправить листы в spec_proc модуле
%1)Process guard expressions(В разделе "Defining actual clauses")
%4)Функция get_fun_name не обрабатывает случай, когда можду именем функции и скобками есть пробелы.
%6)Добавить обработку случая, когда нет actual clauses для функции infer_internal_fun.
%7)Добавить обработку случая, для выражений типо [1,2 | B] = SomeList, а так же когда аргумент функции паттерматчат к дкакому-либо значению.
%8)Обрадотать случай, когда последнее выражение функции - funxepression.
%10)Добавить обрабокту случая вызова функция внутри листво и таплов
%11)Когда при присваивании на левой стороне стоит пременная с типом any а на правой переменная с каким-то более точным значением, присвоить переменной слева это значение
%13)Добавить стринг
%14)Добавить типы pos_integer, neg_integer, etc о время вычисления infix expressions и prefix expressions
%15)Добавить обработку данного случая 
%	f(A) when is_boolean(A) ->
%	[{A, true, da}, {error, false, net}].
%16)Сделать так, что если у функции есть спецификация - оставлять результат тайпера как есть.

-include("user.hrl").
-include("spec.hrl").

-compile(export_all).


%Pay attention that the index values and the order number of elements in the POSSIBLE_TYPES macros has to match.
-define(ANY_SEC_INDEX, 1).
-define(BOOLS_SEC_INDEX, 2).
-define(NUMS_SEC_INDEX, 3).
-define(ATOMS_SEC_INDEX, 4).
-define(LISTS_SEC_INDEX, 5).
-define(TUPLES_SEC_INDEX, 6).
%Pay attention that the IMPROPER_ELEMS_SEC_INDEX has to be always the last element of the POSSIBLE_TYPES macros.
-define(PIDS_SEC_INDEX, 7). 
-define(IMPROPER_ELEMS_SEC_INDEX, 8). 
-define(UNION_INDEX, 9).

-define(ELEMS_TBL, {
		{any, []}, {bools, []}, {nums, []}, {atoms, []}, {lists, []}, {tuples, []}, {pids, []} ,{improper_elems, []}
	}).

-define(LIST_TYPES, [
		empty_list, nonempty_list,  
		nonempty_improper_list, maybe_improper_list, 
		nonempty_maybe_improper_list, list
	]).


-define(BIFs, [
				is_atom, is_binary, is_bitstring, is_boolean,
				is_float ,is_function, is_integer, is_list, 
				is_map, is_number, is_pid, is_port,
				is_record, is_reference, is_tuple, tuple_to_list,
				spawn, self, exit, hd, tl
    ]).

infer_fun_type(Mod_name, Fun_name, Arity, []) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	Root = {{Mod_name, Fun_name, Arity}},
	Clauses_num = length(Clauses),
	Vars = lists:duplicate(Clauses_num, []),
 	[Ret_val_tp] = get_clauses_type(Clauses, Vars, {Root, []}, []),
 	Ret_val_tp.
	%Clauses_types = lists:map(fun(Clause) -> get_clause_type(Clause, Variables, {Root, []}) end, Clauses),

	%{Gen_clauses_tp, _} = generalize_elems(Clauses_types, []),
	%Gen_clauses_tp.
%	case length(Clauses_types) of
%		1 -> Clauses_types;
%		_ -> {union, Clauses_types}
%	end.


get_clause_type(Clause, Variables, Call_stack) ->
	Bodies = get_bodies(Clause),

	define_bodies_type(Bodies, Variables, Call_stack).


get_clauses_type([], [], _Call_stack, Res) -> 
	{Clauses_gen_tp, _} = generalize_elems(Res, []),
	%erlang:display(Clauses_gen_tp),
	[Clauses_gen_tp];
	%Res;
get_clauses_type([Clause | Clauses], [Clause_vars | All_vars], Call_stack, Res) ->
	{Clause_tp, _Upd_vars} = get_clause_type(Clause, Clause_vars, Call_stack),

	case Clause_tp of
		[] -> get_clauses_type(Clauses, All_vars, Call_stack, Res);
	    _  -> get_clauses_type(Clauses, All_vars, Call_stack, [Clause_tp | Res])
	end.


define_bodies_type([], Vars, _Call_stack) -> {[], Vars};
define_bodies_type([Last_body], Vars, Call_stack) ->
	{Clause_type, Upd_vars} = infer_expr_tp(Last_body, Vars, Call_stack),

	case Clause_type of
		{none, []} -> {[], Upd_vars};
		_          -> {Clause_type, Upd_vars}
	end;
define_bodies_type([Body | Bodies], Vars, Call_stack) ->
	{Body_type, Upd_vars} = infer_expr_tp(Body, Vars, Call_stack),

	case Body_type of
		{none, []} -> {[], Upd_vars};
		_          -> define_bodies_type(Bodies, Upd_vars, Call_stack)
	end.         
	

%---------------------------------Inference part-----------------------------------------------

infer_expr_tp(Expr, Vars, Call_stack) ->
	case ?Expr:type(Expr) of
		list_comp       -> {{list, [{any, []}]}, Vars};
		string          -> infer_string(Expr, Vars, Call_stack);
		send_expr       -> infer_send_expr(Expr, Vars, Call_stack);
		receive_expr    -> infer_receive_expr(Expr, Vars, Call_stack);
		if_expr         -> infer_if_expr(Expr, Vars, Call_stack);
		case_expr       -> infer_case_expr(Expr, Vars, Call_stack);
		prefix_expr     -> {infer_prefix_expr_type(Expr, ?Expr:value(Expr), Vars, Call_stack), Vars};
		match_expr      -> infer_match_expr_inf(Expr, Vars, Call_stack);
		infix_expr      -> {infer_infix_expr_type(Expr, ?Expr:value(Expr), Vars, Call_stack), Vars};
		variable        -> {infer_var_type(Expr, Vars), Vars};
		parenthesis     -> infer_parenthesis_inf(Expr, Vars, Call_stack);
		fun_expr        -> Fun_expr = {fun_expr, [Expr]},
		                   {Fun_expr, Vars};
		application     -> {infer_fun_app_type(Expr, Vars, Call_stack), Vars};
		cons            -> infer_cons_expr_type(Expr, Vars, Call_stack);
		tuple           -> infer_tuple_expr_type(Expr,Vars, Call_stack);
		implicit_fun    -> {infer_implicit_fun_expr(Expr, Vars), Vars};
		_Simple_type    -> {infer_simple_type(Expr), Vars}
	end.


infer_string(Expr, _Vars, _Call_stack) ->
	Str_val = ?Expr:value(Expr),
	Str_in_cf = convert_value_in_basic_format_to_compound(Str_val),
	{generalize_term(Str_in_cf, []), []}.


infer_send_expr(Expr, Vars, Call_stack) ->
	[_Pid, Msg] = ?Query:exec(Expr, ?Expr:children()),
	infer_expr_tp(Msg, Vars, Call_stack).


infer_receive_expr(Receive_expr, Vars, Call_stack) ->
	After_clause_in_lst = ?Query:exec(Receive_expr, [aftercl]),
	Clauses = ?Query:exec(Receive_expr, [exprcl]),

	case After_clause_in_lst of
		[]             -> infer_receive_clauses(Clauses, Vars, Call_stack, [], []);
		[After_clause] -> infer_receive_clauses([After_clause | Clauses], Vars, Call_stack, [], [])
	end.


infer_receive_clauses([], Vars, _Call_stack, Clauses_tp, Clauses_vars) ->
	Upd_vars = Vars ++ Clauses_vars, 
	Case_clause_tp = 
		case length(Clauses_tp) of
			0 -> {none, []};
			1 -> hd(Clauses_tp);
			_ -> {union, Clauses_tp}
		end,
	{Case_clause_tp, Upd_vars};
infer_receive_clauses([Clause_expr | Clause_exprs], Vars, Call_stack, Clauses_tp, Clauses_vars) ->
	{Clause_tp, Upd_vars} = get_clause_type(Clause_expr, Vars, Call_stack),
	Clause_vars = Upd_vars -- Vars,
	Upd_clauses_vars = unite_case_clauses_vars(Clause_vars, Clauses_vars),
	infer_receive_clauses(Clause_exprs, Vars, Call_stack, [Clause_tp | Clauses_tp], Upd_clauses_vars).


infer_if_expr(If_expr, Vars, Call_stack) ->
	Clause_exprs = ?Query:exec(If_expr, [exprcl]),
	infer_if_clauses(Clause_exprs, Vars, Call_stack, [], []).


infer_if_clauses([], Vars, _Call_stack, Clauses_tp, Clauses_vars) ->
	Upd_vars = Vars ++ Clauses_vars, 
	Case_clause_tp = 
		case length(Clauses_tp) of
			0 -> {none, []};
			1 -> hd(Clauses_tp);
			_ -> {union, Clauses_tp}
		end,

	{Case_clause_tp, Upd_vars};
infer_if_clauses([Clause_expr | Clause_exprs], Vars, Call_stack, Clauses_tp, Clauses_vars) ->
	[Guard] = ?Query:exec(Clause_expr, ?Clause:guard()),

	case filter_clause_by_guards(Guard, Vars) of
		true     -> {Clause_tp, Upd_vars} = get_clause_type(Clause_expr, Vars, Call_stack),
		            Clause_vars = Upd_vars -- Vars,
		            Upd_clauses_vars  = unite_case_clauses_vars(Clause_vars, Clauses_vars),
		            infer_if_clauses([], Vars, Call_stack, [Clause_tp | Clauses_tp], Upd_clauses_vars);
		possibly -> {Clause_tp, Upd_vars} = get_clause_type(Clause_expr, Vars, Call_stack),
		            Clause_vars = Upd_vars -- Vars,
		            Upd_clauses_vars  = unite_case_clauses_vars(Clause_vars, Clauses_vars),
		            infer_if_clauses(Clause_exprs, Vars, Call_stack, [Clause_tp | Clauses_tp], Upd_clauses_vars);	
		false    -> infer_if_clauses(Clause_exprs, Vars, Call_stack, Clauses_tp, Clauses_vars)	
	end.


infer_case_expr(Case_expr, Vars, Call_stack) ->
	Head_expr = ?Query:exec(Case_expr, [headcl]),
	Clauses_exprs = ?Query:exec(Case_expr, [exprcl]),
	{Head_tp, Upd_vars} = get_clause_type(Head_expr, Vars, Call_stack),
	{Clauses_tp, Upd_vars2} = infer_case_clauses(Clauses_exprs, Head_tp, Upd_vars, Call_stack, [], []),
	{Clauses_tp, Upd_vars2}.


infer_case_clauses([], _Head_tp, Vars, _Call_stack, Clauses_tp, Clauses_vars) ->
	Upd_vars = Vars ++ Clauses_vars, 
	Case_clause_tp = 
		case length(Clauses_tp) of
			0 -> {none, []};
			1 -> hd(Clauses_tp);
			_ -> {union, Clauses_tp}
		end,

	{Case_clause_tp, Upd_vars};
infer_case_clauses([Clause_expr | Clause_exprs], Head_tp, Vars, Call_stack, Clauses_tp, Clauses_vars) ->
	Clause_pat_expr = get_patterns(Clause_expr),

	Guard =
	    case ?Query:exec(Clause_expr, ?Clause:guard()) of
	    	[]      -> [[]];
	    	Guard_expr -> Guard_expr
	    end,

	Clause = filter_clauses([Clause_pat_expr], [Head_tp], Guard),

	case Clause of
		[]                        -> infer_case_clauses(Clause_exprs, Head_tp, Vars, Call_stack, Clauses_tp, Clauses_vars);
		[{Clause_expr, Upd_vars}] -> {Clause_tp, Upd_vars2} = get_clause_type(Clause_expr, Upd_vars, Call_stack),

		                             {Clause_pat_expr_tp, _} = infer_expr_tp(hd(Clause_pat_expr), Upd_vars, Call_stack),
		                             Are_matching_types = are_matching_types(Clause_pat_expr_tp, Head_tp),

		                             case {Are_matching_types, Clause_tp} of
		                             	  {_, []}       -> infer_case_clauses(Clause_exprs, Head_tp, Vars, Call_stack, Clauses_tp, Clauses_vars);
		                                  {true, _}     -> Clause_var = Upd_vars2 -- Vars,
		                                                   Upd_clauses_vars = unite_case_clauses_vars(Clause_var, Clauses_vars),
		                                                   infer_case_clauses([], Head_tp, Vars, Call_stack, [Clause_tp | Clauses_tp], Upd_clauses_vars);
                                          {possibly, _} -> Clause_var = Upd_vars2 -- Vars,
		                                                   Upd_clauses_vars = unite_case_clauses_vars(Clause_var, Clauses_vars),
		                                                   infer_case_clauses(Clause_exprs, Head_tp, Vars, Call_stack, [Clause_tp | Clauses_tp], Upd_clauses_vars)
		                             end
    end.


unite_case_clauses_vars([], Clauses_vars) ->
	Clauses_vars;
unite_case_clauses_vars([Var | Vars], Clauses_vars) ->
	Upd_clauses_vars = unite_case_clauses_var(Var, Clauses_vars),
	unite_case_clauses_vars(Vars, Upd_clauses_vars).


unite_case_clauses_var(Clause_var = {Var_name, [Val]}, Clauses_vars) ->
	case lists:keyfind(Var_name, 1, Clauses_vars) of
		false                          -> [Clause_var | Clauses_vars];
		{Var_name, [{union, [Elems]}]} -> Upd_var = {Var_name, [Val | Elems]},
                                          lists:keyreplace(Var_name, 1, Clauses_vars, Upd_var);                                   
		{Var_name, [Matched_var_val]}  -> Upd_var = {Var_name, [{union, [Val, Matched_var_val]}]},
                                          lists:keyreplace(Var_name, 1, Clauses_vars, Upd_var)
	end. 


infer_implicit_fun_expr(Implicit_fun_expr, _Vars) ->
	[Fun_info_expr, Arity_expr] = ?Query:exec(Implicit_fun_expr, ?Expr:children()),

	case ?Expr:value(Fun_info_expr) of
		':' -> 	[Mod_name_expr, Fun_name_expr] = ?Query:exec(Fun_info_expr, ?Expr:children()),
				{implicit_fun, [{external_mod, ?Expr:value(Mod_name_expr)}, ?Expr:value(Fun_name_expr), ?Expr:value(Arity_expr)]};
		_   ->  Function = ?Query:exec(Implicit_fun_expr, ?Expr:function()),
				[Fun_mod] = ?Query:exec(Function, ?Fun:module()),
				{implicit_fun, [{current_mod, ?Mod:name(Fun_mod)}, ?Expr:value(Fun_info_expr), ?Expr:value(Arity_expr)]}
	end.


infer_var_type(Var_expr, Vars) ->
	Var = find_var_by_name(?Expr:value(Var_expr), Vars),	

	case Var of 
		{variable, _Var_name}     -> {any, []};
		{_Var_name, [{Tp, Val}]} -> {Tp, Val}
	end.

infer_simple_type(Expr) ->
	Expr_val = ?Expr:value(Expr),
	
	case Expr_val of
		true  -> {boolean, [true]};
		false -> {boolean, [false]};
		_     -> {?Expr:type(Expr), [Expr_val]}
	end.


construct_and_convert_cons_to_cf(Cons_expr, Vars, Call_stack) ->
	{Lst, Upd_vars} = construct_list_from_cons_expr(Cons_expr, Vars, Call_stack),
	{convert_value_in_basic_format_to_compound(Lst), Upd_vars}.


infer_cons_expr_type(Cons_expr, Vars, Call_stack) ->
	{Lst_in_cf, Upd_vars} = construct_and_convert_cons_to_cf(Cons_expr, Vars, Call_stack),

	case Lst_in_cf of
		{none, []} -> {{none, []}, Upd_vars};
		_          -> {generalize_term(Lst_in_cf, []), Upd_vars}
	end.


construct_and_convert_tuple_to_cf(Tuple_expr, Vars, Call_stack) ->
	{Tuple, Upd_vars} = construct_tuple(Tuple_expr, Vars, Call_stack),
	{convert_value_in_basic_format_to_compound(Tuple), Upd_vars}.


infer_tuple_expr_type(Tuple_expr, Vars, Call_stack) ->
	{Tuple_in_cf, Upd_vars} = construct_and_convert_tuple_to_cf(Tuple_expr, Vars, Call_stack),

	case Tuple_in_cf of
		{none, []} -> {{none, []}, Upd_vars};
		_          -> {generalize_term(Tuple_in_cf, []), Upd_vars}
	end.


infer_fun_app_type(Fun_app_expr, Vars, Call_stack) ->
	[Fun_info_expr, Arg_lst_expr] = ?Query:exec(Fun_app_expr, ?Expr:children()),

	case ?Expr:type(Fun_info_expr) of 
			variable -> infer_anonymus_fun_tp(?Expr:value(Fun_info_expr), Arg_lst_expr, Vars, Call_stack);
			_        ->	infer_fun_tp(Fun_app_expr, Fun_info_expr, Arg_lst_expr, Vars, Call_stack)
	end.


infer_fun_tp(Fun_app_expr, Fun_info_expr, Arg_lst_expr, Vars, Call_stack) ->
	case ?Expr:value(Fun_info_expr) of
		':'      -> [Mod_name_expr, Fun_name_expr] = ?Query:exec(Fun_info_expr, ?Expr:children()),
				    Mod_name = ?Expr:value(Mod_name_expr),
				    Fun_name = ?Expr:value(Fun_name_expr),
			        infer_external_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack);
		Fun_name -> Fun_expr = ?Query:exec(Fun_app_expr, ?Expr:function()),
		            [Fun_mod_expr] = ?Query:exec(Fun_expr, ?Fun:module()),
		            Mod_name = ?Mod:name(Fun_mod_expr),
		            infer_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack)
	end.


infer_external_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack) ->
	case Mod_name of
		erlang     -> infer_BIFs(Fun_name, Arg_lst_expr, Vars);
		_Any_other -> infer_non_BIF_external_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack)
	end.


infer_BIFs(Fun_name, Arg_lst_expr, Vars) ->
	Arg_lst_elems_exprs = ?Query:exec(Arg_lst_expr, ?Expr:children()),

	Infer_expr_tp = 
		fun(Arg_lst_elem) -> {Elem_tp, _Upd_vars} = infer_expr_tp(Arg_lst_elem, Vars, []),
			                 Elem_tp
	end,

	Arg_lst = lists:map(Infer_expr_tp, Arg_lst_elems_exprs),
	infer_BIF_fun_tp(Fun_name, Arg_lst). 


infer_BIF_fun_tp(Fun_name, _Arg_lst) when (Fun_name == is_atom)     or (Fun_name == is_binary) 
									  or (Fun_name == is_bitstring) or (Fun_name == is_boolean)
									  or (Fun_name == is_float)     or (Fun_name == is_function)
		                              or (Fun_name == is_integer)   or (Fun_name == is_list) 
		                              or (Fun_name == is_map)       or (Fun_name == is_number)
		                              or (Fun_name == is_pid)       or (Fun_name == is_port)
		                              or (Fun_name == is_record)    or (Fun_name == is_reference)
		                              or (Fun_name == is_tuple) ->
	{boolean, []};
infer_BIF_fun_tp(tuple_to_list, _Arg_lst) ->
	{list, [{any, []}]};
infer_BIF_fun_tp(exit, [Reason]) ->
	{atom, [exit]};
infer_BIF_fun_tp(exit, [Pid, Reason]) ->
	{boolean, [true]};
infer_BIF_fun_tp(hd, {any, []}) ->
	{any, []};
infer_BIF_fun_tp(hd, {Lst_tp, [Prop_sec, Improp_sec]}) ->
	Prop_sec;
infer_BIF_fun_tp(hd, {Lst_tp, [Prop_sec]}) ->
	Prop_sec;
infer_BIF_fun_tp(hd, _) ->
	{none, []};
infer_BIF_fun_tp(Fun_name, _Arg_lst) when (Fun_name == spawn) or (Fun_name == self) ->
	{pid, []}.


infer_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack) ->
	case lists:member(Fun_name, ?BIFs) of
		true  -> infer_BIFs(Fun_name, Arg_lst_expr, Vars);
		false -> infer_non_BIF_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack)
	end.


find_var_by_name(Required_var_Name, Vars) ->
	Res = lists:filter(fun({Var_name, _}) -> Required_var_Name == Var_name end, Vars),

	case Res of
		[]    -> {variable, [Required_var_Name]};
		[Var] -> Var
	end.


is_bounded(Var_name, Vars) ->
	Var = find_var_by_name(Var_name, Vars),

	case Var of
		{variable, _Var_name} -> false;
		_  -> true
	end.


infer_anonymus_fun_tp(Var_name, Arg_lst_expr, Vars, Call_stack) ->
	case find_var_by_name(Var_name, Vars) of
		{variable, _Var_name}         -> infer_anon_func_app_without_body(Arg_lst_expr, Vars);
		{Var_name, [{fun_expr, _}]}   -> infer_anon_func_app(Var_name, Arg_lst_expr, Vars);
		{Var_name, [{implicit_fun, {{current_mod, Mod_name}, Fun_name, _Arity}}]}  -> infer_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack);
		{Var_name, [{implicit_fun, {{external_mod, Mod_name}, Fun_name, _Arity}}]} -> infer_external_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack);
		_                             -> {none, []}
	end.


infer_anon_func_app_without_body(Arg_lst_expr, _Vars) ->
	Arg_lst_children = ?Query:exec(Arg_lst_expr, ?Expr:children()),
	Fun = 
		fun(Arg) -> {Tp, _} = infer_expr_tp(Arg, [], []),
	 				Tp 
	end,

	Arg_lst = lists:map(Fun, Arg_lst_children),
	{func, [Arg_lst, [any]]}.


infer_anon_func_app(Var_name, Arg_lst_expr, Vars) ->
	{_Var_name, [{fun_expr, Fun_expr}]} = find_var_by_name(Var_name, Vars),
	Arg_list_children = ?Query:exec(Arg_lst_expr, ?Expr:children()),
	Fun = fun(Arg) -> {Tp, _} = infer_expr_tp(Arg, Vars, []),
				      Tp 
	end,

	Arg_lst = lists:map(Fun, Arg_list_children),

	Clause = ?Query:exec(Fun_expr, ?Expr:clauses()),
	Patterns = ?Query:exec(Clause, ?Clause:patterns()),
	[Fun_expr_vars] = replace_clauses_params_with_args([Patterns], Arg_lst),

	New_var_list = replace_shadowed_vars_vals(Fun_expr_vars, Vars),
	
	get_clause_type(Clause, New_var_list, []).


replace_shadowed_vars_vals([], Vars) -> Vars;
replace_shadowed_vars_vals([Anon_fun_var | Anon_fun_vars], Vars) ->
	New_var_list = replace_shadowed_vars_val(Anon_fun_var, Vars, []),
	replace_shadowed_vars_vals(Anon_fun_vars, New_var_list).
	

replace_shadowed_vars_val(Anon_fun_var, [], New_var_list) ->
	[Anon_fun_var | New_var_list];
replace_shadowed_vars_val({Var_name, Val1}, [{Var_name, _Val2} | Vars], New_var_list) ->
	[{Var_name, Val1} | New_var_list] ++ Vars;
replace_shadowed_vars_val(Anon_fun_var, [Var | Vars], New_var_list) ->
	replace_shadowed_vars_val(Anon_fun_var, Vars, [Var | New_var_list]).


infer_non_BIF_external_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack) ->
	Arg_lst = ?Query:exec(Arg_lst_expr, ?Expr:children()),
	Arity = length(Arg_lst),
	Spec_info = spec_proc:get_spec_type(Mod_name, Fun_name, Arity),

	case Spec_info of
		[Return_type] -> generalize_term(Return_type, []);
		[] -> infer_non_BIF_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Vars, Call_stack)
	end.


infer_non_BIF_internal_fun_tp(Mod_name, Fun_name, Arg_lst_expr, Parent_fun_vars, Call_stack) ->
	Arg_lst_children = ?Query:exec(Arg_lst_expr, ?Expr:children()),

	Fun = fun(Arg) -> {Tp, _} = infer_expr_tp(Arg, Parent_fun_vars, Call_stack),
		              Tp
	end,

	Arg_lst = lists:map(Fun, Arg_lst_children),
	Arity = length(Arg_lst),
	Clauses_vars_pair = find_actual_clauses(Mod_name, Fun_name, Arity, Arg_lst),
	Actual_clauses = lists:map(fun({Clause, _}) -> Clause end, Clauses_vars_pair),
	Vars = lists:map(fun({_, Var}) -> Var end, Clauses_vars_pair),

	{Root, Call_stack_funs} = Call_stack,
	Prev_fun_sig = 
		case Call_stack_funs of
			[] -> Root;
			_  -> hd(Call_stack_funs) 
		end,
 
	Is_recursive_fun = {Mod_name, Fun_name, Arity} == Prev_fun_sig,
	Is_mutually_rec_funs = lists:member({Mod_name, Fun_name, Arity}, Call_stack_funs),

	Fun_tp = 
		case {Is_recursive_fun, Is_mutually_rec_funs} of
			{true, false}  -> [{none, []}];
			{_, true}      -> [{any, []}];
			{false, false} -> Upd_call_stack = {Root, [{Mod_name, Fun_name, Arity} | Call_stack_funs]},
			                  get_clauses_type(Actual_clauses, Vars, Upd_call_stack, [])
		end,

    case length(Fun_tp) of
	    1 -> hd(Fun_tp);
	    _ -> {union, Fun_tp}
    end.


replace_clauses_params_with_args([], _) -> [];
replace_clauses_params_with_args([Pat | Pats], Args) ->
	Upd_vars = replace_clause_params_with_args(Pat, Args, []),
	[Upd_vars | replace_clauses_params_with_args(Pats, Args)].


replace_clause_params_with_args([], [], Vars) -> Vars;
replace_clause_params_with_args([Par | Pars], [Arg | Args], Vars) ->
	{Par_tp, _Upd_vars} = infer_expr_tp(Par, [], []),

	case are_matching_types(Par_tp, Arg) of
		false -> [];
		_     -> 	case ?Expr:type(Par) of
						variable -> Var_name = ?Expr:value(Par),
									New_var = {Var_name, [Arg]},
						            replace_clause_params_with_args(Pars, Args, [New_var | Vars]);
						cons     -> {Ls_cons_in_cf, Upd_vars} = construct_and_convert_cons_to_cf(Par, Vars, []),
									{_Expr_tp, Upd_vars2} = bound_cons_vars(Ls_cons_in_cf, Arg, Upd_vars),
									replace_clause_params_with_args(Pars, Args, Upd_vars2);
						tuple    -> {Ls_tuple_in_cf, Upd_vars} = construct_and_convert_tuple_to_cf(Par, Vars, []),
									{_Expr_tp, Upd_vars2} = bound_tuple_vars(Ls_tuple_in_cf, Arg, Arg, Upd_vars),
									replace_clause_params_with_args(Pars, Args, Upd_vars2);
						_Other   -> replace_clause_params_with_args(Pars, Args, Vars)	
					end
    end.




infer_parenthesis_inf(Expr, Vars, Call_stack) ->
	[Child] = get_children(Expr),
	infer_expr_tp(Child, Vars, Call_stack).


infer_match_expr_inf(Expr, Vars, Call_stack) ->
	[Ls_expr, Rs_expr] = get_children(Expr),

	case ?Expr:type(Ls_expr) of
		variable   -> bound_var_expr(Ls_expr, Rs_expr, Vars, Call_stack);
		cons       -> bound_cons(Ls_expr, Rs_expr, Vars, Call_stack);
		tuple      -> bound_tuple(Ls_expr, Rs_expr, Vars, Call_stack);
		_Simple_tp -> match_simple_tp_expr(Ls_expr, Rs_expr, Vars, Call_stack)
	end.


match_simple_tp_expr(Ls_expr, Rs_expr, Vars, Call_stack) ->
	case ?Expr:type(Rs_expr) of
		variable -> bound_var_expr(Rs_expr, Ls_expr, Vars, Call_stack);
		_        -> {Ls_expr_tp, Upd_vars} = infer_expr_tp(Ls_expr, Vars, Call_stack),
					{_Rs_expr_tp, Upd_vars2} = infer_expr_tp(Rs_expr, Upd_vars, Call_stack),
					{Ls_expr_tp, Upd_vars2}
	end.
		           
bound_tuple(Ls_tuple, Rs_tuple, Vars, Call_stack) ->
	{Ls_tuple_tp, Upd_vars} = construct_and_convert_tuple_to_cf(Ls_tuple, Vars, Call_stack),
	{Rs_tuple_gen_tp, Upd_vars2} = infer_expr_tp(Rs_tuple, Upd_vars, Call_stack),
	bound_tuple_vars(Ls_tuple_tp, Rs_tuple_gen_tp, Rs_tuple_gen_tp, Upd_vars2).


bound_tuple_vars({ungen_tuple, []}, {tuple, []}, Match_expr_tp, Vars) ->
	{Match_expr_tp, Vars};
bound_tuple_vars(_Ls_tuple, {any, []}, _Match_expr_tp, Vars) ->
	{{any, []}, Vars};

bound_tuple_vars({ungen_tuple, Pat = [{variable, [Var_name]} | Ls_elems]}, {union, Elems}, Match_expr_tp, Vars) ->
	Tuple = find_tuple_among_elems(Elems, length(Pat)),
	bound_tuple_vars({ungen_tuple, Pat}, Tuple, Tuple, Vars);
bound_tuple_vars({ungen_tuple, [{variable, [Var_name]} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) ->
	{Rs_elem, Upd_vars} = bound_var_to_value(Var_name, Rs_elem, Vars), 
    bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Upd_vars);
bound_tuple_vars({ungen_tuple, [{ungen_list, Lst_elems} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) -> 
	{_Lst_tp, Upd_vars} = bound_cons_vars({ungen_list, Lst_elems}, Rs_elem, Vars),
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Upd_vars);
bound_tuple_vars({ungen_tuple, [{ungen_tuple, Tuple_elems} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) -> 
	{_Tuple, Upd_vars} = bound_tuple_vars({ungen_tuple, Tuple_elems}, Rs_elem, Rs_elem, Vars),
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Upd_vars);
bound_tuple_vars({ungen_tuple, [_Ls_elem | Ls_elems]}, {tuple, [_Rs_elem | Rs_elems]}, Match_expr_tp, Vars) ->
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Vars).


bound_var_expr(Ls_expr, Rs_expr, Vars, Call_stack) ->
	Var_name = ?Expr:value(Ls_expr),
	bound_var_to_expr_tp(Var_name, Rs_expr, Vars, Call_stack).


bound_var_to_expr_tp(Var_name, Expr, Vars, Call_stack) ->
	{Expr_tp, Upd_vars} = infer_expr_tp(Expr, Vars, Call_stack),
	bound_var_to_value(Var_name, Expr_tp, Upd_vars).


bound_var_to_value(Var_name, Value, Vars) ->
	Is_bounded = is_bounded(Var_name, Vars),


	case Is_bounded of
		true  -> %Upd_vars2 = replace_shadowed_vars_val({Var_name, [Value]}, Vars, []),
		         {Value, Vars};
		false -> New_var = {Var_name, [Value]},
		         {Value, [New_var | Vars]}
	end.


find_lst_among_elems([]) -> [];
find_lst_among_elems([{union, Elems} | _T]) ->
	find_lst_among_elems(Elems);
find_lst_among_elems([{Elem_tp, Elem_val} | _Elems]) when (Elem_tp == empty_list) or (Elem_tp == nonempty_list)
                                                       or (Elem_tp == nonempty_improper_list) or (Elem_tp == maybe_improper_list)
                                                       or (Elem_tp == nonempty_maybe_improper_list) or (Elem_tp == list) ->                                                 
    {Elem_tp, Elem_val};
find_lst_among_elems([_Elem | Elems]) ->
	find_lst_among_elems(Elems).


find_tuple_among_elems([], _Size) -> [];
find_tuple_among_elems([{union, Elems} | _T], Size) ->
	find_tuple_among_elems(Elems, Size);
find_tuple_among_elems([{Elem_tp, Elem_val} | Elems], Size) when (Elem_tp == tuple) ->                                                 
	case Size == length(Elem_val) of
		true  -> {Elem_tp, Elem_val};
		false -> find_tuple_among_elems(Elems, Size)
	end;
find_tuple_among_elems([_Elem | Elems], Size) ->
	find_tuple_among_elems(Elems, Size).


bound_cons(Ls_expr, Rs_expr, Vars, Call_stack) ->
	{Ls_cons_tp, Upd_vars} = construct_and_convert_cons_to_cf(Ls_expr, Vars, Call_stack),
	{Rs_cons_tp, Upd_vars2} = infer_expr_tp(Rs_expr, Upd_vars, Call_stack),
	bound_cons_vars(Ls_cons_tp, Rs_cons_tp, Upd_vars2).


bound_cons_vars({_Lst_tp, []}, {empty_list, []}, Vars) ->
	{{empty_list, []}, Vars};
bound_cons_vars({_Lst_tp, []}, Rs_cons_tp, Vars) ->
	{Rs_cons_tp, Vars};
bound_cons_vars(_Ls_cons, {any, []}, Vars) ->
	{{nonempty_list, [{any, []}]}, Vars};
bound_cons_vars(_Ls_cons, Rs_lst = {_Rs_lst_tp, [{any, []}]}, Vars) ->
	{Rs_lst, Vars};
bound_cons_vars({Lst_tp, [{ungen_tuple, Ls_tuple_elems} | T]}, {Rs_lst_tp, Rs_lst_elems}, Vars) ->
    Rs_tuple_elem = find_tuple_among_elems(Rs_lst_elems, length(Ls_tuple_elems)),
    {_Elem_tp, Upd_vars} = bound_tuple_vars({ungen_tuple, Ls_tuple_elems}, Rs_tuple_elem, Rs_tuple_elem, Vars),
    bound_cons_vars({Lst_tp, T}, {Rs_lst_tp, Rs_lst_elems}, Upd_vars); 
bound_cons_vars({Lst_tp, [{ungen_list, Ls_lst_elems} | T]}, {Rs_lst_tp, Rs_lst_elems}, Vars) ->
    Rs_lst_elem = find_lst_among_elems(Rs_lst_elems),
    {_Elem_tp, Upd_vars} = bound_cons_vars({ungen_list, Ls_lst_elems}, Rs_lst_elem, Vars),
    bound_cons_vars({Lst_tp, T}, {Rs_lst_tp, Rs_lst_elems}, Upd_vars);                                                                        
bound_cons_vars({Lst_tp, [{variable, [Var_name]} | T]}, Rs_cons_tp, Vars) ->
	New_var = bound_cons_var({Lst_tp, [{variable, [Var_name]}]}, Rs_cons_tp),

	case is_bounded(Var_name, Vars) of
		true  -> %Upd_vars = replace_shadowed_vars_val(New_var, Vars, []),
		         bound_cons_vars({Lst_tp, T}, Rs_cons_tp, Vars);
		false -> bound_cons_vars({Lst_tp, T}, Rs_cons_tp, [New_var | Vars])
	end;
bound_cons_vars(Rs_cons = {_Lst_tp, [{'...', [Var_name]}]}, Rs_cons_tp, Vars) ->
	New_var = bound_cons_var(Rs_cons, Rs_cons_tp),
	case is_bounded(Var_name, Vars) of
		true  -> %Upd_vars = replace_shadowed_vars_val(New_var, Vars, []),
		         {Rs_cons_tp, Vars};
		false -> {Rs_cons_tp, [New_var | Vars]}
	end;
bound_cons_vars({_Lst_tp, {_Elem_tp, _Elem_Val}}, Rs_cons_tp, Vars) ->
	{Rs_cons_tp, Vars};
bound_cons_vars({Lst_tp, [_Elem | T]}, Rs_cons_tp, Vars) ->
	bound_cons_vars({Lst_tp, T}, Rs_cons_tp, Vars).


bound_cons_var({ungen_list, [{'...', [Var_name]}]}, Rs_cons = {_Rs_lst_tp, [_Proper_part, Improp_part]}) ->
	{Var_name, [{union, [Rs_cons, Improp_part]}]};
bound_cons_var({ungen_list, [{'...', [Var_name]}]}, {Rs_lst_tp, [Proper_part]}) ->
	Upd_lst_tp = generalize_lst_tp(Rs_lst_tp, empty_list),
	{Var_name, [{Upd_lst_tp, [Proper_part]}]};
bound_cons_var({ungen_list, [{variable, [Var_name]}]}, {_Rs_lst_tp, [Proper_part, _Improp_part]}) ->
	{Var_name, [Proper_part]};
bound_cons_var({ungen_list, [{variable, [Var_name]}]}, {_Rs_lst_tp, [Proper_part]}) ->
	{Var_name, [Proper_part]}.


generalize_elems(Elems, []) ->
	generalize_elems(Elems, ?ELEMS_TBL);
generalize_elems([], Elems_tbl) ->
	Elems_tbl_secs = tuple_to_list(Elems_tbl),
	Gen_elems = convert_elems_tbl_to_internal_format(Elems_tbl_secs, []),
	{Gen_elems, Elems_tbl};
%generalize_elems([Elem | Elems], Elems_tbl) when element(?ANY_SEC_INDEX, Elems_tbl) == {any, {any, []}} ->
%	{{any, []}, Elems_tbl};
generalize_elems([Elem | Elems], Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_with_new_elem(Elem, Elems_tbl),
	generalize_elems(Elems, Upd_elems_tbl).

generalize_term({any, []}, []) ->
	{any, []};
generalize_term(Term, []) ->
	generalize_term(Term, ?ELEMS_TBL);
generalize_term({Tp, Elem_val}, _Elems_tbl) when (Tp == fun_expr) or (Tp == implicit_fun) ->
	{Tp, Elem_val};
generalize_term({union, Elem_val}, Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_with_new_elems(Elem_val, Elems_tbl),
	Elems_tbl_secs = tuple_to_list(Upd_elems_tbl),
	convert_elems_tbl_to_internal_format(Elems_tbl_secs, []);
generalize_term({boolean, Elem_val}, _Elems_tbl) ->
	{boolean, Elem_val};
generalize_term({Elem_tp, Elem_val}, _Elems_tbl) when (Elem_tp == neg_integer) or (Elem_tp == pos_integer) 
	                                               or (Elem_tp == non_neg_integer) or (Elem_tp == integer) 
	                                               or (Elem_tp == float) or (Elem_tp == number) 
	                                               or (Elem_tp == atom) or (Elem_tp == pid)->
	{Elem_tp, Elem_val};
generalize_term({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == empty_list) or (Elem_tp == ungen_list)
												  or (Elem_tp == nonempty_list)
												  or (Elem_tp == nonempty_improper_list) or (Elem_tp == maybe_improper_list)
												  or (Elem_tp == nonempty_maybe_improper_list) or (Elem_tp == list) ->
	{Gen_lst, _} = generalize_lst({Elem_tp, Elem_val}, Elems_tbl),
	Gen_lst;
generalize_term({Elem_tp, Elem_val}, _Elems_tbl) when (Elem_tp == ungen_tuple) or (Elem_tp == tuple) ->
	generalize_tuple({Elem_tp, Elem_val}).


convert_elems_tbl_to_internal_format([], Res) ->
	Upd_res = lists:reverse(lists:concat(Res)),

	case length(Upd_res) of
		0 -> [];
		1 -> hd(Upd_res);
		_ -> {union, Upd_res}
	end;
convert_elems_tbl_to_internal_format([{_Label, []} | T], Res) ->
	convert_elems_tbl_to_internal_format(T, Res);	
convert_elems_tbl_to_internal_format([{tuples, Elems_tbl} | T], Res) ->
	Tuples = generate_tuples_from_tuple_tbl({tuples, Elems_tbl}, []),
	convert_elems_tbl_to_internal_format(T, [Tuples | Res]);
convert_elems_tbl_to_internal_format([{lists, [{empty_list, _Elems_tbl}]} | T], Res) ->
	convert_elems_tbl_to_internal_format(T, [[{empty_list, []}] | Res]);
convert_elems_tbl_to_internal_format([{lists, [{Lst_tp, Elems_tbl}]} | T], Res) ->
	Elems_tbl_secs = tuple_to_list(Elems_tbl),
	Lst = build_lst(Lst_tp, Elems_tbl_secs, []),
	convert_elems_tbl_to_internal_format(T, [[Lst] | Res]);
convert_elems_tbl_to_internal_format([{_Label, Tp} | T], Res) ->
	convert_elems_tbl_to_internal_format(T, [Tp | Res]).

upd_elems_tbl_with_new_elem({variable, _Var_name}, Elems_tbl) ->
	set_elems_tbl_to_any(Elems_tbl);
upd_elems_tbl_with_new_elem({any, []}, Elems_tbl) ->
	set_elems_tbl_to_any(Elems_tbl);
upd_elems_tbl_with_new_elem({union, Elem_val}, Elems_tbl) ->
	upd_elems_tbl_with_new_elems(Elem_val, Elems_tbl);
upd_elems_tbl_with_new_elem({boolean, Elem_val}, Elems_tbl) ->
	upd_elems_tbl_by_index({boolean, Elem_val}, Elems_tbl, ?BOOLS_SEC_INDEX);
upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == neg_integer) or (Elem_tp == pos_integer) 
	                                                          or (Elem_tp == non_neg_integer) or (Elem_tp == integer) 
	                                                          or (Elem_tp == float) or (Elem_tp == number) ->
	upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?NUMS_SEC_INDEX);
upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == atom) ->
	upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?ATOMS_SEC_INDEX);
upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == pid) ->
	upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?PIDS_SEC_INDEX);
upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == empty_list) or (Elem_tp == ungen_list)
												              or (Elem_tp == nonempty_list)
												              or (Elem_tp == nonempty_improper_list) or (Elem_tp == maybe_improper_list)
												              or (Elem_tp == nonempty_maybe_improper_list) or (Elem_tp == list) ->
	upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?LISTS_SEC_INDEX);
upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl) when (Elem_tp == ungen_tuple) or (Elem_tp == tuple) ->
	upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?TUPLES_SEC_INDEX).


upd_elems_tbl_with_new_elems([], Elems_tbl) ->
	Elems_tbl;
upd_elems_tbl_with_new_elems([{Elem_tp, Elem_val} | T], Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_with_new_elem({Elem_tp, Elem_val}, Elems_tbl),
	upd_elems_tbl_with_new_elems(T, Upd_elems_tbl).


upd_tuple_sec_with_gen_tuple({tuple, Elems}, {tuples, []}) ->
	Elems_num = length(Elems),
	Tuple_tbl = lists:duplicate(Elems_num, ?ELEMS_TBL),
	{tuples, upd_tuple_tbl_with_new_elem(Elems, [Tuple_tbl])};
upd_tuple_sec_with_gen_tuple({tuple, Elems}, {tuples, Tuple_tbl}) ->
	{tuples, upd_tuple_tbl_with_new_elem(Elems, Tuple_tbl)}.


upd_tuple_sec_with_ungen_tuple({tuple, Elems}, {tuples, []}) ->
	Elems_num = length(Elems),
	Tuple_tbl = add_elems_to_tuple_tbl(Elems, lists:duplicate(Elems_num, ?ELEMS_TBL)),
	{tuples, [Tuple_tbl]};
upd_tuple_sec_with_ungen_tuple({tuple, Elems}, {tuples, Elem_tbls}) ->
	{tuples, upd_tuple_tbl_with_new_elem(Elems, Elem_tbls)}.


upd_tuple_tbl_with_new_elem(Elems, []) ->
	Elems_num = length(Elems),
	Tuple_tbl = add_elems_to_tuple_tbl(Elems, lists:duplicate(Elems_num, ?ELEMS_TBL)),
	[Tuple_tbl];
upd_tuple_tbl_with_new_elem(Elems, [Tuple_tbl_item | Items]) ->
	case length(Elems) == length(Tuple_tbl_item) of
		true  -> [add_elems_to_tuple_tbl(Elems, Tuple_tbl_item) | Items];
		false -> [Tuple_tbl_item | upd_tuple_tbl_with_new_elem(Elems, Items)]
	end.


add_elems_to_tuple_tbl([], []) -> 
	[];
add_elems_to_tuple_tbl([_Elem | Elems], [Tuple_tbl_item | Items]) when (element(1, Tuple_tbl_item) == {any, [{any, []}]}) ->
	[Tuple_tbl_item | add_elems_to_tuple_tbl(Elems, Items)];
add_elems_to_tuple_tbl([{variable, _Val} | Elems], [_Tuple_tbl_item | Items]) ->
	Upd_item = setelement(1, ?ELEMS_TBL, {any, [{any, []}]}),
	[Upd_item | add_elems_to_tuple_tbl(Elems, Items)];
add_elems_to_tuple_tbl([Elem | Elems], [Tuple_tbl_item | Items]) ->
	Upd_item =
		case Elem of
			{union, U_elems} -> upd_elems_tbl_with_new_elems(U_elems, Tuple_tbl_item);
			Elem             -> upd_elems_tbl_with_new_elem(Elem, Tuple_tbl_item)
		end, 
	[Upd_item | add_elems_to_tuple_tbl(Elems, Items)].

generate_tuples_from_tuple_tbl({tuples, []}, Res) ->
	Res;
generate_tuples_from_tuple_tbl({tuples, [Tuple_tbl_item | Items]}, Res) ->
	Tuple = {tuple, lists:map(fun(Elems_tbl) -> 
								convert_elems_tbl_to_internal_format(tuple_to_list(Elems_tbl), []) end, Tuple_tbl_item)},

	generate_tuples_from_tuple_tbl({tuples, Items}, [Tuple | Res]).


upd_elems_tbl_by_index(_Elem, Elems_tbl, ?ANY_SEC_INDEX) ->
	set_elems_tbl_to_any(Elems_tbl);
upd_elems_tbl_by_index({Tp, Val}, Elems_tbl, ?IMPROPER_ELEMS_SEC_INDEX) ->
    Sec = element(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl),
	Upd_improp_sec = upd_improp_elems_sec({Tp, Val}, Sec),
	setelement(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl, Upd_improp_sec);
upd_elems_tbl_by_index(_Elem, Elems_tbl, _) when (element(1, Elems_tbl) == {any, [{any, []}]}) ->
	Elems_tbl;
upd_elems_tbl_by_index({_Tp, Val}, Elems_tbl, ?UNION_INDEX) ->
	upd_elems_tbl_with_new_elems(Val, Elems_tbl);
upd_elems_tbl_by_index({Tp, Val}, Elems_tbl, Index) ->
	Sec = element(Index, Elems_tbl),

	Upd_sec = 
	case Index of
		?BOOLS_SEC_INDEX          -> upd_bools_sec({Tp, Val}, Sec);
		?NUMS_SEC_INDEX           -> upd_numbers_sec({Tp, Val}, Sec);
		?ATOMS_SEC_INDEX          -> upd_atoms_sec({Tp, Val}, Sec);
		?LISTS_SEC_INDEX          -> upd_lst_sec({Tp, Val}, Sec);
		?TUPLES_SEC_INDEX         -> upd_tuple_sec({tuple, Val}, Sec);
		?PIDS_SEC_INDEX           -> upd_pids_sec({Tp, Val}, Sec)
%		?IMPROPER_ELEMS_SEC_INDEX -> upd_improp_elems_sec({Tp, Val}, Sec)
	end,

	setelement(Index, Elems_tbl, Upd_sec).


upd_pids_sec({pid, []}, {pids, []}) ->
	{pids, [{pid, []}]};
upd_pids_sec({pid, []}, {pids, [{pid, []}]}) ->
	{pids, [{pid, []}]}.


upd_tuple_sec({Tp, Val}, Sec) ->
	case Tp of
		tuple       -> upd_tuple_sec_with_gen_tuple({Tp, Val}, Sec);
		ungen_tuple -> upd_tuple_sec_with_gen_tuple({Tp, Val}, Sec)
	end.


upd_lst_sec({Tp, Val}, Sec) when (Tp == nonempty_list)
						      or (Tp == nonempty_improper_list) or (Tp == maybe_improper_list)
						      or (Tp == nonempty_maybe_improper_list) or (Tp == list) ->
	upd_lst_sec_with_gen_lst({Tp, Val}, Sec);
upd_lst_sec({Tp, Val}, Sec) ->
	upd_lst_sec_with_ungen_lst({Tp, Val}, Sec).


generalize_tuple({Tp, Val}) ->
	Upd_tuple_sec =
		case Tp of
			tuple       -> upd_tuple_sec_with_gen_tuple({Tp, Val}, {tuples, []});
			ungen_tuple -> upd_tuple_sec_with_ungen_tuple({tuple, Val}, {tuples, []})
		end,  
		 
	[Gen_tuple] = generate_tuples_from_tuple_tbl(Upd_tuple_sec, []),
	Gen_tuple.

	
%empty_list
generalize_lst({ungen_list, [{any, []}]}, _Elems_tbl) ->
	{{list, [{any, []}]}, set_elems_tbl_to_any(?ELEMS_TBL)};
generalize_lst(Empty_lst = {empty_list, []}, Elems_tbl) ->
	{Empty_lst, Elems_tbl};
generalize_lst({Lst_tp, {empty_list, []}}, Elems_tbl) ->
	generalize_lst({Lst_tp, []}, Elems_tbl);
%nonempty_maybe_improper_list
generalize_lst({ungen_list, [{'...', _Var_name}]}, Elems_tbl) ->
	{{nonempty_maybe_improper_list, [{any, []}]}, set_elems_tbl_to_any(Elems_tbl)};
generalize_lst({_Lst_tp, {ungen_list, Elems}}, Elems_tbl) ->
	Lst_sec = {lists, [{undef_list, Elems_tbl}]},
	{lists, [{Upd_lst_tp, Upd_elems_tbl}]} = upd_lst_sec_with_ungen_lst({ungen_list, Elems}, Lst_sec),

	Elems_tbl_secs = tuple_to_list(Upd_elems_tbl),
	Gen_lst = build_lst(Upd_lst_tp, Elems_tbl_secs, []),
	{Gen_lst, Upd_elems_tbl};
generalize_lst({_Lst_tp, {Tp, Elems}}, Elems_tbl) when (Tp == nonempty_list)
												    or (Tp == nonempty_improper_list) or (Tp == maybe_improper_list)
												    or (Tp == nonempty_maybe_improper_list) or (Tp == list) ->
    Lst_sec = {lists, [{undef_list, Elems_tbl}]},
	{lists, [{Upd_lst_tp, Upd_elems_tbl}]} = upd_lst_sec_with_gen_lst({Tp, Elems}, Lst_sec),

	Elems_tbl_secs = tuple_to_list(Upd_elems_tbl),
	Gen_lst = build_lst(Upd_lst_tp, Elems_tbl_secs, []),
	{Gen_lst, Upd_elems_tbl};
%improper list
generalize_lst({_Lst_tp, {Tp, Elems}}, Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Tp, Elems}, Elems_tbl, ?IMPROPER_ELEMS_SEC_INDEX),

	Elems_tbl_secs = tuple_to_list(Upd_elems_tbl),
	Gen_lst = build_lst(nonempty_improper_list, Elems_tbl_secs, []),

	{Gen_lst, Upd_elems_tbl};
generalize_lst({Lst_tp, []}, Elems_tbl) ->
	Elems_tbl_secs = tuple_to_list(Elems_tbl),

	Gen_list = 
		case Lst_tp of
			ungen_list -> build_lst(nonempty_list, Elems_tbl_secs, []);
			_          -> build_lst(Lst_tp, Elems_tbl_secs, [])
		end,
		
	{improper_elems, Improp_elems} = element(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl),

	case Improp_elems of
		[{empty_list, []}] -> {Gen_list, Elems_tbl};
		[]                -> {Gen_list, setelement(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl, {improper_elems, [{empty_list, []}]})};
		_Multiple_elems    -> {improper_elems, Upd_improp_elems} = upd_improp_elems_sec({empty_list, []}, {improper_elems, Improp_elems}),
		                     {Gen_list, setelement(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl, {improper_elems, Upd_improp_elems})}
	end;
generalize_lst({Lst_tp, [_ | T]}, Elems_tbl) when element(?ANY_SEC_INDEX, Elems_tbl) == {any, [{any, []}]} ->
	generalize_lst({Lst_tp, T}, Elems_tbl);
generalize_lst({Lst_tp, [{variable, _Val} | T]}, Elems_tbl) ->
	Upd_possible_types = set_elems_tbl_to_any(Elems_tbl),
	generalize_lst({Lst_tp, T}, Upd_possible_types);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when Elem_tp == any ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?ANY_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when Elem_tp == boolean ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?BOOLS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when ((Elem_tp == neg_integer) 
	                                                                      or (Elem_tp == pos_integer) 
	                                                                      or (Elem_tp == non_neg_integer) 
	                                                                      or (Elem_tp == integer) 
	                                                                      or (Elem_tp == float) 
	                                                                      or (Elem_tp == number)) ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?NUMS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when (Elem_tp == pid) ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?PIDS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when Elem_tp == atom ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?ATOMS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when (Elem_tp == empty_list) or (Elem_tp == ungen_list)
															      or (Elem_tp == nonempty_list)
															      or (Elem_tp == nonempty_improper_list) or (Elem_tp == maybe_improper_list)
																  or (Elem_tp == nonempty_maybe_improper_list) or (Elem_tp == list) ->																  														   
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?LISTS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when (Elem_tp == tuple) ->																  														   
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?TUPLES_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst(Lst = {Lst_tp, _Elems}, _Elems_tbl) when (Lst_tp == nonempty_list)
											         or (Lst_tp == nonempty_improper_list) or (Lst_tp == maybe_improper_list)
											         or (Lst_tp == nonempty_maybe_improper_list) or (Lst_tp == list) ->
	Lst_sec = {lists, [{Lst_tp, ?ELEMS_TBL}]},													   
	{lists, [{Lst_tp, Upd_elems_tbl}]} = upd_lst_sec_with_gen_lst(Lst, Lst_sec),
	{Lst, Upd_elems_tbl};
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when (Elem_tp == ungen_tuple) or (Elem_tp == tuple) -> 
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?TUPLES_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{union, Elem_val} | T]}, Elems_tbl) -> 
	Upd_elems_tbl = upd_elems_tbl_by_index({union, Elem_val}, Elems_tbl, ?UNION_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl).


upd_improp_elems_sec_with_elems([], Improp_sec) ->
	Improp_sec;
upd_improp_elems_sec_with_elems([Elem | Elems], Improp_sec) ->
	Upd_improp_sec = upd_improp_elems_sec(Elem, Improp_sec),
	upd_improp_elems_sec_with_elems(Elems, Upd_improp_sec).


upd_improp_elems_sec(Improp_elem, {improper_elems, Elems}) ->
	Elems_tbl = upd_elems_tbl_with_new_elem(Improp_elem, ?ELEMS_TBL),
	Elems_tbl_secs = tuple_to_list(Elems_tbl), 
	Gen_elem = convert_elems_tbl_to_internal_format(Elems_tbl_secs, []),

	case lists:member(Gen_elem, Elems) of
		true  -> {improper_elems, Elems};
		false -> {improper_elems, [Gen_elem | Elems]}
	end.


upd_bools_sec(Boolean, {bools, []}) ->
	{bools, [Boolean]};
upd_bools_sec({boolean, _Val}, {bools, [{boolean, []}]}) ->
	{bools, [{boolean, []}]};
upd_bools_sec({boolean, [Val]}, {bools, [{boolean, [Val]}]}) ->
	{bools, [{boolean, [Val]}]};
upd_bools_sec({boolean, [false]}, {bools, [{boolean, [true]}]}) ->
	{bools, [{boolean, []}]};
upd_bools_sec({boolean, [true]}, {bools, [{boolean, [false]}]}) ->
	{bools, [{boolean, []}]};
upd_bools_sec({boolean, []}, _) ->
	{bools, [{boolean, []}]}.


upd_atoms_sec(Atom, {atoms, []}) ->
	{atoms, [Atom]};
upd_atoms_sec({atom, []}, _) ->
	{atoms, [{atom, []}]};
upd_atoms_sec(_, {atoms, [{atom, []}]}) ->
	{atoms, [{atom, []}]};
upd_atoms_sec({Tp, Val}, {atoms, Vals}) ->
	case lists:member({Tp, Val}, Vals) of
		true -> {atoms, Vals};
		false -> {atoms, [{Tp, Val} | Vals]}
	end.


upd_numbers_sec({Tp, Val}, {nums, []}) ->
	{Tp, [{Tp, Val}]};
upd_numbers_sec({number, []}, _) ->
	{number, [{number, []}]};
upd_numbers_sec(_Number, Nums = {number, [{number, []}]}) ->
	Nums;
upd_numbers_sec({Tp, _Val}, {Tp, [{Tp, []}]}) ->
	{Tp, [{Tp, []}]};	
upd_numbers_sec({Tp, []}, {Tp, _}) ->
	{Tp, [{Tp, []}]};	
upd_numbers_sec({Tp, _Val}, {integer, [{integer, []}]}) when (Tp == neg_integer) or (Tp == pos_integer) 
                                                         or (Tp == non_neg_integer) -> 
	{integer, [{integer, []}]};
upd_numbers_sec({integer, _Val}, {Gen_tp, [{Gen_tp, []}]}) when (Gen_tp == neg_integer) or (Gen_tp == pos_integer) 
	                                                        or (Gen_tp == non_neg_integer) ->
	{integer, [{integer, []}]};
upd_numbers_sec({non_neg_integer, _Val}, {pos_integer, [{pos_integer, []}]}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
upd_numbers_sec({Tp, _Val}, {neg_integer, [{neg_integer, []}]}) when (Tp == pos_integer) or (Tp == non_neg_integer) ->
	{integer, [{integer, []}]};
upd_numbers_sec({pos_integer, _Val}, {non_neg_integer, [{non_neg_integer, []}]}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
upd_numbers_sec({neg_integer, _Val}, {Gen_tp, [{Gen_tp, []}]}) when (Gen_tp == pos_integer) or (Gen_tp == non_neg_integer) ->
	{integer, [{integer, []}]};		
upd_numbers_sec({float, _Val}, {Gen_tp, _Vals}) when (Gen_tp == neg_integer) or (Gen_tp == pos_integer) 
	                                            or (Gen_tp == non_neg_integer) or (Gen_tp == integer) ->
	{number, [{number, []}]};
upd_numbers_sec({Tp, _Val}, {float, _Vals}) when (Tp == neg_integer) or (Tp == pos_integer) 
	                                        or (Tp == non_neg_integer) or (Tp == integer) ->
	{number, [{number, []}]};
upd_numbers_sec({Tp, []}, {integer, _Vals}) when (Tp == neg_integer) or (Tp == pos_integer) 
	                                         or (Tp == non_neg_integer) ->
	{integer, [{integer, []}]};
upd_numbers_sec({non_neg_integer, []}, {pos_integer, _Vals}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
upd_numbers_sec({Tp, []}, {neg_integer, _Vals}) when (Tp == pos_integer) or (Tp == non_neg_integer) ->
	{integer, [{integer, []}]};
upd_numbers_sec({pos_integer, []}, {non_neg_integer, _Vals}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
upd_numbers_sec({neg_integer, []}, {Gen_tp, _Vals}) when (Gen_tp == pos_integer) or (Gen_tp == non_neg_integer) ->
	{integer, [{integer, []}]};
upd_numbers_sec({Num_Tp, [Val]}, {_Gen_tp, Vals}) -> 

	case lists:member({Num_Tp, [Val]}, Vals) of
		true  -> {Num_Tp, Vals};
		false -> {Num_Tp, [{Num_Tp, [Val]} | Vals]}
	end.


set_elems_tbl_to_any(Elems_tbl) ->
	Improp_sec = element(?IMPROPER_ELEMS_SEC_INDEX, Elems_tbl),
	Upd_elems_tbl = setelement(?ANY_SEC_INDEX, ?ELEMS_TBL, {any, [{any, []}]}),
	setelement(?IMPROPER_ELEMS_SEC_INDEX, Upd_elems_tbl, Improp_sec).


upd_lst_sec_with_gen_lst({Lst_tp, [{any, []}]}, Lst_sec) ->
    upd_lst_sec_with_ungen_lst({Lst_tp, [{any, []}]}, Lst_sec);
upd_lst_sec_with_gen_lst({Lst_tp, [{union, U_elems}]}, Lst_sec) ->
	upd_lst_sec_with_ungen_lst({Lst_tp, U_elems}, Lst_sec);
upd_lst_sec_with_gen_lst({Lst_tp, [{union, U_elems}, {union, Improp_elems}]}, Lst_sec) ->
	case Lst_sec of
		{lists, []}                            -> Upd_improp_sec = upd_improp_elems_sec_with_elems(Improp_elems, {improper_elems, []}),
		                           				  Upd_elems_tbl = setelement(?IMPROPER_ELEMS_SEC_INDEX, ?ELEMS_TBL, Upd_improp_sec), 
								       			  upd_lst_sec_with_ungen_lst({Lst_tp, U_elems ++ hd(Improp_elems)}, {lists, [{Lst_tp, Upd_elems_tbl}]});
	   	{lists, [{Gen_lst_tp, Lst_elems_tbl}]} -> Improp_sec = element(?IMPROPER_ELEMS_SEC_INDEX, Lst_elems_tbl),
		   										  Upd_improp_sec = upd_improp_elems_sec_with_elems(Improp_elems, Improp_sec),
		   										  Upd_elems_tbl = setelement(?IMPROPER_ELEMS_SEC_INDEX, Lst_elems_tbl, Upd_improp_sec),
		   										  upd_lst_sec_with_ungen_lst({Lst_tp, U_elems ++ hd(Improp_elems)}, {lists, [{Gen_lst_tp, Upd_elems_tbl}]})
	end;
%check
upd_lst_sec_with_gen_lst({Lst_tp, [{Tp, Val}, {union, Improp_elems}]}, Lst_sec) ->
	case Lst_sec of
		{lists, []}                            -> Upd_improp_sec = upd_improp_elems_sec_with_elems(Improp_elems, {improper_elems, []}),
		                           				  Upd_elems_tbl = setelement(?IMPROPER_ELEMS_SEC_INDEX, ?ELEMS_TBL, Upd_improp_sec), 
								       			  upd_lst_sec_with_ungen_lst({Lst_tp, [{Tp, Val}] ++ hd(Improp_elems)}, {lists, [{Lst_tp, Upd_elems_tbl}]});
	   	{lists, [{Gen_lst_tp, Lst_elems_tbl}]} -> Improp_sec = element(?IMPROPER_ELEMS_SEC_INDEX, Lst_elems_tbl),
		   										  Upd_improp_sec = upd_improp_elems_sec_with_elems(Improp_elems, Improp_sec),
		   										  Upd_elems_tbl = setelement(?IMPROPER_ELEMS_SEC_INDEX, Lst_elems_tbl, Upd_improp_sec),
		   										  upd_lst_sec_with_ungen_lst({Lst_tp, [{Tp, Val}] ++ hd(Improp_elems)}, {lists, [{Gen_lst_tp, Upd_elems_tbl}]})
	end;
%Check
upd_lst_sec_with_gen_lst({Lst_tp, [{union, U_elems}, Improp_elem]}, Lst_sec) ->
   	upd_lst_sec_with_ungen_lst({Lst_tp, U_elems ++ Improp_elem}, Lst_sec);
%Check
upd_lst_sec_with_gen_lst({Lst_tp, [{Tp, Val}, Improp_elem]}, Lst_sec) ->
	upd_lst_sec_with_ungen_lst({Lst_tp, [{Tp, Val} | Improp_elem]}, Lst_sec);
%Check
upd_lst_sec_with_gen_lst(Lst = {_Lst_tp, [{_Tp, _Val}]}, Lst_sec) ->
	upd_lst_sec_with_ungen_lst(Lst, Lst_sec).


upd_lst_sec_with_ungen_lst(Lst, {lists, []}) ->
	{{Lst_tp, _Elems}, Elems_tbl} = generalize_lst(Lst, ?ELEMS_TBL),
	{lists, [{Lst_tp, Elems_tbl}]};
upd_lst_sec_with_ungen_lst({Lst_tp, Elems}, {lists, [{Gen_lst_tp, Elems_tbl}]}) ->
	{{Upd_lst_tp, _}, Upd_elems_tbl} = generalize_lst({Lst_tp, Elems}, Elems_tbl),
	Upd_gen_lst_tp = generalize_lst_tp(Upd_lst_tp, Gen_lst_tp),
	{lists, [{Upd_gen_lst_tp, Upd_elems_tbl}]}.

build_lst(Lst_tp, [{improper_elems, Elems}], Res) ->
	Lst = lists:reverse(lists:concat(Res)),

	Improp_sec = 
		case Elems of
			[]                 -> [];
			[{empty_list, []}] -> [];
			[Elem]             -> [Elem];
			_                  -> [{union, Elems}]
		end,

	case length(Lst) > 1 of
		false -> {Lst_tp, Lst ++ Improp_sec};
		true  -> {Lst_tp, [{union, Lst}] ++ Improp_sec}
	end;
build_lst(Lst_tp, [{_Label, []} | T], Res) ->
	build_lst(Lst_tp, T, Res);
build_lst(Lst_tp, [{tuples, Tuple_tbl} | T], Res) ->
	Tuples = generate_tuples_from_tuple_tbl({tuples, Tuple_tbl}, []),
	build_lst(Lst_tp, T, [Tuples | Res]);
build_lst(Lst_tp, [{lists, [{empty_list, _Elems_tbl}]} | T], Res) ->
	build_lst(Lst_tp, T, [[{empty_list, []}] | Res]);
build_lst(Lst_tp, [{lists, [{Member_lst_tp, Elems_tbl}]} | T], Res) ->
	Elems_tbl_secs = tuple_to_list(Elems_tbl),
	Lst = build_lst(Member_lst_tp, Elems_tbl_secs, []),
	build_lst(Lst_tp, T, [[Lst] | Res]);
build_lst(Lst_tp, [{_Label, Tp} | T], Res) ->
	build_lst(Lst_tp, T, [Tp | Res]).


generalize_lst_tp(Lst_tp, Lst_tp) ->
	Lst_tp;
generalize_lst_tp(list, Lst2) when (Lst2 == empty_list) or (Lst2 == nonempty_list) ->
	list;
generalize_lst_tp(Lst1, list) when (Lst1 == empty_list) or (Lst1 == nonempty_list) ->
	list;
generalize_lst_tp(undef_list, Lst2) ->
	Lst2;
generalize_lst_tp(Lst1, undef_list) ->
	Lst1;
generalize_lst_tp(maybe_improper_list, Lst2) when (Lst2 == nonempty_list) or (Lst2 == nonempty_improper_list) 
                                               or (Lst2 == nonempty_maybe_improper_list) or (Lst2 == list)
                                               or (Lst2 == empty_list) ->
	maybe_improper_list;
generalize_lst_tp(Lst1, maybe_improper_list) when (Lst1 == nonempty_list) or (Lst1 == nonempty_improper_list) 
                                               or (Lst1 == nonempty_maybe_improper_list) or (Lst1 == list)
                                               or (Lst1 == empty_list) ->
	maybe_improper_list;
generalize_lst_tp(list, nonempty_improper_list) ->
	 maybe_improper_list;
generalize_lst_tp(nonempty_improper_list, list) ->
	 maybe_improper_list;
generalize_lst_tp(empty_list, nonempty_maybe_improper_list) ->
	maybe_improper_list;
generalize_lst_tp(nonempty_maybe_improper_list, empty_list) ->
	maybe_improper_list;
generalize_lst_tp(nonempty_list, empty_list) ->
	list;
generalize_lst_tp(empty_list, nonempty_list) ->
	list;
generalize_lst_tp(nonempty_improper_list, empty_list) ->
	maybe_improper_list;
generalize_lst_tp(empty_list, nonempty_improper_list) ->
	maybe_improper_list;
generalize_lst_tp(nonempty_maybe_improper_list, Lst2) when (Lst2 == nonempty_list) or (Lst2 == nonempty_improper_list)
                                                        or (Lst2 == list) ->
	nonempty_maybe_improper_list;
generalize_lst_tp(Lst1, nonempty_maybe_improper_list) when (Lst1 == nonempty_list) or (Lst1 == nonempty_improper_list)
                                                        or (Lst1 == list) ->
	nonempty_maybe_improper_list;
generalize_lst_tp(nonempty_improper_list, nonempty_list) ->
	nonempty_maybe_improper_list;	
generalize_lst_tp(nonempty_list, nonempty_improper_list) ->
	nonempty_maybe_improper_list.

infer_infix_expr_type(Expr, Operation, Vars, Call_stack) when (Operation == 'orelse') or (Operation == 'andalso') ->
	[Sub_expr1, Sub_expr2] = ?Query:exec(Expr, [exprcl]),
    {Clause1_tp, _} = get_clause_type(Sub_expr1, Vars, Call_stack),
    {Clause2_tp, _} = get_clause_type(Sub_expr2, Vars, Call_stack),
    compute_infix_expr(Clause1_tp, Clause2_tp, Operation);	
infer_infix_expr_type(Expr, Operation, Vars, Call_stack) ->
	[Sub_expr1, Sub_expr2] = get_children(Expr),
	{Expr_inf1, Upd_vars} = infer_expr_tp(Sub_expr1, Vars, Call_stack),
	{Expr_inf2, _Upd_vars2} = infer_expr_tp(Sub_expr2, Upd_vars, Call_stack),
%Добавить проверку на правильность типа	
	compute_infix_expr(Expr_inf1, Expr_inf2, Operation).

infer_prefix_expr_type(Expr, Operation, Vars, Call_stack) ->
	[Sub_expr] = ?Query:exec(Expr, ?Expr:children()),
	{Sub_expr_inf, _Upd_vars} = infer_expr_tp(Sub_expr, Vars, Call_stack),
	compute_prefix_expr(Sub_expr_inf, Operation).

compute_prefix_expr({none, []}, _Operation) ->
	{none, []};
compute_prefix_expr({union, Union_elems}, Operation) -> 
	{union, lists:map(fun(Expr1) -> compute_prefix_expr(Expr1, Operation) end, Union_elems)};
compute_prefix_expr({boolean, []}, 'not') ->
	{boolean, []};
compute_prefix_expr({boolean, [Val]}, 'not') ->
	{boolean, [not Val]};
compute_prefix_expr({float, [Val]}, '+') ->
	{float, [+Val]};
compute_prefix_expr({Tp, [Val]}, '+') when (Tp == neg_integer)     or (Tp == pos_integer) 
                                        or (Tp == non_neg_integer) or (Tp == integer) ->
	{integer, [+Val]};

compute_prefix_expr({float, [Val]}, '-') ->
	{float, [-Val]};
compute_prefix_expr({Tp, [Val]}, '-') when (Tp == neg_integer)     or (Tp == pos_integer) 
                                        or (Tp == non_neg_integer) or (Tp == integer) ->
	{integer, [-Val]};

compute_prefix_expr({Tp, [Val]}, 'bnot') when (Tp == neg_integer)       or (Tp == pos_integer) 
                                             or (Tp == non_neg_integer) or (Tp == integer) ->
	if
		Val < 0 -> {integer, [bnot (Val)]};
		true      -> {integer, [bnot Val]}
	end;

compute_prefix_expr({float, []}, Operation) when ((Operation == '+') or (Operation == '-')) ->
	{float, []};
compute_prefix_expr({Tp, []}, Operation) when ((Operation == '+')      or (Operation == '-')) 
                                          and ((Tp == neg_integer)     or (Tp == pos_integer) 
                                          	or (Tp == non_neg_integer) or (Tp == integer)) ->
	{integer, []};
compute_prefix_expr({Tp, []}, Operation) when ((Operation == '+') or (Operation == '-')) 
                                          and ((Tp == number)     or (Tp == any)) ->
	{number, []};

compute_prefix_expr({Tp, []}, 'bnot') when (Tp == neg_integer)     or (Tp == pos_integer) 
                                        or (Tp == non_neg_integer) or (Tp == integer) ->
	{integer, []};
compute_prefix_expr({Tp, []}, 'bnot') when (Tp == number) or (Tp == any) ->
	{number, []};
compute_prefix_expr({_Tp, _Val}, _Operation) ->
	{none, []}.


compute_infix_expr(Tp1, Tp2, _Operation) when (Tp1 == {none, []}) or (Tp2 == {none, []}) ->
	{none, []};
compute_infix_expr({boolean, [Value1]}, {boolean, [Value2]}, ',') ->
	{boolean, [Value1 and Value2]};
compute_infix_expr({boolean, [Value1]}, {boolean, [Value2]}, ';') ->
	{boolean, [Value1 or Value2]};
compute_infix_expr(_Expr1, _Expr2, Operation) when (Operation == ',') or (Operation == ';') ->
	{boolean, []};
compute_infix_expr({any, []}, {any, []}, '++') ->
	{list, [{any, []}]};
compute_infix_expr(Lst1, Lst2, '++') when (Lst1 == {any, []}) or (Lst2 == {any, []}) ->
	{nonempty_maybe_improper_list, [{any, []}]};
compute_infix_expr({any, []}, {empty_list, []}, '++') ->
	{list, [{any, []}]};
compute_infix_expr({empty_list, []}, {any, []}, '++') ->
	{any, []};
compute_infix_expr(Lst1, Lst2, '++') ->
	{Concat_op_res, _} = generalize_elems([Lst1, Lst2], []),
	Concat_op_res;

compute_infix_expr(Lst1, Lst2, '--') ->
	Lst1;

compute_infix_expr({union, Union_elems1}, {union, Union_elems2}, Operation) -> 
	Two_unions_merged = [compute_infix_expr(Union_elem1, Union_elem2, Operation) || 
							Union_elem1 <- Union_elems1, Union_elem2 <- Union_elems2],
	{union, lists:usort(Two_unions_merged)};
compute_infix_expr({union, Union_elems}, Expr2, Operation) -> 
	{union, lists:map(fun(Expr1) -> compute_infix_expr(Expr1, Expr2, Operation) end, Union_elems)};
compute_infix_expr(Expr1, {union, Union_elems}, Operation) -> 
	{union, lists:map(fun(Expr2) -> compute_infix_expr(Expr1, Expr2, Operation) end, Union_elems)};

compute_infix_expr({boolean, [true]}, _Rs_expr, 'orelse') ->
	{boolean, [true]};
compute_infix_expr({boolean, []}, _Rs_expr, Operation) when (Operation == 'and') or (Operation == 'or')
														 or (Operation == 'xor') or ('orelse')
														 or (Operation == 'andalso')  ->
	{boolean, []};
compute_infix_expr(_Ls_expr, {boolean,[]}, Operation) when (Operation == 'and') or (Operation == 'or')
													    or (Operation == 'xor') or ('orelse')
													    or (Operation == 'andalso')  ->
	{boolean, []};
compute_infix_expr({boolean, [Val1]}, {boolean, [Val2]}, 'and') ->
	{boolean, [Val1 and Val2]};
compute_infix_expr({boolean, [Val1]}, {boolean, [Val2]}, 'or') ->
	{boolean, [Val1 or Val2]};
compute_infix_expr({boolean, [Val1]}, {boolean, [Val2]}, 'xor') ->
	{boolean, [Val1 xor Val2]};
compute_infix_expr({boolean, [Val1]}, {boolean, [Val2]}, 'orelse') ->
	{boolean, [Val1 orelse Val2]};
compute_infix_expr({boolean, [Val1]}, {boolean, [Val2]}, 'andalso') ->
	{boolean, [Val1 andalso Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '==') when ((Tp1 == neg_integer)     or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == atom)            or (Tp1 == boolean)
                                                          or (Tp1 == float))
                                                        and ((Tp2 == neg_integer)     or (Tp2 == pos_integer) 
                                                          or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                          or (Tp2 == atom)            or (Tp2 == boolean)
                                                          or (Tp2 == float)) ->
    {boolean, [Val1 == Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '=:=') when (Tp1 == neg_integer)     or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == atom)            or (Tp1 == boolean)
                                                          or (Tp1 == float) -> 
    {boolean, [(Tp1 =:= Tp2) and (Val1 =:= Val2)]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '/=') when ((Tp1 == neg_integer)     or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == atom)            or (Tp1 == boolean)
                                                          or (Tp1 == float))
                                                        and ((Tp2 == neg_integer)     or (Tp2 == pos_integer) 
                                                          or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                          or (Tp2 == atom)            or (Tp2 == boolean)
                                                          or (Tp2 == float)) ->
    {boolean, [Val1 /= Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '=/=') when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == atom) or (Tp1 == boolean)
                                                          or (Tp1 == float) -> 
    {boolean, [(Tp1 =/= Tp2) and (Val1 =/= Val2)]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '=<') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == float))
                                                        and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                          or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                          or (Tp2 == float)) ->
    {boolean, [Val1 =< Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '<') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                         or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                         or (Tp1 == float))
                                                       and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                         or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                         or (Tp2 == float)) ->
    {boolean, [Val1 < Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '>=') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                          or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                          or (Tp1 == float))
                                                        and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                          or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                          or (Tp2 == float)) ->
    {boolean, [Val1 >= Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '>') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                         or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                         or (Tp1 == float))
                                                       and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                         or (Tp2 == non_neg_integer) or (Tp2 == integer)
                                                         or (Tp2 == float)) ->
    {boolean, [Val1 > Val2]};
compute_infix_expr(_Tp1, _Tp2, Operation) when (Operation == '==') or (Operation == '/=')
									        or (Operation == '=<') or (Operation == '<')
									        or (Operation == '>=') or (Operation == '>')
									        or (Operation == '=:=') or (Operation =='=/=') ->
	{boolean, []};
compute_infix_expr({float, [Val1]}, {Tp2, [Val2]}, '+') when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
	                                                            or (Tp2 == non_neg_integer) or (Tp2 == integer) 
	                                                            or (Tp2 == float) ->
	{float, [Val1 + Val2]};
compute_infix_expr({Tp1, [Val1]}, {float, [Val2]}, '+') when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                            or (Tp1 == non_neg_integer) or (Tp1 == integer) 
	                                                            or (Tp1 == float) ->
	{float, [Val1 + Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '+') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                             or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                               and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                               	 or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 + Val2]};
compute_infix_expr({float, [Val1]}, {Tp2, [Val2]}, '-') when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
	     													     or (Tp2 == non_neg_integer) or (Tp2 == integer) 
	     													     or (Tp2 == float) ->
	{float, [Val1 - Val2]};
compute_infix_expr({Tp1, [Val1]}, {float, [Val2]}, '-') when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
															    or (Tp1 == non_neg_integer) or (Tp1 == integer) 
															    or (Tp1 == float) ->
	{float, [Val1 - Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '-') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                  	 									    or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                              and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                              	or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 - Val2]};

compute_infix_expr({float, [Val1]}, {Tp2, [Val2]}, '*') when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
	                                                            or (Tp2 == non_neg_integer) or (Tp2 == integer) 
	                                                            or (Tp2 == float) ->
	{float, [Val1 * Val2]};
compute_infix_expr({Tp1, [Val1]}, {float, [Val2]}, '*') when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
	    											            or (Tp1 == non_neg_integer) or (Tp1 == integer) 
	    											            or (Tp1 == float) ->
	{float, [Val1 * Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '*') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	      												         or (Tp1 == non_neg_integer) or (Tp1 == integer)) and
														           ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
														         or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 * Val2]};
compute_infix_expr(_Expr1, {_Tp2, [0]}, '/') ->
	{none, []};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, '/') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                             or (Tp1 == non_neg_integer) or (Tp1 == integer) 
	                                                             or (Tp1 == float)) 
                                                               and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                               	 or (Tp2 == non_neg_integer) or (Tp2 == integer) 
                                                               	 or (Tp2 == float)) ->
	{float, [Val1 / Val2]};
compute_infix_expr(_Expr1, {_Tp2, [0]}, 'div') ->
	{none, []};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'div') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
																   or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
																 and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
																   or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 div Val2]};
compute_infix_expr(_Expr1, {_Tp2, [0]}, 'rem') ->
	{none, []};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'rem') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
																   or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                                 and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                                   or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 rem Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'band') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                                or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                 											      and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                 											      	or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 band Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'bor') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                               or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                                 and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                                   or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 bor Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'bxor') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                                or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                                  and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                                  	or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 bxor Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'bsl') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                               or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
                                                                 and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                                   or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 bsl Val2]};
compute_infix_expr({Tp1, [Val1]}, {Tp2, [Val2]}, 'bsr') when ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
	                                                               or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
       												             and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
       												               or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, [Val1 bsr Val2]};
compute_infix_expr({Tp, [Val1]}, {Tp, [Val2]}, 'and') when (Tp == boolean) ->
	{boolean, [Val1 and Val2]};
compute_infix_expr({Tp, [Val1]}, {Tp, [Val2]}, 'or') when (Tp == boolean) ->
	{boolean, [Val1 or Val2]};
compute_infix_expr({Tp, [Val1]}, {Tp, [Val2]}, 'xor') when (Tp == boolean) ->
	{boolean, [Val1 xor Val2]};
compute_infix_expr({Tp1, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == 'and') or (Operation == 'or') 
                                                                 or (Operation == 'xor')) 
                                                               and ((Tp1 == boolean) or (Tp1 == any)) 
                                                               and ((Tp2 == boolean) or (Tp2 == any)) ->
	{boolean, []};

compute_infix_expr({float, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == '+') or (Operation == '-') 
                                                               or (Operation == '*') or (Operation == '/')) 
													         and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
															   or (Tp2 == non_neg_integer) or (Tp2 == integer) 
															   or (Tp2 == float) or (Tp2 == number) 
															   or (Tp2 == any)) ->
	{float, []};
compute_infix_expr({Tp1, _Val1}, {float, _Val2}, Operation) when ((Operation == '+') or (Operation == '-') 
	                                                                 or (Operation == '*') or (Operation == '/')) 
 															       and ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
 															       	 or (Tp1 == non_neg_integer) or (Tp1 == integer) 
 															       	 or (Tp1 == float) or (Tp1 == number) 
 															       	 or (Tp1 == any)) ->
	{float, []};
compute_infix_expr({Tp1, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == '+') or (Operation == '-') 
	      												             or (Operation == '*') or (Operation == '/')) 
																   and ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
																     or (Tp1 == non_neg_integer) or (Tp1 == integer)) 
																   and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
																   	 or (Tp2 == non_neg_integer) or (Tp2 == integer)) ->
	{integer, []};
compute_infix_expr({Tp1, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == '+') or (Operation == '-') 
																	 or (Operation == '*') or (Operation == '/')) 
														           and ((Tp1 == number) or (Tp1 == any)) 
														           and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
														           	 or (Tp2 == non_neg_integer) or (Tp2 == integer) 
														           	 or (Tp2 == float) or (Tp2 == number) 
														           	 or (Tp2 == any)) ->
	{number, []};
compute_infix_expr({Tp1, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == '+') or (Operation == '-') 
																     or (Operation == '*') or (Operation == '/')) 
														           and ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
														           	 or (Tp1 == non_neg_integer) or (Tp1 == integer) 
														           	 or (Tp1 == float) or (Tp1 == number) or (Tp1 == any)) 
														           and ((Tp2 == number) or (Tp2 == any)) ->
	{number, []};
compute_infix_expr({Tp1, _Val1}, {Tp2, _Val2}, Operation) when ((Operation == 'div') or (Operation == 'rem') 
	                                                                 or (Operation == 'band') or (Operation == 'bor') 
	                                                                 or (Operation == 'bxor') or (Operation == 'bsl') 
	                                                                 or (Operation == 'bsr')) 
                                                                   and ((Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                                   	 or (Tp1 == non_neg_integer) or (Tp1 == integer) 
                                                                   	 or (Tp1 == number) or (Tp1 == any)) 
                                                                   and ((Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                                   	 or (Tp2 == non_neg_integer) or (Tp2 == integer) 
                                                                   	 or (Tp2 == number) or (Tp2 == any)) ->
	{integer, []};
compute_infix_expr(_Ls_expr, _Rs_expr, _Operation) ->
	{none, []}.

%---------------------------------Helper functions---------------------------------------------
convert_list_elems_in_basic_format_to_compound([], Converted_values) -> 
	{ungen_list, lists:reverse(Converted_values)};
convert_list_elems_in_basic_format_to_compound([{'...', Val}], Converted_values) ->
	{ungen_list, lists:reverse([{'...', Val} | Converted_values])};
convert_list_elems_in_basic_format_to_compound([H | T], Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),

	case Converted_value of
		{none, []} -> {none, []};
		_          -> convert_list_elems_in_basic_format_to_compound(T, [Converted_value | Converted_values])
	end;
convert_list_elems_in_basic_format_to_compound(Val, Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(Val),

	case Converted_value of
		{none, []} -> {none, []};
		{any, []}  -> {ungen_list, lists:reverse(Converted_values)};
		_          -> Reversed_values = lists:reverse(Converted_values),
	                  {ungen_list, Reversed_values ++ Converted_value}
    end.


convert_tuple_elems_in_basic_format_to_compound([]) -> [];
convert_tuple_elems_in_basic_format_to_compound([H | T]) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),

	case Converted_value of
		{none, []} -> {none, []};
		_          -> [Converted_value | convert_tuple_elems_in_basic_format_to_compound(T)]
	end.

convert_value_in_basic_format_to_compound([]) -> 
	{empty_list, []};
convert_value_in_basic_format_to_compound({Tp, Val}) when (Tp == empty_list) or (Tp == ungen_list)
														   or (Tp == nonempty_list)
														   or (Tp == nonempty_improper_list) or (Tp == maybe_improper_list)
														   or (Tp == nonempty_maybe_improper_list) or (Tp == list)
														   or (Tp == tuple) or (Tp == union) or (Tp == atom)
														   or (Tp == boolean) or (Tp == union)
														   or (Tp == neg_integer) or (Tp == pos_integer)
														   or (Tp == non_neg_integer) or (Tp == integer)
														   or (Tp == float) or (Tp == number) or (Tp == any)
														   or (Tp == pid) or (Tp == {none, []}) -> 
	{Tp, Val};
convert_value_in_basic_format_to_compound({'...', Val}) -> 
	{'...', Val};
convert_value_in_basic_format_to_compound({Tp, []}) ->
	{Tp, []};
convert_value_in_basic_format_to_compound(Val) when is_integer(Val)->
	{integer, [Val]};
convert_value_in_basic_format_to_compound(Val) when is_float(Val) ->
	{float, [Val]};
convert_value_in_basic_format_to_compound(Val) when is_boolean(Val) ->
	{boolean, [Val]};
convert_value_in_basic_format_to_compound(Val) when is_atom(Val) ->
	{atom, [Val]};
convert_value_in_basic_format_to_compound({variable, Val}) ->
	{variable, Val};
convert_value_in_basic_format_to_compound(Val) when is_list(Val) ->
	convert_list_elems_in_basic_format_to_compound(Val, []);
convert_value_in_basic_format_to_compound(Val) when is_tuple(Val) ->
	Tuple_elems_list = tuple_to_list(Val),
	{ungen_tuple, convert_tuple_elems_in_basic_format_to_compound(Tuple_elems_list)}.



get_path(Mod_name) ->
	Mod = ?Query:exec(?Mod:find(Mod_name)),
	File = ?Query:exec(Mod, ?Mod:file()),

	case File of
		[]  -> [];
		[F] -> ?File:path(F)
	end.

get_bodies(Clause) ->
	?Query:exec(Clause, ?Clause:body()).

get_children(Expr) ->
	?Query:exec(Expr, ?Expr:children()).

get_applications(Fun_node) ->
	?Query:exec(Fun_node, ?Fun:applications()).

get_clauses(Fun_def) ->
	?Query:exec(Fun_def, ?Form:clauses()).

get_fundef(Fun_node) ->
	?Query:exec(Fun_node, ?Fun:definition()).

get_patterns(Clause) ->
	?Query:exec(Clause, ?Clause:patterns()).

get_actual_params([]) -> [];
get_actual_params(Application) ->
	Args_list = ?Expr:fun_app_args(Application),
	?Query:exec(Args_list, ?Expr:children()).	

%----------------------------------Defining actual clauses-------------------------------------
find_actual_clauses(Mod_name, Fun_name, Arity, Actual_params) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	Pat_exprs = [get_patterns(Clause) || Clause <- Clauses],
	Guards = obtain_clauses_guards(Clauses),

	case Actual_params of
		[] -> [Clause] = get_clauses(Fun_def),
			  [{Clause, []}];
		_  -> filter_clauses(Pat_exprs, Actual_params, Guards)   
	end.


filter_clauses([], _Pars, []) ->
	[];
filter_clauses([Pat_expr | Pat_exprs], Pars, [Guard | Guards]) ->
	Upd_vars = replace_clause_params_with_args(Pat_expr, Pars, []),
	Pat = obtain_pats_tp(Pat_expr, Upd_vars),
	Is_pars_matched = compare_pat_with_actual_pars(Pat, Pars, true),

	case Is_pars_matched of
		true -> 
                Is_guard_matched = filter_clause_by_guards(Guard, Upd_vars),

                case Is_guard_matched of
                	false    -> filter_clauses(Pat_exprs, Pars, Guards);
                	possibly -> [Clause] = ?Query:exec(hd(Pat_expr), ?Expr:clause()),
                	            [{Clause, Upd_vars} | filter_clauses(Pat_exprs, Pars, Guards)];
                	true     -> [Clause] = ?Query:exec(hd(Pat_expr), ?Expr:clause()),
                				[{Clause, Upd_vars}]
                end;
        possibly -> Is_guard_matched = filter_clause_by_guards(Guard, Upd_vars),

	                case Is_guard_matched of
	                	false    -> filter_clauses(Pat_exprs, Pars, Guards);
	                	_        -> [Clause] = ?Query:exec(hd(Pat_expr), ?Expr:clause()),
	                	            [{Clause, Upd_vars} | filter_clauses(Pat_exprs, Pars, Guards)]
	                end;
	    false    -> filter_clauses(Pat_exprs, Pars, Guards)
	end.

filter_clause_by_guards([], _Vars) ->
	true;
filter_clause_by_guards(Guard, Vars) -> 
	{Is_guard_matched, _Upd_vars} = infer_expr_tp(Guard, Vars, []),

	case Is_guard_matched of
		{boolean, [true]}  -> true;
		{boolean, []}      -> possibly;
		{boolean, [false]} -> false
	end.


compare_pat_with_actual_pars([], [], Status) ->
	Status;
compare_pat_with_actual_pars([Pat_elem | Pat_elems], [Par | Pars], Status) ->
	case are_matching_types(Pat_elem, Par) of
		false    -> false;
		possibly -> compare_pat_with_actual_pars(Pat_elems, Pars, possibly);
		true     -> compare_pat_with_actual_pars(Pat_elems, Pars, Status)
	end.    


obtain_clauses_guards([]) -> [];
obtain_clauses_guards([Clause | Clauses]) ->
	Guards = ?Query:exec(Clause, ?Clause:guard()),

	case Guards of
		[]      -> [[] | obtain_clauses_guards(Clauses)];
		[Guard] -> [Guard | obtain_clauses_guards(Clauses)]
	end.  


obtain_pats_tp([], _Vars) -> [];
obtain_pats_tp([Pat_expr | Pat_exprs], Vars) ->
	{Pat, _Upd_vars} = infer_expr_tp(Pat_expr, Vars, []),	
	[Pat | obtain_pats_tp(Pat_exprs, Vars)].	  


is_union_match({union, []}, _Elem2) ->
	false;
is_union_match({union, [Elem1 | Elems]}, Elem2) ->
	Is_matching = are_matching_types(Elem1, Elem2),
	case Is_matching of
		false       -> is_union_match({union, Elems}, Elem2);
		Is_matching -> Is_matching
	end.


is_ls_union_match_to_rs_union({union, []}, _Union2, Status) ->
	Status;
is_ls_union_match_to_rs_union({union, [Elem1 | Elems1]}, {union, Elems2}, Status) ->
	Is_match = is_union_match({union, Elems2}, Elem1),

	case Is_match of
		false    -> false;
		possibly -> is_ls_union_match_to_rs_union({union, Elems1}, {union, Elems2}, possibly);
		true     -> is_ls_union_match_to_rs_union({union, Elems1}, {union, Elems2}, Status)
	end. 


are_matching_unions(Union1, Union2) ->
	Are_ls_union_match = is_ls_union_match_to_rs_union(Union1, Union2, true),

	case Are_ls_union_match of
		false -> false;
		_     -> is_ls_union_match_to_rs_union(Union2, Union1, Are_ls_union_match)
	end.
	

are_matching_types({any, []}, _Tp2) ->
	possibly;
are_matching_types(_Tp1, {any, []}) ->
	possibly;

are_matching_types({union, Elems1}, {union, Elems2}) ->
	are_matching_unions({union, Elems1}, {union, Elems2});
are_matching_types({union, Elems1}, Elem2) ->
	is_union_match({union, Elems1}, Elem2);
are_matching_types(Elem1, {union, Elems2}) ->
	is_union_match({union, Elems2}, Elem1);


are_matching_types({pid, []}, {pid, []}) ->
	possibly;
are_matching_types({number, _Val1}, {Tp2, _Val2}) when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
												    or (Tp2 == non_neg_integer) or (Tp2 == integer) 
												    or (Tp2 == float) or (Tp2 == number) ->
	possibly;
are_matching_types({Tp1, _Val1}, {number, _Val2}) when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
													or (Tp1 == non_neg_integer) or (Tp1 == integer) 
													or (Tp1 == float) or (Tp1 == number) ->
	possibly;

are_matching_types({Tp1, [Value]}, {Tp2, [Value]}) when (Tp1 == neg_integer)     or (Tp1 == pos_integer) 
                                                     or (Tp1 == non_neg_integer) or (Tp1 == integer)
                                                    and (Tp2 == neg_integer)     or (Tp2 == pos_integer) 
                                                     or (Tp2 == non_neg_integer) or (Tp2 == integer) ->
	true;
are_matching_types({Tp, [Value]}, {Tp, [Value]}) when (Tp == atom)  or (Tp == boolean)
                                                   or (Tp == float) or (Tp == implicit_fun)
                                                   or (Tp == fun_expr) ->
	true;
are_matching_types({neg_integer, [_Value]}, {Tp2, []}) when (Tp2 == neg_integer) or (Tp2 == integer) ->
	possibly;
are_matching_types({pos_integer, [_Value]}, {Tp2, []}) when (Tp2 == pos_integer) or (Tp2 == non_neg_integer) 
														   or (Tp2 == integer) ->
	possibly;
are_matching_types({non_neg_integer, [_Value]}, {Tp2, []}) when (Tp2 == non_neg_integer) or (Tp2 == integer) ->
	possibly;
are_matching_types({integer, [_Value]}, {Tp2, []}) when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                       or (Tp2 == non_neg_integer) or (Tp2 == integer) ->
	possibly;

are_matching_types({Tp1, []}, {neg_integer, [_Value]}) when (Tp1 == neg_integer) or (Tp1 == integer) ->
	possibly;
are_matching_types({Tp1, []}, {pos_integer, [_Value]}) when (Tp1 == pos_integer) or (Tp1 == non_neg_integer) 
                                                           or (Tp1 == integer) ->
	possibly;
are_matching_types({Tp1, []}, {non_neg_integer, [_Value]}) when (Tp1 == non_neg_integer) or (Tp1 == integer) ->
	possibly;
are_matching_types({Tp1, []}, {integer, [_Value]}) when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                                       or (Tp1 == non_neg_integer) or (Tp1 == integer) ->
	possibly;

are_matching_types({neg_integer, [_Value]}, {Tp2, []}) when (Tp2 == neg_integer) or (Tp2 == integer) ->
	possibly;
are_matching_types({pos_integer, [_Value]}, {Tp2, []}) when (Tp2 == pos_integer) or (Tp2 == non_neg_integer) 
                                                           or (Tp2 == integer) ->
	possibly;
are_matching_types({non_neg_integer, [_Value]}, {Tp2, []}) when (Tp2 == non_neg_integer) or (Tp2 == integer) ->
	possibly;
are_matching_types({integer, [_Value]}, {Tp2, []}) when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                                     or (Tp2 == non_neg_integer) or (Tp2 == integer) ->
	possibly;	
are_matching_types({Type, [_Value]}, {Type, []}) when (Type == float) or (Type == atom) 
                                                   or (Type == boolean) or (Type == fun_expr) 
                                                   or (Type == implicit_fun) ->
	possibly;
are_matching_types({Type, []}, {Type, [_Value]}) when (Type == float) or (Type == atom) 
                                                   or (Type == boolean) or (Type == fun_expr) 
                                                   or (Type == implicit_fun)->
	possibly;
are_matching_types({Type, []}, {Type, []}) when (Type == float) or (Type == atom) 
                                             or (Type == boolean) or (Type == fun_expr) 
                                             or (Type == implicit_fun)->
	possibly;
are_matching_types({integer, []}, {Tp2, []}) when (Tp2 == neg_integer) or (Tp2 == pos_integer) 
                                               or (Tp2 == non_neg_integer) or (Tp2 == integer) ->
    possibly;
are_matching_types({Tp1, []}, {integer, []}) when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
                                               or (Tp1 == non_neg_integer) or (Tp1 == integer) ->
    possibly;
are_matching_types({variable, _Value}, _Tp2) ->
	possibly;
are_matching_types(_Tp1, {variable, _Value}) ->
	possibly;

are_matching_types({Lst_tp1, Elems1}, {Lst_tp2, Elems2}) when ((Lst_tp1 == nonempty_list) or (Lst_tp1 == empty_list)
                                                           or (Lst_tp1 == nonempty_improper_list) or (Lst_tp1 == maybe_improper_list)
                                                           or (Lst_tp1 == nonempty_maybe_improper_list) or (Lst_tp1 == list))
                                                          and ((Lst_tp2 == nonempty_list) or (Lst_tp2 == empty_list) 
                                                           or (Lst_tp2 == nonempty_improper_list) or (Lst_tp2 == maybe_improper_list)
                                                           or (Lst_tp2 == nonempty_maybe_improper_list) or (Lst_tp2 == list)) ->
	are_matching_lists({Lst_tp1, Elems1}, {Lst_tp2, Elems2});
are_matching_types({tuple, Elems1}, {tuple, Elems2}) ->
	case length(Elems1) == length(Elems2) of
		true  -> are_matching_tuples({tuple, Elems1}, {tuple, Elems2}, true);
		false -> false
	end;  
are_matching_types(_Tp1, _Tp2) ->
	false.


are_matching_tuples({tuple, []}, {tuple, []}, Status) ->
	Status;
are_matching_tuples({tuple, [Elem1 | Elems1]}, {tuple, [Elem2 | Elems2]}, Status) ->
	Are_matching_elems = are_matching_types(Elem1, Elem2),

	case Are_matching_elems of
		false -> false;
		possibly -> are_matching_tuples({tuple, Elems1}, {tuple, Elems2}, possibly);
		true     -> are_matching_tuples({tuple, Elems1}, {tuple, Elems2}, Status)
	end. 

are_matching_lists({empty_list, []}, {empty_list, []}) ->
	true;
are_matching_lists({empty_list, []}, {Lst2_tp, _Elems}) when (Lst2_tp == list) or (Lst2_tp == maybe_improper_list) ->
	possibly;
are_matching_lists({Lst1_tp, _Elems}, {empty_list, []}) when (Lst1_tp == list) or (Lst1_tp == maybe_improper_list) ->
	possibly;
are_matching_lists({_Lst_tp1, [{any, []}]}, _Lst2) ->
    possibly;
are_matching_lists(_Lst1, {_Lst_tp2, [{any, []}]}) ->
    possibly;
are_matching_lists({Lst_tp1, _Elems1}, {nonempty_improper_list, _Elems2}) when (Lst_tp1 == nonempty_list) or (Lst_tp1 == list) ->
	false;
are_matching_lists({nonempty_improper_list, _Elems1}, {Lst_tp2, _Elems2}) when (Lst_tp2 == nonempty_list) or (Lst_tp2 == list) ->
	false;	
are_matching_lists({_Lst_tp1, [Prop_part1, Improp_part1]}, {_Lst_tp2, [Prop_part2, Improp_part2]}) ->
    Prop_parts_match = are_matching_types(Prop_part1, Prop_part2),
    Improp_parts_match = are_matching_types(Improp_part1, Improp_part2),

    case {Prop_parts_match, Improp_parts_match} of
    	{false, _}   -> false;
    	{_, false}   -> false;
    	{true, true} -> true;
    	_Other       -> possibly
    end;          
are_matching_lists({_Lst_tp1, [Elems1]}, {_Lst_tp2, [Elems2]}) ->
    are_matching_types(Elems1, Elems2).


extract_expr_vals([], Vars, _Call_stack) -> {[], Vars};
extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Vars, Call_stack) ->
	{Left_cons_expr_list, Upd_vars} = extract_expr_val(Left_cons_expr, Vars, Call_stack),
	{Right_cons_expr_list, Upd_vars2} = extract_expr_val(Right_cons_expr, Upd_vars, Call_stack),

	Cons = 
	case Right_cons_expr_list of
		{empty_list, []}    -> Left_cons_expr_list;
		{variable, Value} -> Left_cons_expr_list ++ [{'...', Value}];
		_             -> Left_cons_expr_list ++ Right_cons_expr_list
	end,

	{Cons, Upd_vars2};
extract_expr_vals([Expr | Exprs], Vars, Call_stack) ->
	case ?Expr:type(Expr) of 
		cons   -> {Cons, Upd_vars} = construct_list_from_cons_expr(Expr, Vars, Call_stack),
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars, Call_stack),
				  {[Cons | Vals], Upd_vars2};
		list   -> {Cons, Upd_vars} = construct_list_from_list_expr(Expr, Vars, Call_stack), 
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars, Call_stack),
				  {Cons ++ Vals, Upd_vars2};
		tuple  -> {Tuple, Upd_vars} = construct_tuple(Expr, Vars, Call_stack), 
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars, Call_stack),
				  {[Tuple | Vals], Upd_vars2};
		variable  -> Var_name = ?Expr:value(Expr),
					Var = obtain_var_val(Var_name, Vars),
					{Vals, Upd_vars2} = extract_expr_vals(Exprs, Vars, Call_stack),
		            {[Var | Vals], Upd_vars2};
		_        -> {Gen_expr_tp, Upd_vars} = infer_expr_tp(Expr, Vars, Call_stack), 
					{Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars, Call_stack),
					{[Gen_expr_tp | Vals], Upd_vars2}		
	end.

extract_expr_val(Expr, Vars, Call_stack) ->
	case ?Expr:type(Expr) of
		cons     -> construct_list_from_cons_expr(Expr, Vars, Call_stack);
		list     -> construct_list_from_list_expr(Expr, Vars, Call_stack);
		tuple    -> construct_tuple(Expr, Vars, Call_stack);
		variable -> Var_name = ?Expr:value(Expr),
					{obtain_var_val(Var_name, Vars), Vars};
		_        -> infer_expr_tp(Expr, Vars, Call_stack)
	end.

obtain_var_val(Var_name, Vars) ->
	Var = find_var_by_name(Var_name, Vars),

	case Var of
		{variable, [Var_name]} -> {variable, [Var_name]};
		{Var_name, [Value]}  -> Value
	end.

construct_tuple([], _Vars, _Call_stack) -> [];
construct_tuple(Tuple, Vars, Call_stack) ->
	Children = ?Query:exec(Tuple, ?Expr:children()),
	{Tuple_elems_in_lst, Upd_vars} = extract_expr_vals(Children, Vars, Call_stack),
	{list_to_tuple(Tuple_elems_in_lst), Upd_vars}.


construct_list_from_cons_expr(Cons, Vars, Call_stack) ->
	Children = ?Query:exec(Cons, ?Expr:children()),

	case length(Children) of
		0 -> {{empty_list, []}, Vars};
		1 -> extract_expr_vals(Children, Vars, Call_stack);
		2 -> [Left_cons_expr, Right_cons_expr] = Children,
			 extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Vars, Call_stack)
	end.

construct_list_from_list_expr([], _Vars, _Call_stack) -> [];
construct_list_from_list_expr(L, Vars, Call_stack) ->
	Children = ?Query:exec(L, ?Expr:children()),
	extract_expr_vals(Children, Vars, Call_stack).

%--------------------Extraction of a function specification from the typer result--------------------------------------
improve_typer_res(Mod_name) ->
	Mod_node_in_lst = ?Query:exec(?Mod:find(Mod_name)),

	Mod_node = 
		case Mod_node_in_lst of
			[]    -> [];
			[Res] -> Res 
		end,

	[File_node] = ?Query:exec(Mod_node, ?Mod:file()),
	Path = ?File:path(File_node),
	Spec = os:cmd("typer " ++ [$" | Path] ++ "\""),
	RE = lists:concat(["-spec ", ".+\."]),
	{_, Capture} = re:run(Spec, RE, [global, {capture, all, list}]),
	Specs = extract_matches(Capture),

	improve_all_specs(Specs, Mod_name).


improve_all_specs([], _Mod_name) ->
	[];
improve_all_specs([Spec | Specs], Mod_name) ->
	[improve_single_spec(Spec, Mod_name) | improve_all_specs(Specs, Mod_name)].




improve_single_spec(Spec, Mod_name) ->
	{Fun_name_in_str, Arity, Args_sec, Ret_tp_in_str} = get_fun_info(Spec, []),
	Mod_node = ?Query:exec(?Mod:find(Mod_name)),
	Fun_name = list_to_atom(Fun_name_in_str),
	Spec_node = ?Query:exec(Mod_node, ?Spec:find(Fun_name, Arity)),

	Res = 
		case Spec_node of
			[] -> improve_typer_ret_val(Mod_name, Fun_name, Arity, Args_sec, Ret_tp_in_str);
			_  -> Spec
		end,

	io:fwrite("~p~n", [Res]).


improve_typer_ret_val(Mod_name, Fun_name, Arity, Args_sec, Ret_tp_in_str) ->
	Typer_ret_tp = convert_typer_res_to_cf(Ret_tp_in_str, [], 0),
	
	Improved_ret_tp = 
		case Typer_ret_tp of
			{none, []} -> {none, []};
			_          -> Re_ret_tp = infer_fun_type(Mod_name, Fun_name, Arity, []),
			              case Re_ret_tp of
				              [] -> {none, []};
							  _  -> filter_typer_res(Typer_ret_tp, Re_ret_tp)
						  end
		end,
	Res_in_typer_format = convert_elem_to_tf(Improved_ret_tp),
	"-spec " ++ atom_to_list(Fun_name) ++ Args_sec ++ " -> " ++ Res_in_typer_format ++ ".".


filter_typer_res(Typer_res, {any, []}) ->
	Typer_res;
filter_typer_res({union, Elems1}, {union, Elems2}) ->
	Filtered_elems = filter_elems(Elems1, Elems2, []),

	case length(Filtered_elems) of
		1 -> hd(Filtered_elems);
		_ -> {union, Filtered_elems}
	end;
filter_typer_res({union, Elems1}, {Tp2, Elems2}) ->
	Filtered_elems = filter_elems(Elems1, [{Tp2, Elems2}], []),

	case length(Filtered_elems) of
		1 -> hd(Filtered_elems);
		_ -> {union, Filtered_elems}
	end;
filter_typer_res(Typer_res, Re_res) ->
	Filtered_elems = filter_elems([Typer_res], [Re_res], []),

	case length(Filtered_elems) of
		1 -> hd(Filtered_elems);
		_ -> {union, Filtered_elems}
	end.


filter_elems([], _Referl_res, Filtered_elems) ->
	lists:reverse(Filtered_elems);
filter_elems([{empty_list, []} | Typer_res], Re_res, Filtered_elems) ->
	filter_elems(Typer_res, Re_res, [{empty_list, []} | Filtered_elems]);
filter_elems([{Tp1, [{any, []}]} | Typer_res], Re_res, Filtered_elems) when (Tp1 == nonempty_maybe_improper_list)
												                         or (Tp1 == maybe_improper_list) ->
	filter_elems(Typer_res, Re_res, [{Tp1, [{any, []}]} | Filtered_elems]);
filter_elems([{Typer_lst_tp, Typer_lst_elems} | Typer_res], Re_res, Filtered_elems) when (Typer_lst_tp == nonempty_list) 
                                                                                      or (Typer_lst_tp == list) 
												                                      or (Typer_lst_tp == nonempty_improper_list) 
												                                      or (Typer_lst_tp == nonempty_maybe_improper_list) 
												                                      or (Typer_lst_tp == maybe_improper_list) -> 
    Re_lst = find_lst_among_elems(Re_res),

    case Re_lst of
    	[]                         -> filter_elems(Typer_res, Re_res, [{Typer_lst_tp, Typer_lst_elems} | Filtered_elems]);
    	{Re_lst_tp, Re_lst_elems}  -> case is_exact_subset(Re_lst_elems, Typer_lst_elems) of
					   	                  true  -> filter_elems(Typer_res, Re_res, [{Re_lst_tp, Re_lst_elems} | Filtered_elems]);
					    	              false -> filter_elems(Typer_res, Re_res, [{Typer_lst_tp, Typer_lst_elems} | Filtered_elems])
					                  end
    end;
filter_elems([{tuple, Typer_tuple_elems} | Typer_res], Re_res, Filtered_elems) ->
	Tuple_elems_num = length(Typer_tuple_elems),
	Re_tuple = find_tuple_among_elems(Re_res, Tuple_elems_num),

	case Re_tuple of
		[] -> filter_elems(Typer_res, Re_res, [{tuple, Typer_tuple_elems} | Filtered_elems]);
		_  -> Filtered_tuple = filter_tuple({tuple, Typer_tuple_elems}, Re_tuple, []),
		      filter_elems(Typer_res, Re_res, [Filtered_tuple | Filtered_elems])
    end; 
filter_elems([Elem1 | Elems1], Elems2, Filtered_elems) ->
	case is_subset(Elem1, Elems2) of
		false -> filter_elems(Elems1, Elems2, Filtered_elems);
		_     -> filter_elems(Elems1, Elems2, [Elem1 | Filtered_elems])
	end.


filter_tuple({tuple, []}, {tuple, []}, Filtered_elems) ->
	{tuple, lists:reverse(Filtered_elems)};
filter_tuple({tuple, [Elem1 | Elems1]}, {tuple, [Elem2 | Elems2]}, Filtered_elems) ->
	Filtered_elem = filter_typer_res(Elem1, Elem2),
	filter_tuple({tuple, Elems1}, {tuple, Elems2}, [Filtered_elem | Filtered_elems]).


is_exact_subset([], _Super_set) ->
	true;
is_exact_subset([{union, U_elems1} | Elems1], [{union, U_elems2} | Elems2]) ->
	Is_subset_union = is_subset_union({union, U_elems1}, {union, U_elems2}),

	case Is_subset_union of
		true -> is_exact_subset(Elems1, Elems2);
		_    -> false
	end;
is_exact_subset([Elem | Elems], Super_set) ->
	case is_subset(Elem, Super_set) of
		true -> is_exact_subset(Elems, Super_set);
		_    -> false
	end.


is_subset_union({union, []}, _Supset_union) ->
	true;
is_subset_union({union, [Elem | Elems]}, Supset_union) ->
	Is_match = is_union_match(Supset_union, Elem),

	case Is_match of
		true -> is_subset_union({union, Elems}, Supset_union);
		_    -> false 
	end. 


is_subset(_Elem1, []) ->
	false;
is_subset(Elem1, [Elem2 | Elems2]) ->
	case are_matching_types(Elem1, Elem2) of
		false -> is_subset(Elem1, Elems2);
		Res   -> Res
	end.


%tf - typer format
%cf - compound format
convert_elems_to_tf([]) -> [];
convert_elems_to_tf([Elem | Elems]) ->
	[convert_elem_to_tf(Elem) | convert_elems_to_tf(Elems)].

convert_elem_to_tf({no_return, []}) ->
	"no_return()";
convert_elem_to_tf({Tp, [Val]}) when (Tp == neg_integer)     or (Tp == pos_integer)
                                  or (Tp == non_neg_integer) or (Tp == integer) -> 
    integer_to_list(Val);
convert_elem_to_tf({float, _Val}) ->
	atom_to_list(float) ++ "()";
convert_elem_to_tf({Tp, [Val]}) when (Tp == boolean) or (Tp == atom) ->
	[$' | atom_to_list(Val)] ++ "'";
convert_elem_to_tf({Tp, []}) when (Tp == neg_integer)     or (Tp == pos_integer)
                               or (Tp == non_neg_integer) or (Tp == integer)
                               or (Tp == float)           or (Tp == number)
                               or (Tp == atom)            or (Tp == boolean)
                               or (Tp == pid)             or (Tp == any)
                               or (Tp == none) ->
    atom_to_list(Tp) ++ "()";
convert_elem_to_tf({Tp, Val}) when (Tp == empty_list)                   or (Tp == nonempty_list)
	                            or (Tp == nonempty_improper_list)       or (Tp == maybe_improper_list)
		                        or (Tp == nonempty_maybe_improper_list) or (Tp == list) ->
    convert_lst_to_tf({Tp, Val});
convert_elem_to_tf({tuple, Elems}) ->
	convert_tuple_to_tf({tuple, Elems});
convert_elem_to_tf({union, Elems}) ->
	convert_union_in_cf_to_typer_format(Elems).


convert_union_in_cf_to_typer_format(Elems) ->
	Elems_in_typer_format = convert_elems_to_tf(Elems),
	separate_elems_with_symbol(Elems_in_typer_format, " | ").


convert_tuple_to_tf({undef_tuple, []}) ->
	"tuple()";
convert_tuple_to_tf({tuple, Elems}) ->
	Elems_in_tf = convert_elems_to_tf(Elems),
	Separated_elems = separate_elems_with_symbol(Elems_in_tf, ","),
	[${ | Separated_elems] ++ "}".
	

convert_lst_to_tf({empty_list, []}) ->
	"[]";
convert_lst_to_tf({nonempty_maybe_improper_list, [{any, []}]}) ->
	"nonempty_maybe_improper_list()";
convert_lst_to_tf({maybe_improper_list, [{any, []}]}) ->
	"maybe_improper_list()";
convert_lst_to_tf({nonempty_list, [Elem]}) ->
	Elem_in_tf = convert_elem_to_tf(Elem),
	[$[ | Elem_in_tf] ++ ",...]";
convert_lst_to_tf({list, [Elem]}) ->
	Elem_in_tf = convert_elem_to_tf(Elem),
	[$[ | Elem_in_tf] ++ "]";
convert_lst_to_tf({Lst_tp, [Prop_sec, Improp_sec]}) when (Lst_tp == nonempty_improper_list) 
                                                      or (Lst_tp == nonempty_maybe_improper_list)
                                                      or (Lst_tp == maybe_improper_list) ->
	Conv_prop_sec = convert_elem_to_tf(Prop_sec),
	Conv_improp_sec = convert_elem_to_tf(Improp_sec),
	Lst_tp_in_str = atom_to_list(Lst_tp),
	Lst_tp_in_str ++ "(" ++ Conv_prop_sec ++ "," ++ Conv_improp_sec ++ ")".


separate_elems_with_symbol(Elems, Symbol) ->
	Elems_with_separators = insert_separators(Elems, Symbol),
	lists:concat(Elems_with_separators).


insert_separators([Elem], _Symbol) ->
	[Elem];
insert_separators([Elem | Elems], Symbol) ->
	Separated_elem = Elem ++ Symbol,
	[Separated_elem | insert_separators(Elems, Symbol)].


convert_typer_res_to_cf([], [Elem], _Unions) ->
	Elem;
convert_typer_res_to_cf([32 | T], Elems, Unions) ->
	convert_typer_res_to_cf(T, Elems, Unions);
convert_typer_res_to_cf(Ret_val_str, Elems, Unions) ->
	{Elem, Tail} = convert_composite_elem(Ret_val_str, [], false),
	convert_typer_res_to_cf(Tail, [Elem | Elems], Unions).


convert_composite_elem([], Elems, true) ->
	{{union, lists:reverse(Elems)}, []};
convert_composite_elem([], Elems, false) ->
	{hd(Elems), []};
convert_composite_elem([32 | T], Elems, Is_union) ->
	convert_composite_elem(T, Elems, Is_union);
convert_composite_elem([$) | T], Elems, true) ->
	{{union, lists:reverse(Elems)}, T};
convert_composite_elem([$) | T], Elems, false) ->
	{hd(Elems), T};
convert_composite_elem([$] | T], Elems, true) ->
	{{union, lists:reverse(Elems)}, [$] | T]};
convert_composite_elem([$] | T], Elems, false) ->
	{hd(Elems), [$] | T]};
convert_composite_elem([$} | T], Elems, true) ->
	{{union, lists:reverse(Elems)}, [$} | T]};
convert_composite_elem([$} | T], Elems, false) ->
	{hd(Elems), [$} | T]};
convert_composite_elem([$( | T], Elems, Is_union) ->
	{Elem, Str_after_conv} = convert_composite_elem(T, [], false),
	convert_composite_elem(Str_after_conv, [Elem | Elems], Is_union);
convert_composite_elem([$| | T], Elems, _Is_union) ->
	convert_composite_elem(T, Elems, true);
convert_composite_elem([$, | T], Elems, true) ->
	{{union, lists:reverse(Elems)}, [$, | T]};
convert_composite_elem([$, | T], Elems, false) ->
	{hd(Elems), [$, | T]};
convert_composite_elem(Ret_val_str, Elems, Is_union) ->
	{Elem, Str_after_conv} = convert_single_elem(Ret_val_str),
	convert_composite_elem(Str_after_conv, [Elem | Elems], Is_union).	

convert_single_elem("no_return()" ++ T) ->
	{{no_return, []}, T};
convert_single_elem("none()" ++ T) ->
	{{none, []}, T};
convert_single_elem("neg_integer()" ++ T) ->
	{{neg_integer, []}, T};
convert_single_elem("pos_integer()" ++ T) ->
	{{pos_integer, []}, T};
convert_single_elem("non_neg_integer()" ++ T) ->
	{{non_neg_integer, []}, T};
convert_single_elem("integer()" ++ T) ->
	{{integer, []}, T};
convert_single_elem("float()" ++ T) ->
	{{float, []}, T};
convert_single_elem("number()" ++ T) ->
	{{number, []}, T};
convert_single_elem("atom()" ++ T) ->
	{{atom, []}, T};
convert_single_elem("boolean()" ++ T) ->
	{{boolean, []}, T};
convert_single_elem("'true'" ++ T) ->
	{{boolean, [true]}, T};
convert_single_elem("'false'" ++ T) ->
	{{boolean, [false]}, T};
convert_single_elem("pid()" ++ T) ->
	{{pid, []}, T};
convert_single_elem("any()" ++ T) ->
	{{any, []}, T};
convert_single_elem("_" ++ T) ->
	{{any, []}, T};
convert_single_elem([$' | T]) ->
	convert_atom(T, []);
convert_single_elem("fun" ++ T) ->
	convert_anon_fun(T, []);
convert_single_elem([${ | T]) ->
	convert_tuple(T, []);
convert_single_elem("[]" ++ T) ->
	Lst = {empty_list, []},
	{Lst, T};
convert_single_elem([$[ | T]) ->
	convert_lst(T, []);
convert_single_elem("nonempty_improper_list" ++ T) ->
	convert_lst(T, []);
convert_single_elem("nonempty_maybe_improper_list()" ++ T) ->
	Lst = {nonempty_maybe_improper_list, [{any, []}]},
	{Lst, T};
convert_single_elem("nonempty_maybe_improper_list" ++ T) ->
	{{_, Elems}, Str_after_conv} = convert_lst(T, []),
	Lst = {nonempty_maybe_improper_list, Elems},
	{Lst, Str_after_conv};
convert_single_elem("maybe_improper_list()" ++ T) ->
	Lst = {maybe_improper_list, [{any, []}]},
	{Lst, T};
convert_single_elem("maybe_improper_list" ++ T) ->
	{{_, Elems}, Str_after_conv} = convert_lst(T, []),
	Lst = {maybe_improper_list, Elems},
	{Lst, Str_after_conv};
convert_single_elem([H | T]) when (H >= 48) and (H =< 57) ->
	convert_literal_number(T, [H]).


convert_atom([$' | T], Buf) ->
	Atom_val_in_str = lists:reverse(Buf),
	Atom_val = list_to_atom(Atom_val_in_str),
	Atom = {atom, [Atom_val]},
	{Atom, T};
convert_atom([H | T], Buf) ->
	convert_atom(T, [H | Buf]).


convert_anon_fun([32 | T], Args) ->
	convert_anon_fun(T, Args);
convert_anon_fun([$, | T], Args) ->
	convert_anon_fun(T, Args);
convert_anon_fun([$( | T], Args) ->
	convert_anon_fun(T, Args);
convert_anon_fun("->" ++ T, Args) ->
	{Ret_val, Str_after_conv} = convert_composite_elem(T, [], false),
	Anon_fun = {fun_expr, [Args, Ret_val], []},
	{Anon_fun, Str_after_conv};
convert_anon_fun(Ret_val_str, Args) ->
	{Arg, Str_after_conv} = convert_composite_elem(Ret_val_str, [], false),
	convert_anon_fun(Str_after_conv, [Arg | Args]).


convert_lst([$( | T], Prop_sec) ->
	convert_lst(T, Prop_sec);
convert_lst(",..." ++ T, Prop_sec) ->
	{{nonempty_list, Prop_sec}, tl(T)};
convert_lst([$, | T], Prop_sec) ->
	{Improp_sec, Str_after_conv} = convert_composite_elem(T, [], false),
	Lst = {nonempty_improper_list, Prop_sec ++ [Improp_sec]},
	{Lst, Str_after_conv};
convert_lst([$] | T], Prop_sec) ->
	{{list, Prop_sec}, T};
convert_lst(Ret_val_in_str, Prop_sec) ->
	{Lst_elems, Str_after_conv} = convert_composite_elem(Ret_val_in_str, [], false),
	convert_lst(Str_after_conv, [Lst_elems | Prop_sec]).


convert_tuple([$} | T], Rev_elems) ->
	Tuple_elems = lists:reverse(Rev_elems),
	{{tuple, Tuple_elems}, T};	
convert_tuple([$, | T], Elems) ->
	convert_tuple(T, Elems);
convert_tuple(Ret_val_in_str, Elems) ->
	{Tuple_elem, Str_after_conv} = convert_composite_elem(Ret_val_in_str, [], false),
	convert_tuple(Str_after_conv, [Tuple_elem | Elems]).


convert_literal_number([H | T], Buf) when (H >= 48) and (H =< 57) ->
	convert_literal_number(T, [H | Buf]);
convert_literal_number(T, Buf) ->
	Number_in_str = lists:reverse(Buf),
	Number = list_to_integer(Number_in_str),

	Number_in_cf = 
		if
			Number  < 0 -> {neg_integer, [Number]};
			Number == 0 -> {non_neg_integer, [Number]};
			Number  > 0 -> {pos_integer, [Number]}
		end,
	{Number_in_cf, T}.


filter_ret_val([$>, 32 | T]) ->
	lists:droplast(T);
filter_ret_val([_ | T]) ->
	filter_ret_val(T).


extract_matches([]) -> [];
extract_matches([H | T]) ->
	[hd(H) | extract_matches(T)]. 

get_fun_node(Mod_name, Fun_name, Arity) ->
	[Mod] = ?Query:exec(?Mod:find(Mod_name)),
	?Query:exec(Mod, ?Mod:local(Fun_name, Arity)).


get_fun_info([32 | T], Fun_name) ->
	get_fun_info(T, Fun_name);
get_fun_info([$-, $s, $p, $e, $c, 32 | T], Fun_name) ->
	get_fun_info(T, Fun_name);
get_fun_info([$( | T], Rev_fun_name) ->
	Fun_name = lists:reverse(Rev_fun_name),
	{Arity, Args_sec, Ret_val_sec} = compute_arity_args_ret_tp([$( | T], 0, 0, 0, 0, 0, []),
	Filtered_ret_val = filter_ret_val(Ret_val_sec),
	{Fun_name, Arity, Args_sec, Filtered_ret_val};
get_fun_info([H | T], Fun_name) ->
	get_fun_info(T, [H | Fun_name]).

get_arity(Spec) ->
	compute_arity_args_ret_tp(Spec, 0, 0, 0, 0, 0, []).


compute_arity_args_ret_tp([$, | T], 0, 0, 1, 0, Arity, Args) ->
	compute_arity_args_ret_tp(T, 0, 0, 1, 0, Arity + 1, [$, | Args]);
compute_arity_args_ret_tp([$[ | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List + 1, Tupple, Fun, Binary, Arity, [$[ | Args]);
compute_arity_args_ret_tp([$] | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List - 1, Tupple, Fun, Binary, Arity, [$] | Args]);
compute_arity_args_ret_tp([${ | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple + 1, Fun, Binary, Arity, [${ | Args]);
compute_arity_args_ret_tp([$} | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple - 1, Fun, Binary, Arity, [$} | Args]);
compute_arity_args_ret_tp([$( | T], List, Tupple, 0, Binary, _, Args) ->
	Next_elem = hd(T),

	case Next_elem of
		$) -> Args_sec = lists:reverse([$), $( | Args]),
              {0, Args_sec, tl(T)};
		_  -> compute_arity_args_ret_tp(T, List, Tupple, 1, Binary, 1, [$( | Args])
	end;
compute_arity_args_ret_tp([$( | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple, Fun + 1, Binary, Arity, [$( | Args]);
compute_arity_args_ret_tp([$) | T], List, Tupple, Fun, Binary, Arity, Args) ->
	case Fun of
		1 -> Args_sec = lists:reverse([$) | Args]),
		     {Arity, Args_sec, T};
		_ -> compute_arity_args_ret_tp(T, List, Tupple, Fun - 1, Binary, Arity, [$) | Args])
	end;
compute_arity_args_ret_tp([$<, $< | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple, Fun, Binary + 1, Arity, [$<, $< | Args]);
compute_arity_args_ret_tp([$>, $> | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple, Fun, Binary - 1, Arity, [$>, $> | Args]);
compute_arity_args_ret_tp([H | T], List, Tupple, Fun, Binary, Arity, Args) ->
	compute_arity_args_ret_tp(T, List, Tupple, Fun, Binary, Arity, [H | Args]).

	
%----------------------------Tests------------------------------------------------------------------------
test() ->
%	Test1 = infer_fun_type(unit_test, af1, 0, []),
%	erlang:display({test1, af1, Test1 == [{integer, [305]}]}),

%	Test2 = infer_fun_type(unit_test, af2, 0, []),
%	erlang:display({test2, af2, Test2 == [{integer, [7]}]}),

%	Test3 = infer_fun_type(unit_test, af3, 0, []),
%	erlang:display({test3, af3, Test3 == [{integer, [3]}]}),

%	Test4 = infer_fun_type(unit_test, af3_2, 0, []),
%	erlang:display({test4, af3_2, Test4 == [{integer, [3]}]}),

%	Test5 = infer_fun_type(unit_test, af3_3, 0, []),
%	erlang:display({test5, af3_3, Test5 == [{number,[]}]}),

%	Test6 = infer_fun_type(unit_test, af4_2, 0, []),
%	erlang:display({test6, af4_2, Test6 == [{integer, [3]}]}),

	Test7 = infer_fun_type(unit_test, lfac_2, 0, []),
	erlang:display({test7, lfac_2, Test7 == {union,[{integer,[1]},{integer,[2]}]}}),

	Test8 = infer_fun_type(unit_test, lfac2_2, 0, []),
	erlang:display({test8, lfac2_2, Test8 == {atom,[ok]}}),

	Test9 = infer_fun_type(unit_test, lfac3_3, 1, []),
	erlang:display({test9, lfac3_3, Test9 == {atom,[ok]}}),

	Test10 = infer_fun_type(unit_test, lfac4_4, 0, []),
	erlang:display({test10, lfac4_4, Test10 == {atom,[ok]}}),

	Test11 = infer_fun_type(unit_test, lfac5_5, 0, []),
	erlang:display({test11, lfac5_5, Test11 == {atom,[ok]}}),

	Test12 = infer_fun_type(unit_test, lfac7_7, 0, []),
	erlang:display({test12, lfac7_7, Test12 == {atom,[ok]}}),

	Test13 = infer_fun_type(unit_test, ei1, 0, []),
	erlang:display({test13, ei1, Test13 == {nonempty_list,[{union,[{integer,[1]},{integer,[2]},{integer,[4]}]}]}}),

	Test14 = infer_fun_type(unit_test, ei2, 0, []),
	erlang:display({test14, ei2, Test14 == {nonempty_list,[{union,[{integer,[1]},{integer,[2]},{nonempty_list,[{union,[{integer,[1]},{integer,[2]},{integer,[3]}]}]}]}]}}),

	Test15 = infer_fun_type(unit_test, ei3, 0, []),
	erlang:display({test15, ei3, Test15 == {tuple,[{nonempty_list,[{union,[{integer,[1]},{integer,[2]}]}]},{nonempty_list,[{union,[{integer,[3]},{integer,[4]}]}]}]}}),

	Test16 = infer_fun_type(unit_test, ei4, 0, []),
	erlang:display({test16, ei4, Test16 == {nonempty_list,[{union,[{integer,[1]},{integer,[2]}]}]}}),

	Test17 = infer_fun_type(unit_test, ei5, 0, []),
	erlang:display({test17, ei5, Test17 == {nonempty_improper_list,[{integer,[1]},{integer,[2]}]}}),

	Test18 = infer_fun_type(unit_test, ei6, 1, []),
	erlang:display({test18, ei6, Test18 == {nonempty_maybe_improper_list,[{any, []}]}}),

	%Test19 = infer_fun_type(unit_test, pm, 0, []),
	%erlang:display({test19, pm, Test19 == [{integer,[3]}]}),

	%Test20 = infer_fun_type(unit_test, pm2, 0, []),
	%erlang:display({test20, pm2, Test20 == [{defined_list,[{integer,[1]},{integer,[2]}]}]}),

	%Generalization

	%Numbers

	T21 = c([1, {number, []}]),
	Test21 = g(T21),
	erlang:display({test21, Test21 == {nonempty_list, [{number, []}]}}),

	T22 = c([1, {number, []}]),
	Test22 = g(T22),
	erlang:display({test22, Test22 == {nonempty_list, [{number, []}]}}),

	T23 = c([1,2,3]),
	Test23 = g(T23),
	erlang:display({test23, Test23 == {nonempty_list,[{union,[{integer,[1]},
                         {integer,[2]},
                         {integer,[3]}]}]}}),

	T24 = c([1,2,3.5]),
	Test24 = g(T24),
	erlang:display({test24, Test24 == {nonempty_list, [{number, []}]}}),

	T25 = c([1.1, 1.2, 3]),
	Test25 = g(T25),
	erlang:display({test25, Test25 == {nonempty_list, [{number, []}]}}),

	%Booleans
	T26 = c([true, false]),
	Test26 = g(T26),
	erlang:display({test26, Test26 == {nonempty_list, [{boolean, []}]}}),

	T27 = c([false, false]),
	Test27 = g(T27),
	erlang:display({test27, Test27 == {nonempty_list, [{boolean, [false]}]}}),

	T28 = c([true, true]),
	Test28 = g(T28),
	erlang:display({test28, Test28 == {nonempty_list, [{boolean, [true]}]}}),

	T29 = c([{boolean, []}, true]),
	Test29 = g(T29),
	erlang:display({test29, Test29 == {nonempty_list, [{boolean, []}]}}),

	T30 = c([ok, error]),
	Test30 = g(T30),	
	erlang:display({test30, Test30 == {nonempty_list, [{union, [{atom, [ok]}, {atom, [error]}]}]}}),

	T31 = c([1,2, []]),
	Test31 = g(T31),
	erlang:display({test31, Test31 == {nonempty_list,[{union,[
						 {integer,[1]},
                         {integer,[2]},
                         {empty_list, []}
                    ]}]}}),

	T32 = c([[1,2,3], [ok, error]]),
	Test32 = g(T32),
	erlang:display({test32, Test32 == {nonempty_list,
									    [{nonempty_list,
									         [{union,
									              [{integer,[1]},
									               {integer,[2]},
									               {integer,[3]},
									               {atom,[ok]},
									               {atom,[error]}]}]}]}}),

	T33 = c([[1,2,3], [ok, true], []]),
	Test33 = g(T33),	
	erlang:display({test33, Test33 == {nonempty_list,
										[{list,
											[{union,[{boolean,[true]},{integer,[1]},{integer,[2]},{integer,[3]},{atom,[ok]}]}]}]}}),

	T34 = c([[1,2 | 3], [4,5 | 6]]),
	Test34 = g(T34),	
	erlang:display({test34, Test34 == {nonempty_list,
									    [{nonempty_improper_list,
									         [{union,
									              [{integer,[1]},{integer,[2]},{integer,[4]},{integer,[5]}]},
									          {union,[{integer,[6]},{integer,[3]}]}]}]}}),


	T35 = c([[1,2 | 3], [4,5 | 6] | 7]),
	Test35 = g(T35),	
	erlang:display({test35, Test35 == {nonempty_improper_list,
									    [{nonempty_improper_list,
									         [{union,
									              [{integer,[1]},{integer,[2]},{integer,[4]},{integer,[5]}]},
									          {union,[{integer,[6]},{integer,[3]}]}]},
									     {integer,[7]}]}}),

	T36 = c([[1,2 | 3], [4,5, 6] | 7]),
	Test36 = g(T36),	
	erlang:display({test36, Test36 == {nonempty_improper_list,
									    [{nonempty_maybe_improper_list,
									         [{union,
									              [{integer,[1]},
									               {integer,[2]},
									               {integer,[4]},
									               {integer,[5]},
									               {integer,[6]}]},
									          {union,[{empty_list,[]},{integer,[3]}]}]},
									     {integer,[7]}]}}),

	T37 = c([[1,2 | 3], [4,5, 6], [] | 7]),
	Test37 = g(T37),	
	erlang:display({test37, Test37 == {nonempty_improper_list,
									    [{maybe_improper_list,
									         [{union,
									              [{integer,[1]},
									               {integer,[2]},
									               {integer,[4]},
									               {integer,[5]},
									               {integer,[6]}]},
									          {union,[{empty_list,[]},{integer,[3]}]}]},
									     {integer,[7]}]}}),

	T38 = c([[1,2, {'...', ["A"]}], [3,4], ok]),
	Test38 = g(T38),	
	erlang:display({test38, Test38 == {nonempty_list,[{union,[{atom,[ok]},
                         				{nonempty_maybe_improper_list,[{any, []}]}]}]}}),

	T39 = c([ok, [1,2], {a, b}, {[c, d], {1, 2}}, {true,false, daa}]),
	Test39 = g(T39),	
	erlang:display({test39, Test39 == {nonempty_list,
				    [{union,
				         [{atom,[ok]},
				          {nonempty_list,[{union,[{integer,[1]},{integer,[2]}]}]},
				          {tuple,
				              [{union,
				                   [{atom,[a]},
				                    {nonempty_list,[{union,[{atom,[c]},{atom,[d]}]}]}]},
				               {union,[{atom,[b]},{tuple,[{integer,[1]},{integer,[2]}]}]}]},
				          {tuple,
				              [{boolean,[true]},{boolean,[false]},{atom,[daa]}]}]}]}}),

	T40 = c([{{1,2}, {3,4}, {5,6,7}}]),
	Test40 = g(T40),	
	erlang:display({test40, Test40 == {nonempty_list,[{tuple,[{tuple,[{integer,[1]},
		                                 {integer,[2]}]},
		                         {tuple,[{integer,[3]},{integer,[4]}]},
		                         {tuple,[{integer,[5]},
		                                 {integer,[6]},
		                                 {integer,[7]}]}]}]}}),

	T41 = c([{2,3,{variable, ["A"]}}, {2,3}, {ok, at, true}]),
	Test41 = g(T41),	
	erlang:display({test41, Test41 == {nonempty_list,
							    [{union,
							         [{tuple,
							              [{union,[{integer,[2]},{atom,[ok]}]},
							               {union,[{integer,[3]},{atom,[at]}]},
							               {any,[]}]},
							          {tuple,[{integer,[2]},{integer,[3]}]}]}]}}),

	T42 = c([1, {ok, true}, {da, net}, [lol, lool] | {3,4,5}]),
	Test42 = g(T42),	
	erlang:display({test42, Test42 == {nonempty_improper_list,
									    [{union,
									         [{integer,[1]},
									          {nonempty_list,[{union,[{atom,[lol]},{atom,[lool]}]}]},
									          {tuple,
									              [{union,[{atom,[ok]},{atom,[da]}]},
									               {union,[{boolean,[true]},{atom,[net]}]}]}]},
									     {tuple,[{integer,[3]},{integer,[4]},{integer,[5]}]}]}}),

	A43 = refined_genspec:c([1,2]),
	B43 = refined_genspec:g(A43),
	C43 = refined_genspec:c([B43, [2,3,4,5]]),
	Test43 = refined_genspec:g(C43),
	erlang:display({test43, Test43 == {nonempty_list,
									    [{nonempty_list,
									         [{union,
									              [{integer,[1]},
									               {integer,[2]},
									               {integer,[3]},
									               {integer,[4]},
									               {integer,[5]}]}]}]}}),

	A44 = refined_genspec:c([1]),
	B44 = refined_genspec:g(A44),
	C44 = refined_genspec:c([[2,3,4,5], B44]),
	Test44 = refined_genspec:g(C44),
	erlang:display({test44, Test44 == {nonempty_list,
									    [{nonempty_list,
									         [{union,
									              [{integer,[2]},
									               {integer,[3]},
									               {integer,[4]},
									               {integer,[5]},
									               {integer,[1]}]}]}]}}),

	A45 = refined_genspec:c([ok, true | 1]),
	B45 = refined_genspec:g(A45),
	C45 = refined_genspec:c([[2,3,4], B45]),
	Test45 = refined_genspec:g(C45),
	erlang:display({test45, Test45 == {nonempty_list,
										    [{nonempty_maybe_improper_list,
										         [{union,
										              [{boolean,[true]},
										               {integer,[2]},
										               {integer,[3]},
										               {integer,[4]},
										               {atom,[ok]}]},
										          {union,[{integer,[1]},{empty_list,[]}]}]}]}}),
	A46 = refined_genspec:c([[ok | 1], [ok | 2]]),
	B46 = refined_genspec:g(A46),
	C46 = refined_genspec:c([[[2,3,4]], B46]),
	Test46 = refined_genspec:g(C46),
	erlang:display({test46, Test46 == {nonempty_list,
									    [{nonempty_list,
									         [{nonempty_maybe_improper_list,
									              [{union,
									                   [{integer,[2]},{integer,[3]},{integer,[4]},{atom,[ok]}]},
									               {union,[{integer,[1]},{integer,[2]},{empty_list,[]}]}]}]}]}}),

	A47 = refined_genspec:c([[true, false, error | 1], [ok | 2]]),
	B47 = refined_genspec:g(A47),
	C47 = refined_genspec:c([[[2,3,4]], B47]),
	Test47 = refined_genspec:g(C47),
	erlang:display({test47, Test47 == {nonempty_list,
									    [{nonempty_list,
									         [{nonempty_maybe_improper_list,
									              [{union,
									                   [{boolean,[]},
									                    {integer,[2]},
									                    {integer,[3]},
									                    {integer,[4]},
									                    {atom,[error]},
									                    {atom,[ok]}]},
									               {union,[{integer,[1]},{integer,[2]},{empty_list,[]}]}]}]}]}}),

	A48 = refined_genspec:c([[true, false, {number, []} | 1], [ok | 1]]),
	B48 = refined_genspec:g(A48),
	C48 = refined_genspec:c([[[2,3,4]], B48]),
	Test48 = refined_genspec:g(C48),
	erlang:display({test48, Test48 == {nonempty_list,
									    [{nonempty_list,
									         [{nonempty_maybe_improper_list,
									              [{union,[{boolean,[]},{number,[]},{atom,[ok]}]},
									               {union,[{integer,[1]},{empty_list,[]}]}]}]}]}}),

	A49 = refined_genspec:c([1 | 2]),
	B49 = refined_genspec:g(A49),
	C49 = refined_genspec:c([[3 | 4], B49]),
	Test49 = refined_genspec:g(C49),
	erlang:display({test49, Test49 == {nonempty_list,
									    [{nonempty_improper_list,
									         [{union,[{integer,[3]},{integer,[1]}]},
									          {union,[{integer,[2]},{integer,[4]}]}]}]}}),

	A50 = refined_genspec:c([[1,2 | 3], [[4,5,6], []] | 7]),
	B50 = refined_genspec:g(A50),
	C50 = refined_genspec:c([[er, da | ok], B50]),
	Test50 = refined_genspec:g(C50),
	erlang:display({test50, Test50 == {nonempty_list,
									    [{nonempty_improper_list,
									         [{union,
									              [{atom,[er]},
									               {atom,[da]},
									               {nonempty_maybe_improper_list, 
									                   [{union,
									                        [{integer,[1]},
									                         {integer,[2]},
									                         {list,
									                             [{union,
									                                  [{integer,[4]},
									                                   {integer,[5]},
									                                   {integer,[6]}]}]}]},
									                    {union,[{integer,[3]},{empty_list,[]}]}]}]},
									          {union,[{integer,[7]},{atom,[ok]}]}]}]}}),

	A51 = refined_genspec:c([[{variable, ["A"]} | 1], [2,3 | 4]]),
	B51 = refined_genspec:g(A51),
	C51 = refined_genspec:c([[[5,6 | 7]], B51]),
	Test51 = refined_genspec:g(C51),
	%erlang:display(Test51),
	erlang:display({test51, Test51 == {nonempty_list,
									    [{nonempty_list,
									         [{nonempty_improper_list,
									              [{any,[]},
									               {union,[{integer,[1]},{integer,[4]},{integer,[7]}]}]}]}]}}),
	A52 = c([1,2]),
	B52 = c([3,4,5 | A52]),
	Test52 = g(B52),
	erlang:display({test52, Test52 == {nonempty_list,[{union,[{integer,[3]},
				                        {integer,[4]},
				                        {integer,[5]},
				                        {integer,[1]},
				                        {integer,[2]}]}]}}),

	A53 = c([1,2,{'...', ["A"]}]),
	B53 = c([3,4 | A53]),
	Test53 = g(B53),
	erlang:display({test53, Test53 == {nonempty_maybe_improper_list, [{any, []}]}}),

	A54 = c([1,2 | 3]),
	B54 = c([4,5 | A54]),
	Test54 = g(B54),
	erlang:display({test54, Test54 == {nonempty_improper_list,[{union,[{integer,[4]},
		                                 {integer,[5]},
		                                 {integer,[1]},
		                                 {integer,[2]}]},
		                         			{integer,[3]}]}}),

	A55 = c([[1,2],[ok, error]]),
	B55 = c([[3,4] | A55]),
	Test55 = g(B55),
	erlang:display({test55, Test55 == {nonempty_list,
									    [{nonempty_list,
									         [{union,
									              [{integer,[3]},
									               {integer,[4]},
									               {integer,[1]},
									               {integer,[2]},
									               {atom,[ok]},
									               {atom,[error]}]}]}]}}),

	A56 = refined_genspec:c([1,2,3]),
	B56 = refined_genspec:g(A56),
	C56 = refined_genspec:c([5,6 | B56]),
	Test56 = refined_genspec:g(C56),
	erlang:display({test56, Test56 == {nonempty_list,[{union,[{integer,[5]},
				                        {integer,[6]},
				                        {integer,[1]},
				                        {integer,[2]},
				                        {integer,[3]}]}]}}),

	A57 = refined_genspec:c([1,2 | 3]),
	B57 = refined_genspec:g(A57),
	C57 = refined_genspec:c([4,5 | B57]),
	Test57 = refined_genspec:g(C57),
	erlang:display({test57, Test57 == {nonempty_improper_list,[{union,[{integer,[4]},
		                                 {integer,[5]},
		                                 {integer,[1]},
		                                 {integer,[2]}]},
		                         {integer,[3]}]}}),

	A58 = refined_genspec:c([1,2]),
	B58 = refined_genspec:g(A58),
	C58 = refined_genspec:c([[3,4] | B58]),
	Test58 = refined_genspec:g(C58),
	erlang:display({test58, Test58 == {nonempty_list,
									    [{union,
									         [{integer,[1]},
									          {integer,[2]},
									          {nonempty_list,[{union,[{integer,[3]},{integer,[4]}]}]}]}]}}),

	A59 = refined_genspec:c([1,2 | 3]),
	B59 = refined_genspec:g(A59),
	C59 = refined_genspec:c([[3,4] | B59]),
	Test59 = refined_genspec:g(C59),
	erlang:display({test59, Test59 == {nonempty_improper_list,
									    [{union,
									         [{integer,[1]},
									          {integer,[2]},
									          {nonempty_list,[{union,[{integer,[3]},{integer,[4]}]}]}]},
									     {integer,[3]}]}}),

	A60 = refined_genspec:c([1,2,{'...', ["A"]}]),
	B60 = refined_genspec:g(A60),
	C60 = refined_genspec:c([[3,4] | B60]),
	Test60 = refined_genspec:g(C60),
	erlang:display({test60, Test60 == {nonempty_maybe_improper_list, [{any, []}]}}),

	T61 = c([he | to]),
	A61 = c([[[ok, true, false], da, [kak, tak | T61]] | 7]),
	T61_1 = c([su | do]),
	T61_2 = g(T61_1),
	C61 = c([3, [4,su | T61_2] | A61]),
	Test61 = g(C61),
	erlang:display({test61, Test61 == {nonempty_improper_list,
									    [{union,
									         [{integer,[3]},
									          {nonempty_maybe_improper_list,
									              [{union,
									                   [{integer,[4]},
									                    {atom,[su]},
									                    {atom,[da]},
									                    {nonempty_maybe_improper_list,
									                        [{union,
									                             [{boolean,[]},
									                              {atom,[ok]},
									                              {atom,[kak]},
									                              {atom,[tak]},
									                              {atom,[he]}]},
									                         {union,[{atom,[to]},{empty_list,[]}]}]}]},
									               {union,[{empty_list,[]},{atom,[do]}]}]}]},
									     {integer,[7]}]}}),

	Gen_tuple = {union,[{tuple,[{union,[{integer,[1]},{integer,[3]}]},
                {union,[{integer,[2]},{integer,[4]}]}]},
        {tuple,[{integer,[5]},{integer,[6]},{integer,[7]}]}]},

    A62 = c([1,2,Gen_tuple]),
    Test62 = g(A62),
	erlang:display({test62, Test62 == {nonempty_list,[{union,[{integer,[1]},
				                        {integer,[2]},
				                        {tuple,[{union,[{integer,[1]},{integer,[3]}]},
				                                {union,[{integer,[2]},{integer,[4]}]}]},
				                        {tuple,[{integer,[5]},
				                                {integer,[6]},
				                                {integer,[7]}]}]}]}}),

	A63 = c([1,2 | Gen_tuple]),
    Test63 = g(A63),
	erlang:display({test63, Test63 == {nonempty_improper_list,
									    [{union,[{integer,[1]},{integer,[2]}]},
									     {union,
									         [{tuple,
									              [{union,[{integer,[1]},{integer,[3]}]},
									               {union,[{integer,[2]},{integer,[4]}]}]},
									          {tuple,[{integer,[5]},{integer,[6]},{integer,[7]}]}]}]}}),

	A64 = c([{ok, error}, Gen_tuple]),
    Test64 = g(A64),
	erlang:display({test64, Test64 == {nonempty_list,
									    [{union,
									         [{tuple,
									              [{union,[{integer,[1]},{integer,[3]},{atom,[ok]}]},
									               {union,[{integer,[2]},{integer,[4]},{atom,[error]}]}]},
									          {tuple,[{integer,[5]},{integer,[6]},{integer,[7]}]}]}]}}),

	Test65 = infer_fun_type(unit_test, cons_bound, 1, []),
	erlang:display({test65, cons_bound, Test65 == {any, []}}),

	Test66 = infer_fun_type(unit_test, cons_bound2, 1, []),
	erlang:display({test66, cons_bound2, Test66 == {any, []}}),

	Test67 = infer_fun_type(unit_test, cons_bound3, 1, []),
	erlang:display({test67, cons_bound3, Test67 == {number, []}}),

	Test68 = infer_fun_type(unit_test, cons_bound4, 0, []),
	erlang:display({test68, cons_bound4, Test68 == {integer, [2]}}),

	Test69 = infer_fun_type(unit_test, cons_bound5, 0, []),
	erlang:display({test69, cons_bound5, Test69 == {integer, [87]}}),

	Test70 = infer_fun_type(unit_test, cons_bound6, 0, []),
	erlang:display({test70, cons_bound6, Test70 == {union,[{nonempty_improper_list,[{union,[{integer,[1]},{integer,[2]}]},{integer,[3]}]},{integer,[3]}]}}),

	Test71 = infer_fun_type(unit_test, cons_bound7, 0, []),
	erlang:display({test71, cons_bound7, Test71 == {list,[{union,[{integer,[1]},
										                {integer,[2]},
										                {integer,[3]}]}]}}),

	Test72 = infer_fun_type(unit_test, cons_bound8, 0, []),
	erlang:display({test72, cons_bound8, Test72 == {union,[{integer,[1]},{integer,[2]}]}}),

	Test77 = infer_fun_type(unit_test, cons_bound9, 0, []),
	erlang:display({test77, cons_bound9, Test77 == {tuple,[{integer,[1]},{integer,[2]},{integer,[3]}]}}),

%Tuple bound

	Test73 = infer_fun_type(unit_test, tuple_bound, 0, []),
	erlang:display({test73, tuple_bound, Test73 == {integer,[1]}}),

	Test74 = infer_fun_type(unit_test, tuple_bound2, 0, []),
	erlang:display({test74, tuple_bound2, Test74 == {integer,[1]}}),

	Test75 = infer_fun_type(unit_test, tuple_bound3, 0, []),
	erlang:display({test75, tuple_bound3, Test75 == {tuple,[{integer,[4]},{integer,[5]}]}}),

	Test76 = infer_fun_type(unit_test, tuple_bound4, 1, []),
	erlang:display({test76, tuple_bound4, Test76 == {tuple,[{any,[]},{integer,[5]}]}}),

	Test78 = infer_fun_type(unit_test, match_expr, 1, []),
	erlang:display({test78, match_expr, Test78 == {integer,[4]}}),

	Test79 = infer_fun_type(unit_test, cons_bound10, 0, []),
	erlang:display({test79, cons_bound10, Test79 == {tuple,[{integer,[3]},{integer,[4]},{integer,[5]}]}}),

	Test80 = infer_fun_type(unit_test, cl_mat, 0, []),
	erlang:display({test80, cl_mat, Test80 == {atom,[horoso]}}),

	Test81 = infer_fun_type(unit_test, cl_mat2, 1, []),
	erlang:display({test81, cl_mat2, Test81 == {atom,[eror]}}),

	Test82 = infer_fun_type(unit_test, cl_mat3, 1, []),
	erlang:display({test82, cl_mat3, Test82 == {atom,[ok]}}).



g(List) -> 
	{Res, _} = generalize_lst(List, ?ELEMS_TBL),
	Res.

c(Value) ->
	convert_value_in_basic_format_to_compound(Value).

u([Elem | Elems]) ->
	{_lst_tp, Elems_in_cf} = c([Elem | Elems]),
	{Res, _} = generalize_elems(Elems_in_cf, []),
	Res;
u(Elem) ->
	Elem_in_cf = c(Elem),
	{Res, _} = generalize_elems([Elem_in_cf], []),
	Res.

m(A, B) ->
	A_in_cf = u(A),
	B_in_cf = u(B),
	%erlang:display(A_in_cf),
	%erlang:display(B_in_cf),
	are_matching_types(A_in_cf, B_in_cf).

t(Tuple) ->
	A = c(Tuple),
	generalize_tuple(A).

i(Mod_name, Fun_name, Arity) ->
	infer_fun_type(Mod_name, Fun_name, Arity, []).

itr(Mod_name) ->
	improve_typer_res(Mod_name).

ge(Elems) ->
	{Gen_elems, _Upd_elems_tbl} = generalize_elems(Elems, []),
	Gen_elems.



infer_fun_types_for_testing([], _Mod_name) ->
	[];
infer_fun_types_for_testing([Spec | Specs], Mod_name) ->
	[infer_one_fun(Spec, Mod_name) | infer_fun_types_for_testing(Specs, Mod_name)].


infer_one_fun(Spec, Mod_name) ->
	{Fun_name_in_str, Arity, Args_sec, _Ret_tp_in_str} = get_fun_info(Spec, []),
	Mod_node = ?Query:exec(?Mod:find(Mod_name)),
	Fun_name = list_to_atom(Fun_name_in_str),

	Fun_tp = infer_fun_type(Mod_name, Fun_name, Arity, []),
	Res_in_typer_format = convert_elem_to_tf(Fun_tp),
	Res = "-spec " ++ atom_to_list(Fun_name) ++ Args_sec ++ " -> " ++ Res_in_typer_format ++ ".",
	io:fwrite("~p~n", [Res]).

start_testing(Mod_name) ->
	Mod_node_in_lst = ?Query:exec(?Mod:find(Mod_name)),

	Mod_node = 
		case Mod_node_in_lst of
			[]    -> [];
			[Res] -> Res 
		end,

	[File_node] = ?Query:exec(Mod_node, ?Mod:file()),
	Path = ?File:path(File_node),
	Spec = os:cmd("typer " ++ [$" | Path] ++ "\""),
	RE = lists:concat(["-spec ", ".+\."]),
	{_, Capture} = re:run(Spec, RE, [global, {capture, all, list}]),
	Specs = extract_matches(Capture),

	infer_fun_types_for_testing(Specs, Mod_name).


%--------------------------------Testing------------------------------------------
print_expr_val(Expr) ->
	Actual_vals = extract_expr_vals([Expr], [], []),

	case ?Expr:type() of
		tuple -> erlang:list_to_tuple(Actual_vals);
		_     -> Actual_vals
	end.

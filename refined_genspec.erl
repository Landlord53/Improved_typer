-module(refined_genspec).

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
-define(IMPROPER_ELEMS_SEC_INDEX, 7). 
-define(UNION_INDEX, 8).

-define(ELEMS_TBL, {
		{any, []}, {bools, []}, {nums, []}, {atoms, []}, {lists, []}, {tuples, []}, {improper_elems, []}
	}).

-define(LIST_TYPES, [
		empty_list, nonempty_list,  
		nonempty_improper_list, maybe_improper_list, 
		nonempty_maybe_improper_list, list
	]).

infer_fun_type(Mod_name, Fun_name, Arity, Variables) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	Clauses_types = lists:map(fun(Clause) -> get_clause_type(Clause, Variables) end, Clauses),

	case length(Clauses_types) of
		1 -> Clauses_types;
		_ -> {union, Clauses_types}
	end.

get_clause_type(Clause, Variables) ->
	Bodies = get_bodies(Clause),
	define_bodies_type(Bodies, Variables).

get_clauses_type([], []) -> [];
get_clauses_type([Clause | Clauses], [Clause_variables | All_variables]) ->
	[get_clause_type(Clause, Clause_variables) | get_clauses_type(Clauses, All_variables)].

define_bodies_type([], _) -> [];
define_bodies_type([Last_body], Vars) ->
	{Clause_type, _Upd_vars} = infer_expr_inf(Last_body, Vars),
	Clause_type;
define_bodies_type([Body | Bodies], Vars) ->
	{_Body_type, Upd_vars} = infer_expr_inf(Body, Vars),
	define_bodies_type(Bodies, Upd_vars).



%---------------------------------Inference part-----------------------------------------------

infer_expr_inf(Expr, Vars) ->
	case ?Expr:type(Expr) of
		prefix_expr -> {infer_prefix_expr_type(Expr, ?Expr:value(Expr), Vars), Vars};
		match_expr -> infer_match_expr_inf(Expr, Vars);
		infix_expr -> {infer_infix_expr_type(Expr, ?Expr:value(Expr), Vars), Vars};
		variable   -> {infer_var_type(Expr, Vars), Vars};
		parenthesis -> {infer_parenthesis_inf(Expr, Vars), Vars};
		fun_expr    -> Fun_expr = {fun_expr, Expr},
		               {Fun_expr, Vars};
		application -> {infer_fun_app_type(Expr, Vars), Vars};
		cons        -> infer_cons_expr_type(Expr, Vars);
		tuple       -> infer_tuple_expr_type(Expr,Vars);
		implicit_fun -> {infer_implicit_fun_expr(Expr, Vars), Vars};
		_Simple_type    -> {infer_simple_type(Expr), Vars}
	end.

infer_implicit_fun_expr(Implicit_fun_expr, _Vars) ->
	[Fun_info_expr, Arity_expr] = ?Query:exec(Implicit_fun_expr, ?Expr:children()),

	case ?Expr:value(Fun_info_expr) of
		':' -> 	[Mod_name_expr, Fun_name_expr] = ?Query:exec(Fun_info_expr, ?Expr:children()),
				{implicit_fun, {{external_mod, ?Expr:value(Mod_name_expr)}, ?Expr:value(Fun_name_expr), ?Expr:value(Arity_expr)}};
		_   ->  Function = ?Query:exec(Implicit_fun_expr, ?Expr:function()),
				[Fun_mod] = ?Query:exec(Function, ?Fun:module()),
				{implicit_fun, {{current_mod, ?Mod:name(Fun_mod)}, ?Expr:value(Fun_info_expr), ?Expr:value(Arity_expr)}}
	end.

infer_var_type(Var_expr, Vars) ->
	Var = find_var_by_name(?Expr:value(Var_expr), Vars),	

	case Var of 
		{variable, _Var_name}     -> {any, []};
		{_Var_name, [{Tp, Val}]} -> {Tp, Val}
	end.

infer_simple_type(Expr) ->
	case ?Expr:value(Expr) of
		true  -> {boolean, [true]};
		false -> {boolean, [false]};
		_     -> {?Expr:type(Expr), [?Expr:value(Expr)]}
	end.

construct_and_convert_cons_to_cf(Cons_expr, Vars) ->
	{Lst, Upd_vars} = construct_list_from_cons_expr(Cons_expr, Vars),
	{convert_value_in_basic_format_to_compound(Lst), Upd_vars}.

infer_cons_expr_type(Cons_expr, Vars) ->
	{Lst_in_cf, Upd_vars} = construct_and_convert_cons_to_cf(Cons_expr, Vars),
	{generalize_term(Lst_in_cf, []), Upd_vars}.

construct_and_convert_tuple_to_cf(Tuple_expr, Vars) ->
	{Tuple, Upd_vars} = construct_tuple(Tuple_expr, Vars),
	{convert_value_in_basic_format_to_compound(Tuple), Upd_vars}.

infer_tuple_expr_type(Tuple_expr, Vars) ->
	{Tuple_in_cf, Upd_vars} = construct_and_convert_tuple_to_cf(Tuple_expr, Vars),
	{generalize_term(Tuple_in_cf, []), Upd_vars}.


infer_fun_app_type(Fun_app, Vars) ->
	[Expr, Arg_list] = ?Query:exec(Fun_app, ?Expr:children()),

	case ?Expr:type(Expr) of 
			variable -> infer_anonymus_function(?Expr:value(Expr), Arg_list, Vars);
			_        ->	case ?Expr:value(Expr) of
							':'      -> [Module, Fun] = ?Query:exec(Expr, ?Expr:children()),
										infer_external_fun(?Expr:value(Module), ?Expr:value(Fun), Arg_list, Vars);
							_        -> Function = ?Query:exec(Fun_app, ?Expr:function()),
						                [Fun_mod] = ?Query:exec(Function, ?Fun:module()),
										infer_internal_fun(?Mod:name(Fun_mod), ?Expr:value(Expr), Arg_list, Vars)
						end
	end.

find_var_by_name(Required_var_Name, Variables) ->
	Res = lists:filter(fun({Var_name, _}) -> Required_var_Name == Var_name end, Variables),

	case Res of
		[]    -> {variable, [Required_var_Name]};
		[Var] -> Var
	end.

is_bounded(Variable_name, Vars) ->
	Variable = find_var_by_name(Variable_name, Vars),

	case Variable of
		{variable, _Var_name} -> false;
		_  -> true
	end.

infer_anonymus_function(Var_name, Arg_lst_expr, Vars) ->
	case find_var_by_name(Var_name, Vars) of
		{variable, _Var_name}         -> infer_anon_func_app_without_body(Arg_lst_expr, Vars);
		{Var_name, [{fun_expr, _}]}   -> infer_anon_func_app(Var_name, Arg_lst_expr, Vars);
		{Var_name, [{implicit_fun, {{current_mod, Mod_name}, Fun_name, _Arity}}]}  -> infer_internal_fun(Mod_name, Fun_name, Arg_lst_expr, Vars);
		{Var_name, [{implicit_fun, {{external_mod, Mod_name}, Fun_name, _Arity}}]} -> infer_external_fun(Mod_name, Fun_name, Arg_lst_expr, Vars);
		_                           -> {none, []}
	end.

infer_anon_func_app_without_body(Arg_lst_expr, _Vars) ->
	Arg_lst_children = ?Query:exec(Arg_lst_expr, ?Expr:children()),
	Fun = fun(Arg) -> {Tp, _} = infer_expr_inf(Arg, []),
	 				  Tp 
	end,

	Arg_lst = lists:map(Fun, Arg_lst_children),
	{func, [Arg_lst, [any]]}.

infer_anon_func_app(Var_name, Arg_lst_expr, Vars) ->
	{_Var_name, [{fun_expr, Fun_expr}]} = find_var_by_name(Var_name, Vars),
	Arg_list_children = ?Query:exec(Arg_lst_expr, ?Expr:children()),
	Fun = fun(Arg) -> {Tp, _} = infer_expr_inf(Arg, Vars),
				      Tp 
	end,

	Arg_list = lists:map(Fun, Arg_list_children),

	Clause = ?Query:exec(Fun_expr, ?Expr:clauses()),
	Patterns = ?Query:exec(Clause, ?Clause:patterns()),
	[Fun_expr_vars] = replace_clauses_params_with_args([Patterns], Arg_list),

	New_var_list = replace_shadowed_vars_vals(Fun_expr_vars, Vars),
	
	get_clause_type(Clause, New_var_list).

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

infer_external_fun(Mod_name, Fun_name, Arg_list_expr, Variables) ->
	Arg_list = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arity = length(Arg_list),
	Spec_info = spec_proc:get_spec_type(Mod_name, Fun_name, Arity),

	case Spec_info of
		{_, [Return_type]} -> Return_type;
		[] -> infer_internal_fun(Mod_name, Fun_name, Arg_list_expr, Variables)
	end.

infer_internal_fun(Mod_name, Fun_name, Arg_list_expr, Parent_fun_variables) ->
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),

	Fun = fun(Arg) -> {Tp, _} = infer_expr_inf(Arg, Parent_fun_variables),
		              Tp
	end,

	Arg_list = lists:map(Fun, Arg_list_children),
	Arity = length(Arg_list),
	Actual_clauses_with_pats = find_actual_clauses(Mod_name, Fun_name, Arity, Arg_list),
	Actual_clauses = lists:map(fun({Clause, _}) -> Clause end, Actual_clauses_with_pats),
	Clauses_patterns = lists:map(fun({_, Pat}) -> Pat end, Actual_clauses_with_pats),

	Variables = replace_clauses_params_with_args(Clauses_patterns, Arg_list),
	Fun_type = get_clauses_type(Actual_clauses, Variables),

	case length(Fun_type) of
		1 -> hd(Fun_type);
		_ -> {union, Fun_type}
	end.

replace_clauses_params_with_args([], _) -> [];
replace_clauses_params_with_args([Pat | Pats], Args) ->
	[replace_clause_params_with_args(Pat, Args) | replace_clauses_params_with_args(Pats, Args)].

replace_clause_params_with_args([], []) -> [];
replace_clause_params_with_args([Par | Pars], [Arg | Args]) ->
	case ?Expr:type(Par) of
		variable -> [{?Expr:value(Par), [Arg]} | replace_clause_params_with_args(Pars, Args)];
		_        -> replace_clause_params_with_args(Pars, Args)
	end.

infer_parenthesis_inf(Expr, Vars) ->
	[Child] = get_children(Expr),
	infer_expr_inf(Child, Vars).

infer_match_expr_inf(Expr, Vars) ->
	[Ls_expr, Rs_expr] = get_children(Expr),

	case ?Expr:type(Ls_expr) of
		variable   -> bound_a_single_var(Ls_expr, Rs_expr, Vars);
		cons       -> bound_cons(Ls_expr, Rs_expr, Vars);
		tuple      -> bound_tuple(Ls_expr, Rs_expr, Vars);
		_Simple_tp -> match_simple_tp(Ls_expr, Rs_expr, Vars)
	end.

match_simple_tp(Ls_expr, Rs_expr, Vars) ->
	case ?Expr:type(Rs_expr) of
		variable -> {Ls_expr_tp, Upd_vars} = infer_expr_inf(Ls_expr, Vars),
					New_var = {?Expr:value(Rs_expr), [Ls_expr_tp]},
					{Ls_expr_tp, [New_var | Upd_vars]};
		_        -> {Ls_expr_tp, Upd_vars} = infer_expr_inf(Ls_expr, Vars),
					{_Rs_expr_tp, Upd_vars2} = infer_expr_inf(Rs_expr, Upd_vars),
					{Ls_expr_tp, Upd_vars2}
	end.
		           
bound_tuple(Ls_tuple, Rs_tuple, Vars) ->
	{Ls_tuple_tp, Upd_vars} = construct_and_convert_tuple_to_cf(Ls_tuple, Vars),
	{Rs_tuple_gen_tp, Upd_vars2} = infer_expr_inf(Rs_tuple, Upd_vars),
	bound_tuple_vars(Ls_tuple_tp, Rs_tuple_gen_tp, Rs_tuple_gen_tp, Upd_vars2).


bound_tuple_vars({ungen_tuple, []}, {tuple, []}, Match_expr_tp, Vars) ->
	{Match_expr_tp, Vars};
bound_tuple_vars(_Ls_tuple, {any, []}, _Match_expr_tp, Vars) ->
	{{any, []}, Vars};
bound_tuple_vars({ungen_tuple, [{variable, [Var_name]} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) ->
	case is_bounded(Var_name, Vars) of
		true  -> bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Vars);
		false -> New_var = {Var_name, [Rs_elem]},
		         bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, [New_var | Vars])
	end;
bound_tuple_vars({ungen_tuple, [{ungen_list, Lst_elems} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) -> 
	{_Lst_tp, Upd_vars} = bound_cons_vars({ungen_list, Lst_elems}, Rs_elem, Vars),
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Upd_vars);
bound_tuple_vars({ungen_tuple, [{ungen_tuple, Tuple_elems} | Ls_elems]}, {tuple, [Rs_elem | Rs_elems]}, Match_expr_tp, Vars) -> 
	{_Tuple, Upd_vars} = bound_tuple_vars({ungen_tuple, Tuple_elems}, Rs_elem, Rs_elem, Vars),
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Upd_vars);
bound_tuple_vars({ungen_tuple, [_Ls_elem | Ls_elems]}, {tuple, [_Rs_elem | Rs_elems]}, Match_expr_tp, Vars) ->
	bound_tuple_vars({ungen_tuple, Ls_elems}, {tuple, Rs_elems}, Match_expr_tp, Vars).

bound_a_single_var(Ls_expr, Rs_expr, Vars) ->
	Var_name = ?Expr:value(Ls_expr),
	Is_bounded = is_bounded(Var_name, Vars),

	case Is_bounded of
		true  -> infer_expr_inf(Ls_expr, Vars);
		false -> {Rs_cons_tp, Upd_vars} = infer_expr_inf(Rs_expr, Vars),
				 New_var = {Var_name, [Rs_cons_tp]},
				 {Rs_cons_tp, [New_var | Upd_vars]}
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


bound_cons(Ls_expr, Rs_expr, Vars) ->
	{Ls_cons_tp, Upd_vars} = construct_and_convert_cons_to_cf(Ls_expr, Vars),
	{Rs_cons_tp, Upd_vars2} = infer_expr_inf(Rs_expr, Upd_vars),
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
	case is_bounded(Var_name, Vars) of
		true  -> bound_cons_vars({Lst_tp, T}, Rs_cons_tp, Vars);
		false -> New_var = bound_cons_var({Lst_tp, [{variable, [Var_name]}]}, Rs_cons_tp),
		         bound_cons_vars({Lst_tp, T}, Rs_cons_tp, [New_var | Vars])
	end;
bound_cons_vars(Rs_cons = {_Lst_tp, [{'...', [Var_name]}]}, Rs_cons_tp, Vars) ->
	case is_bounded(Var_name, Vars) of
		true  -> {Rs_cons_tp, Vars};
		false -> New_var = bound_cons_var(Rs_cons, Rs_cons_tp),
		         {Rs_cons_tp, [New_var | Vars]}
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
generalize_elems([Elem | Elems], Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_with_new_elem(Elem, Elems_tbl),
	generalize_elems(Elems, Upd_elems_tbl).


generalize_term(Term, []) ->
generalize_term(Term, ?ELEMS_TBL);
generalize_term({Tp, Elem_val}, _Elems_tbl) when (Tp == fun_expr) or (Tp == implicit_fun) ->
	{Tp, Elem_val};
generalize_term({union, Elem_val}, Elems_tbl) ->
	Upd_elems_tbl = upd_elems_tbl_with_new_elems(Elem_val, Elems_tbl),
	convert_elems_tbl_to_internal_format(Upd_elems_tbl, []);
generalize_term({boolean, Elem_val}, _Elems_tbl) ->
	{boolean, Elem_val};
generalize_term({Elem_tp, Elem_val}, _Elems_tbl) when (Elem_tp == neg_integer) or (Elem_tp == pos_integer) 
	                                                          or (Elem_tp == non_neg_integer) or (Elem_tp == integer) 
	                                                          or (Elem_tp == float) or (Elem_tp == number) ->
	{Elem_tp, Elem_val};
generalize_term({Elem_tp, Elem_val}, _Elems_tbl) when (Elem_tp == atom) ->
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
convert_elems_tbl_to_internal_format([{lists, [Lst = {_Lst_tp, []}]} | T], Res) ->
	convert_elems_tbl_to_internal_format(T, [[Lst | Res]]);
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
		?IMPROPER_ELEMS_SEC_INDEX -> upd_improp_elems_sec({Tp, Val}, Sec)
	end,

	setelement(Index, Elems_tbl, Upd_sec).


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
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when Elem_tp == atom ->
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?ATOMS_SEC_INDEX),
	generalize_lst({Lst_tp, T}, Upd_elems_tbl);
generalize_lst({Lst_tp, [{Elem_tp, Elem_val} | T]}, Elems_tbl) when (Elem_tp == empty_list) or (Elem_tp == ungen_list)
															      or (Elem_tp == nonempty_list)
															      or (Elem_tp == nonempty_improper_list) or (Elem_tp == maybe_improper_list)
																  or (Elem_tp == nonempty_maybe_improper_list) or (Elem_tp == list) ->																  														   
	Upd_elems_tbl = upd_elems_tbl_by_index({Elem_tp, Elem_val}, Elems_tbl, ?LISTS_SEC_INDEX),
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
build_lst(Lst_tp, [{lists, [{Member_lst_tp, []}]} | T], Res) ->
	build_lst(Lst_tp, T, [[{Member_lst_tp, []}] | Res]);
build_lst(Lst_tp, [{lists, [{Member_lst_tp, Elems_tbl}]} | T], Res) ->
	Elems_tbl_secs = tuple_to_list(Elems_tbl),
	Lst = build_lst(Member_lst_tp, Elems_tbl_secs, []),
	build_lst(Lst_tp, T, [[Lst] | Res]);
build_lst(Lst_tp, [{_Label, Tp} | T], Res) ->
	build_lst(Lst_tp, T, [Tp | Res]).

generalize_lst_tp(Lst_tp, Lst_tp) ->
	Lst_tp;
generalize_lst_tp(undef_list, Lst2) ->
	Lst2;
generalize_lst_tp(Lst1, undef_list) ->
	Lst1;
generalize_lst_tp(maybe_improper_list, Lst2) when (Lst2 == nonempty_list) or (Lst2 == nonempty_improper_list) 
                                               or (Lst2 == nonempty_maybe_improper_list) or (Lst2 == list) ->
	maybe_improper_list;
generalize_lst_tp(Lst1, maybe_improper_list) when (Lst1 == nonempty_list) or (Lst1 == nonempty_improper_list) 
                                               or (Lst1 == nonempty_maybe_improper_list) or (Lst1 == list) ->
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


infer_infix_expr_type(Expr, Operation, Vars) ->
	[Sub_expr1, Sub_expr2] = get_children(Expr),
	{Expr_inf1, Upd_vars} = infer_expr_inf(Sub_expr1, Vars),
	{Expr_inf2, _Upd_vars2} = infer_expr_inf(Sub_expr2, Upd_vars),
%Добавить проверку на правильность типа	
	compute_infix_expr(Expr_inf1, Expr_inf2, Operation).

infer_prefix_expr_type(Expr, Operation, Vars) ->
	[Sub_expr] = ?Query:exec(Expr, ?Expr:children()),
	{Sub_expr_inf, _Upd_vars} = infer_expr_inf(Sub_expr, Vars),
	compute_prefix_expr(Sub_expr_inf, Operation).

compute_prefix_expr({union, Union_elems}, Operation) -> 
	{union, lists:map(fun(Expr1) -> compute_prefix_expr(Expr1, Operation) end, Union_elems)};

compute_prefix_expr({float, [Value]}, '+') ->
	{float, [+Value]};
compute_prefix_expr({Type, [Value]}, '+') when (Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer) ->
	{integer, [+Value]};

compute_prefix_expr({float, [Value]}, '-') ->
	{float, [-Value]};
compute_prefix_expr({Type, [Value]}, '-') when (Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer) ->
	{integer, [-Value]};

compute_prefix_expr({Type, [Value]}, 'bnot') when (Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer) ->
	if
		Value < 0 -> {integer, [bnot (Value)]};
		true      -> {integer, [bnot Value]}
	end;

compute_prefix_expr({float, []}, Operation) when ((Operation == '+') or (Operation == '-')) ->
	{float, []};
compute_prefix_expr({Type, []}, Operation) when ((Operation == '+') or (Operation == '-')) and 
												((Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer)) ->
	{integer, []};
compute_prefix_expr({Type, []}, Operation) when ((Operation == '+') or (Operation == '-')) and 
												((Type == number) or (Type == any)) ->
	{number, []};

compute_prefix_expr({Type, []}, 'bnot') when (Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer) ->
	{integer, []};
compute_prefix_expr({Type, []}, 'bnot') when (Type == number) or (Type == any) ->
	{number, []};

compute_prefix_expr({_Type, _Value}, _Operation) ->
	{none, []}.

compute_infix_expr({union, Union_elems1}, {union, Union_elems2}, Operation) -> 
	Two_unions_merged = [compute_infix_expr(Union_elem1, Union_elem2, Operation) || Union_elem1 <- Union_elems1, Union_elem2 <- Union_elems2],
	{union, lists:usort(Two_unions_merged)};
compute_infix_expr({union, Union_elems}, Expr2, Operation) -> 
	{union, lists:map(fun(Expr1) -> compute_infix_expr(Expr1, Expr2, Operation) end, Union_elems)};
compute_infix_expr(Expr1, {union, Union_elems}, Operation) -> 
	{union, lists:map(fun(Expr2) -> compute_infix_expr(Expr1, Expr2, Operation) end, Union_elems)};

compute_infix_expr({float, [Value1]}, {Type2, [Value2]}, '+') when ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float)) ->
	{float, [Value1 + Value2]};
compute_infix_expr({Type1, [Value1]}, {float, [Value2]}, '+') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float)) ->
	{float, [Value1 + Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '+') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														           ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 + Value2]};

compute_infix_expr({float, [Value1]}, {Type2, [Value2]}, '-') when ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float)) ->
	{float, [Value1 - Value2]};
compute_infix_expr({Type1, [Value1]}, {float, [Value2]}, '-') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float)) ->
	{float, [Value1 - Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '-') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														           ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 - Value2]};

compute_infix_expr({float, [Value1]}, {Type2, [Value2]}, '*') when ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float)) ->
	{float, [Value1 * Value2]};
compute_infix_expr({Type1, [Value1]}, {float, [Value2]}, '*') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float)) ->
	{float, [Value1 * Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '*') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														           ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 * Value2]};

compute_infix_expr(_Expr1, {_Type2, [0]}, '/') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '/') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float)) and
																   ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float)) ->
	{float, [Value1 / Value2]};


compute_infix_expr(_Expr1, {_Type2, [0]}, 'div') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'div') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
																     ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 div Value2]};

compute_infix_expr(_Expr1, {_Type2, [0]}, 'rem') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'rem') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
																     ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 rem Value2]};


compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'band') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														              ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 band Value2]};


compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'bor') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														             ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 bor Value2]};


compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'bxor') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														             ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 bxor Value2]};



compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'bsl') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														             ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 bsl Value2]};


compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'bsr') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														             ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 bsr Value2]};

compute_infix_expr({Type, [Value1]}, {Type, [Value2]}, 'and') when Type == boolean ->
	{boolean, [Value1 and Value2]};
compute_infix_expr({Type, [Value1]}, {Type, [Value2]}, 'or') when Type == boolean ->
	{boolean, [Value1 or Value2]};
compute_infix_expr({Type, [Value1]}, {Type, [Value2]}, 'xor') when Type == boolean ->
	{boolean, [Value1 xor Value2]};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, Operation) when ((Operation == 'and') or (Operation == 'or') or (Operation == 'xor')) and 
																	 ((Type1 == boolean) or (Type1 == any)) and ((Type2 == boolean) or (Type2 == any)) ->
	{boolean, []};

compute_infix_expr({float, _Value1}, {Type2, _Value2}, Operation) when ((Operation == '+') or (Operation == '-') or (Operation == '*') or (Operation == '/')) and
																	   ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float) or (Type2 == number) or (Type2 == any)) ->
	{float, []};
compute_infix_expr({Type1, _Value1}, {float, _Value2}, Operation) when ((Operation == '+') or (Operation == '-') or (Operation == '*') or (Operation == '/')) and
															           ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float) or (Type1 == number) or (Type1 == any)) ->
	{float, []};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, Operation) when ((Operation == '+') or (Operation == '-') or (Operation == '*') or (Operation == '/')) and
																       ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
														               ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, []};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, Operation) when ((Operation == '+') or (Operation == '-') or (Operation == '*') or (Operation == '/')) and
																       ((Type1 == number) or (Type1 == any)) and
														               ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float) or (Type2 == number) or (Type2 == any)) ->
	{number, []};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, Operation) when ((Operation == '+') or (Operation == '-') or (Operation == '*') or (Operation == '/')) and
                                                                        ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float) or (Type1 == number) or (Type1 == any)) and 
                                                                        ((Type2 == number) or (Type2 == any)) ->
	{number, []};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, Operation) when ((Operation == 'div') or (Operation == 'rem') or (Operation == 'band') or (Operation == 'bor') or (Operation == 'bxor') or (Operation == 'bsl') or (Operation == 'bsr')) and
                                                                        ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == number) or (Type1 == any)) and 
                                                                        ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == number) or (Type2 == any)) ->
	{integer, []};
compute_infix_expr(_A, _B, _Operation) ->
	{none, []}.

%---------------------------------Helper functions---------------------------------------------
convert_list_elems_in_basic_format_to_compound([], Converted_values) -> 
	{ungen_list, lists:reverse(Converted_values)};
convert_list_elems_in_basic_format_to_compound([{'...', Val}], Converted_values) ->
	{ungen_list, lists:reverse([{'...', Val} | Converted_values])};
convert_list_elems_in_basic_format_to_compound([H | T], Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),
	convert_list_elems_in_basic_format_to_compound(T, [Converted_value | Converted_values]);
convert_list_elems_in_basic_format_to_compound(Val, Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(Val),
	Reversed_values = lists:reverse(Converted_values),
	{ungen_list, Reversed_values ++ Converted_value}.

convert_tuple_elems_in_basic_format_to_compound([]) -> [];
convert_tuple_elems_in_basic_format_to_compound([H | T]) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),
	[Converted_value | convert_tuple_elems_in_basic_format_to_compound(T)].

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
														   or (Tp == float) or (Tp == number) or (Tp == any) -> 
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
	Patterns = [get_patterns(Clause) || Clause <- Clauses],

	case Actual_params of
		[] -> 	Fun_def = Fun_def,
				[Clause] = get_clauses(Fun_def),
				[{Clause, []}];
		_  ->   find_actual_clause(Patterns, Actual_params)   
	end.

find_actual_clause([], _) -> [];
find_actual_clause([Pat | Pats], Pars) ->
	Res = compare_pat_with_actual_pars(Pat, Pars, true),

	case Res of 
		true     -> [Clause] = 
		            	?Query:exec(hd(Pat), ?Expr:clause()),
				    [{Clause, Pat}];
		possibly -> [Clause] = ?Query:exec(hd(Pat), ?Expr:clause()),
				 	[{Clause, Pat} | find_actual_clause(Pats, Pars)];
		false    -> find_actual_clause(Pats, Pars)
	end.

compare_pat_with_actual_pars([], [], Status) ->
	Status;
compare_pat_with_actual_pars([Pat_elem | Pat_elems], [Par | Pars], Status) ->
	{Gen_pat_tp, _Upd_vars} = infer_expr_inf(Pat_elem, []),

	case are_matching_types(Gen_pat_tp, Par) of
		false    -> false;
		possibly -> compare_pat_with_actual_pars(Pat_elems, Pars, possibly);
		true     -> compare_pat_with_actual_pars(Pat_elems, Pars, Status)
	end.      

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
	

are_matching_types(Type, Type) ->
	true;

are_matching_types({any, []}, _Type2) ->
	possibly;
are_matching_types(_Type1, {any, []}) ->
	possibly;

are_matching_types({union, Elems1}, {union, Elems2}) ->
	are_matching_unions({union, Elems1}, {union, Elems2});
are_matching_types({union, Elems1}, Elem2) ->
	is_union_match({union, Elems1}, Elem2);
are_matching_types(Elem1, {union, Elems2}) ->
	is_union_match({union, Elems2}, Elem1);

are_matching_types({number, _Val1}, {Type2, _Val2}) when (Type2 == neg_integer) or (Type2 == pos_integer) 
												      or (Type2 == non_neg_integer) or (Type2 == integer) 
												      or (Type2 == float) or (Type2 == number) ->
	possibly;
are_matching_types({Tp1, _Val1}, {number, _Val2}) when (Tp1 == neg_integer) or (Tp1 == pos_integer) 
													or (Tp1 == non_neg_integer) or (Tp1 == integer) 
													or (Tp1 == float) or (Tp1 == number) ->
	possibly;

are_matching_types({_Type1, [Value]}, {_Type2, [Value]}) when is_number(Value) ->
	true;

are_matching_types({neg_integer, [_Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == integer) ->
	possibly;
are_matching_types({pos_integer, [_Value]}, {Type2, []}) when (Type2 == pos_integer) or (Type2 == non_neg_integer) 
														   or (Type2 == integer) ->
	possibly;
are_matching_types({non_neg_integer, [_Value]}, {Type2, []}) when (Type2 == non_neg_integer) or (Type2 == integer) ->
	possibly;
are_matching_types({integer, [_Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == pos_integer) 
                                                       or (Type2 == non_neg_integer) or (Type2 == integer) ->
	possibly;

are_matching_types({Type1, []}, {neg_integer, [_Value]}) when (Type1 == neg_integer) or (Type1 == integer) ->
	possibly;
are_matching_types({Type1, []}, {pos_integer, [_Value]}) when (Type1 == pos_integer) or (Type1 == non_neg_integer) 
                                                           or (Type1 == integer) ->
	possibly;
are_matching_types({Type1, []}, {non_neg_integer, [_Value]}) when (Type1 == non_neg_integer) or (Type1 == integer) ->
	possibly;
are_matching_types({Type1, []}, {integer, [_Value]}) when (Type1 == neg_integer) or (Type1 == pos_integer) 
                                                       or (Type1 == non_neg_integer) or (Type1 == integer) ->
	possibly;

are_matching_types({neg_integer, [_Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == integer) ->
	possibly;
are_matching_types({pos_integer, [_Value]}, {Type2, []}) when (Type2 == pos_integer) or (Type2 == non_neg_integer) 
                                                           or (Type2 == integer) ->
	possibly;
are_matching_types({non_neg_integer, [_Value]}, {Type2, []}) when (Type2 == non_neg_integer) or (Type2 == integer) ->
	possibly;
are_matching_types({integer, [_Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == pos_integer) 
                                                       or (Type2 == non_neg_integer) or (Type2 == integer) ->
	possibly;	
are_matching_types({Type, [Value1]}, {Type, [Value2]}) when (Value1 == Value2) ->
	true;
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
are_matching_types({variable, _Value}, _Type2) ->
	possibly;
are_matching_types(_Type1, {variable, _Value}) ->
	possibly;

are_matching_types({Lst_tp1, Elems1}, {Lst_tp2, Elems2}) when ((Lst_tp1 == nonempty_list)
                                                           or (Lst_tp1 == nonempty_improper_list) or (Lst_tp1 == maybe_improper_list)
                                                           or (Lst_tp1 == nonempty_maybe_improper_list) or (Lst_tp1 == list))
                                                          and ((Lst_tp2 == nonempty_list)
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


extract_expr_vals([], Vars) -> {[], Vars};
extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Vars) ->
	{Left_cons_expr_list, Upd_vars} = extract_expr_val(Left_cons_expr, Vars),
	{Right_cons_expr_list, Upd_vars2} = extract_expr_val(Right_cons_expr, Upd_vars),

	Cons = 
	case Right_cons_expr_list of
		{empty_list, []}    -> Left_cons_expr_list;
		{variable, Value} -> Left_cons_expr_list ++ [{'...', Value}];
		_             -> Left_cons_expr_list ++ Right_cons_expr_list
	end,

	{Cons, Upd_vars2};
extract_expr_vals([Expr | Exprs], Vars) ->

	case ?Expr:type(Expr) of 
		cons   -> {Cons, Upd_vars} = construct_list_from_cons_expr(Expr, Vars),
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars),
				  {[Cons | Vals], Upd_vars2};
		list   -> {Cons, Upd_vars} = construct_list_from_list_expr(Expr, Vars), 
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars),
				  {Cons ++ Vals, Upd_vars2};
		tuple  -> {Tuple, Upd_vars} = construct_tuple(Expr, Vars), 
				  {Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars),
				  {[Tuple | Vals], Upd_vars2};
		variable  -> Var_name = ?Expr:value(Expr),
					Var = obtain_var_val(Var_name, Vars),
					{Vals, Upd_vars2} = extract_expr_vals(Exprs, Vars),
		            {[Var | Vals], Upd_vars2};
		_        -> {Gen_expr_tp, Upd_vars} = infer_expr_inf(Expr, Vars), 
					{Vals, Upd_vars2} = extract_expr_vals(Exprs, Upd_vars),
					{[Gen_expr_tp | Vals], Upd_vars2}		
	end.

extract_expr_val(Expr, Vars) ->
	case ?Expr:type(Expr) of
		cons     -> construct_list_from_cons_expr(Expr, Vars);
		list     -> construct_list_from_list_expr(Expr, Vars);
		tuple    -> construct_tuple(Expr, Vars);
		variable -> Var_name = ?Expr:value(Expr),
					{obtain_var_val(Var_name, Vars), Vars};
		_        -> infer_expr_inf(Expr, Vars)
	end.

obtain_var_val(Var_name, Vars) ->
	Var = find_var_by_name(Var_name, Vars),

	case Var of
		{variable, [Var_name]} -> {variable, [Var_name]};
		{Var_name, [Value]}  -> Value
	end.

construct_tuple([], _Vars) -> [];
construct_tuple(Tuple, Vars) ->
	Children = ?Query:exec(Tuple, ?Expr:children()),
	{Tuple_elems_in_lst, Upd_vars} = extract_expr_vals(Children, Vars),
	{list_to_tuple(Tuple_elems_in_lst), Upd_vars}.


construct_list_from_cons_expr(Cons, Vars) ->
	Children = ?Query:exec(Cons, ?Expr:children()),

	case length(Children) of
		0 -> {{empty_list, []}, Vars};
		1 -> extract_expr_vals(Children, Vars);
		2 -> [Left_cons_expr, Right_cons_expr] = Children,
			 extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Vars)
	end.

construct_list_from_list_expr([], _Vars) -> [];
construct_list_from_list_expr(L, Vars) ->
	Children = ?Query:exec(L, ?Expr:children()),
	extract_expr_vals(Children, Vars).

%--------------------Extraction of a function specification from the typer result--------------------------------------
extract_matches([]) -> [];
extract_matches([H | T]) ->
	[hd(H) | extract_matches(T)]. 

get_fun_node(Mod_name, Fun_name, Arity) ->
	[Mod] = ?Query:exec(?Mod:find(Mod_name)),
	?Query:exec(Mod, ?Mod:local(Fun_name, Arity)).

get_typer_specs(Path) ->
	Spec = os:cmd("typer " ++ [$" | Path] ++ "\""),
	RE = lists:concat(["-spec ", ".+\."]),
	{_, Capture} = re:run(Spec, RE, [global, {capture, all, list}]),
	extract_matches(Capture).

get_fun_name([]) -> [];
get_fun_name([$-, $s, $p, $e, $c, 32 | T]) ->
	get_fun_name(T);
get_fun_name([$( | _]) ->
	[];
get_fun_name([H | T]) ->
	[H | get_fun_name(T)].

get_arity(Spec) ->
	compute_arity(Spec, 0, 0, 0, 0, 0).


compute_arity([$, | T], 0, 0, 1, 0, Arity) ->
	compute_arity(T, 0, 0, 1, 0, Arity + 1);
compute_arity([$[ | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List + 1, Tupple, Fun, Binary, Arity);
compute_arity([$] | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List - 1, Tupple, Fun, Binary, Arity);
compute_arity([${ | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple + 1, Fun, Binary, Arity);
compute_arity([$} | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple - 1, Fun, Binary, Arity);
compute_arity([$( | T], List, Tupple, 0, Binary, _) ->
	case hd(T) of
		$) -> 0;
		_  -> compute_arity(T, List, Tupple, 1, Binary, 1)
	end;
compute_arity([$( | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple, Fun + 1, Binary, Arity);
compute_arity([$) | T], List, Tupple, Fun, Binary, Arity) ->
	case Fun of
		1 -> Arity;
		_ -> compute_arity(T, List, Tupple, Fun - 1, Binary, Arity)
	end;
compute_arity([$<, $< | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple, Fun, Binary + 1, Arity);
compute_arity([$>, $> | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple, Fun, Binary - 1, Arity);
compute_arity([_ | T], List, Tupple, Fun, Binary, Arity) ->
	compute_arity(T, List, Tupple, Fun, Binary, Arity).
	

test() ->
	Test1 = infer_fun_type(unit_test, af1, 0, []),
	erlang:display({test1, af1, Test1 == [{integer, [305]}]}),

	Test2 = infer_fun_type(unit_test, af2, 0, []),
	erlang:display({test2, af2, Test2 == [{integer, [7]}]}),

	Test3 = infer_fun_type(unit_test, af3, 0, []),
	erlang:display({test3, af3, Test3 == [{integer, [3]}]}),

	Test4 = infer_fun_type(unit_test, af3_2, 0, []),
	erlang:display({test4, af3_2, Test4 == [{integer, [3]}]}),

	Test5 = infer_fun_type(unit_test, af3_3, 0, []),
	erlang:display({test5, af3_3, Test5 == [{number,[]}]}),

	Test6 = infer_fun_type(unit_test, af4_2, 0, []),
	erlang:display({test6, af4_2, Test6 == [{integer, [3]}]}),

	Test7 = infer_fun_type(unit_test, lfac_2, 0, []),
	erlang:display({test7, lfac_2, Test7 == [{any,[]}]}),

	Test8 = infer_fun_type(unit_test, lfac2_2, 0, []),
	erlang:display({test8, lfac2_2, Test8 == [{atom,[ok]}]}),

	Test9 = infer_fun_type(unit_test, lfac3_3, 1, []),
	erlang:display({test9, lfac3_3, Test9 == [{atom,[ok]}]}),

	Test10 = infer_fun_type(unit_test, lfac4_4, 0, []),
	erlang:display({test10, lfac4_4, Test10 == [{atom,[ok]}]}),

	Test11 = infer_fun_type(unit_test, lfac5_5, 0, []),
	erlang:display({test11, lfac5_5, Test11 == [{atom,[ok]}]}),

	Test12 = infer_fun_type(unit_test, lfac7_7, 0, []),
	erlang:display({test12, lfac7_7, Test12 == [{atom,[ok]}]}),

	Test13 = infer_fun_type(unit_test, ei1, 0, []),
	erlang:display({test13, ei1, Test13 == [{nonempty_list,[{union,[{integer,[1]},{integer,[2]},{integer,[4]}]}]}]}),

	Test14 = infer_fun_type(unit_test, ei2, 0, []),
	erlang:display({test14, ei2, Test14 == [{nonempty_list,[{union,[{integer,[1]},{integer,[2]},{nonempty_list,[{union,[{integer,[1]},{integer,[2]},{integer,[3]}]}]}]}]}]}),

	Test15 = infer_fun_type(unit_test, ei3, 0, []),
	erlang:display({test15, ei3, Test15 == [{tuple,[{nonempty_list,[{union,[{integer,[1]},{integer,[2]}]}]},{nonempty_list,[{union,[{integer,[3]},{integer,[4]}]}]}]}]}),

	Test16 = infer_fun_type(unit_test, ei4, 0, []),
	erlang:display({test16, ei4, Test16 == [{nonempty_list,[{union,[{integer,[1]},{integer,[2]}]}]}]}),

	Test17 = infer_fun_type(unit_test, ei5, 0, []),
	erlang:display({test17, ei5, Test17 == [{nonempty_improper_list,[{integer,[1]},{integer,[2]}]}]}),

	Test18 = infer_fun_type(unit_test, ei6, 1, []),
	erlang:display({test18, ei6, Test18 == [{nonempty_maybe_improper_list,[{any, []}]}]}),

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
	erlang:display({test65, cons_bound, Test65 == [{any, []}]}),

	Test66 = infer_fun_type(unit_test, cons_bound2, 1, []),
	erlang:display({test66, cons_bound2, Test66 == [{any, []}]}),

	Test67 = infer_fun_type(unit_test, cons_bound3, 1, []),
	erlang:display({test67, cons_bound3, Test67 == [{number, []}]}),

	Test68 = infer_fun_type(unit_test, cons_bound4, 0, []),
	erlang:display({test68, cons_bound4, Test68 == [{integer, [2]}]}),

	Test69 = infer_fun_type(unit_test, cons_bound5, 0, []),
	erlang:display({test69, cons_bound5, Test69 == [{integer, [87]}]}),

	Test70 = infer_fun_type(unit_test, cons_bound6, 0, []),
	erlang:display({test70, cons_bound6, Test70 == [{union,
												     [{nonempty_improper_list,
												          [{union,[{integer,[1]},{integer,[2]}]},{integer,[3]}]},
												      {integer,[3]}]}]}),

	Test71 = infer_fun_type(unit_test, cons_bound7, 0, []),
	erlang:display({test71, cons_bound7, Test71 == [{list,[{union,[{integer,[1]},
										                {integer,[2]},
										                {integer,[3]}]}]}]}),

	Test72 = infer_fun_type(unit_test, cons_bound8, 0, []),
	erlang:display({test72, cons_bound8, Test72 == [{union,[{integer,[1]},{integer,[2]}]}]}),

	Test77 = infer_fun_type(unit_test, cons_bound9, 0, []),
	erlang:display({test77, cons_bound9, Test77 == [{tuple,[{integer,[1]},{integer,[2]},{integer,[3]}]}]}),

%Tuple bound

	Test73 = infer_fun_type(unit_test, tuple_bound, 0, []),
	erlang:display({test73, tuple_bound, Test73 == [{integer,[1]}]}),

	Test74 = infer_fun_type(unit_test, tuple_bound2, 0, []),
	erlang:display({test74, tuple_bound2, Test74 == [{integer,[1]}]}),

	Test75 = infer_fun_type(unit_test, tuple_bound3, 0, []),
	erlang:display({test75, tuple_bound3, Test75 == [{tuple,[{integer,[4]},{integer,[5]}]}]}),

	Test76 = infer_fun_type(unit_test, tuple_bound4, 1, []),
	erlang:display({test76, tuple_bound4, Test76 == [{tuple,[{any,[]},{integer,[5]}]}]}),

	Test78 = infer_fun_type(unit_test, match_expr, 1, []),
	erlang:display({test78, match_expr, Test78 == [{integer,[4]}]}),

	Test79 = infer_fun_type(unit_test, cons_bound10, 0, []),
	erlang:display({test79, cons_bound10, Test79 == [{tuple,[{integer,[3]},{integer,[4]},{integer,[5]}]}]}),

	Test80 = infer_fun_type(unit_test, cl_mat, 0, []),
	erlang:display({test80, cl_mat, Test80 == [{atom,[horoso]}]}).



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














%--------------------------------Testing------------------------------------------
print_expr_val(Expr) ->
	Actual_vals = extract_expr_vals([Expr], []),

	case ?Expr:type() of
		tuple -> erlang:list_to_tuple(Actual_vals);
		_     -> Actual_vals
	end.
%--------------------------------Defining of actual ret type----------------------

get_typer_ret_val([]) -> [];
get_typer_ret_val(Spec) ->
	Ret_val = move_to_ret_val(Spec),
	extract_possible_ret_types(Ret_val, [], 0, 0).

move_to_ret_val([$>, 32 | T]) ->
	lists:droplast(T);
move_to_ret_val([_ | T]) ->
	move_to_ret_val(T).

extract_possible_ret_types([], Buf, _, _) ->
	lists:reverse(Buf);
extract_possible_ret_types([32 | T], Buf, In_tupple, In_list) ->
	extract_possible_ret_types(T, Buf, In_tupple, In_list);
extract_possible_ret_types([$| | T], Buf, 0, 0) ->
	[lists:reverse(Buf) | [extract_possible_ret_types(T, [], 0, 0)]];
extract_possible_ret_types([H | T], Buf, In_tupple, In_list) ->
	extract_possible_ret_types(T, [H | Buf], In_tupple, In_list).

define_simple_type("float()") ->
	[float, number];
define_simple_type("integer()") ->
	[integer, number];
define_simple_type("number()") ->
	[number];
define_simple_type("atom()") -> 
	[atom];
define_simple_type(A) ->
	REs = ["\\d+\.\\d+", "\\d+", "\'.+\'"],
	Matches = [re:run(A, RE, [{capture, first, list}]) || RE <- REs],

	case Matches of
		[{match, [A]}, _, _] -> erlang:list_to_float(A);
		[_, {match, [A]}, _] -> erlang:list_to_integer(A);
		[_, _, {match, [A]}] -> erlang:list_to_atom(lists:droplast(tl(A)))
	end.

%-----------------Код ненужный на данный момент-------------


%are_matching_types({Type1, Vals1}, {Type2, Vals2}) when ((Type1 == defined_list) or (Type1 == list) or (Type1 == nonempty_list) or (Type1 == improper_list)) and
%														((Type2 == defined_list) or (Type2 == list) or (Type2 == nonempty_list) or (Type2 == improper_list)) ->
%	are_matching_lists({Type1, Vals1}, {Type2, Vals2});

%are_matching_types(_Type1, _Type2) ->
%	false.

%are_matching_lists(List, List) ->
%	true;
%are_matching_lists({empty_list, []}, {list, _Val}) ->
%	true;
%are_matching_lists({list, _Val}, {empty_list, []}) ->
%	true;
%are_matching_lists(List1, List2) ->
%	are_lists_elems_matching(List1, List2).


are_lists_elems_matching({_Type1, []}, {_Type2, []}) ->
	true;
are_lists_elems_matching({_Type1, _Elems1}, {nonempty_list, [{'...', _}]}) ->
	true;
are_lists_elems_matching({nonempty_list, [{'...', _}]}, {_Type2, _Elems2}) ->
	true;
are_lists_elems_matching({defined_list, [Elem1 | Elems1]}, {defined_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({defined_list, Elems1}, {defined_list, Elems2});

are_lists_elems_matching({defined_list, [Elem1 | Elems1]}, {nonempty_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({defined_list, Elems1}, {nonempty_list, Elems2});
are_lists_elems_matching({nonempty_list, [Elem1 | Elems1]}, {defined_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({nonempty_list, Elems1}, {defined_list, Elems2});

are_lists_elems_matching({_List1_type, [Elem1 | _Elems1]}, {list, [Elem2]}) ->
	are_matching_types(Elem1, Elem2);
are_lists_elems_matching({list, [Elem1]}, {_List2_type, [Elem2 | _Elems2]}) ->
	are_matching_types(Elem1, Elem2);

are_lists_elems_matching({nonempty_list, [Elem1 | Elems1]}, {nonempty_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching(Elems1, Elems2);

are_lists_elems_matching({_Type1, [_Elem1 | _Elems1]}, {_Type2, []}) ->
	false;
are_lists_elems_matching({_Type1, []}, {_Type2, [_Elem2 | _Elems2]}) ->
	false.




convert_values_in_compound_format_to_basic([]) -> [];
convert_values_in_compound_format_to_basic({empty_list, []}) ->
	{empty_list, []};
convert_values_in_compound_format_to_basic([H | T]) ->
	[convert_value_in_compound_format_to_basic(H) | convert_values_in_compound_format_to_basic(T)];
convert_values_in_compound_format_to_basic(Val) ->
	convert_value_in_compound_format_to_basic(Val).

convert_value_in_compound_format_to_basic({empty_list, []}) -> 
	[];
convert_value_in_compound_format_to_basic({'...', Val}) -> 
	{'...', Val};
convert_value_in_compound_format_to_basic({Type, []}) ->
	{Type, []};
convert_value_in_compound_format_to_basic({Type, [Val]}) when is_integer(Type) or is_float(Type) or is_atom(Type) or is_boolean(Type) ->
	Val;
convert_value_in_compound_format_to_basic({variable, Val}) ->
	{variable, Val};
convert_value_in_compound_format_to_basic({List_type, Values}) when (List_type == ungen_list) ->
	convert_values_in_compound_format_to_basic(Values);
convert_value_in_compound_format_to_basic({tuple, Values}) ->
	Tuple_elems_list = convert_values_in_compound_format_to_basic(Values),
	list_to_tuple(Tuple_elems_list).

%--------------------------Looking for actual clauses-----
	

compare_terms([], []) -> true;
compare_terms([Pat | Pats], [Par | Pars]) ->
	Param_type = ?Expr:type(Par),
	Pat_type = ?Expr:type(Pat),

	case {Param_type, Pat_type} of
		{cons, cons}     -> case compare_cons(Pat, Par) of
						   		true  -> compare_terms(Pats, Pars);
						   		possibly -> compare_terms(Pats, Pars);
								false -> false
							end;
		{tuple, tuple} -> case compare_tuples(Pat, Par) of
						   		true  -> compare_terms(Pats, Pars);
						   		possibly -> compare_terms(Pats, Pars);
								false -> false
							end;
		{_, variable}    -> possibly;
		{variable, _}    -> possibly;
		_                -> case compare_simple_type(Pat, Par) of
								true  -> compare_terms(Pats, Pars);
								possibly -> compare_terms(Pats, Pars);
								false -> false
							end
	end.

compare_tuples(T1, T2) ->
	Children1 = ?Query:exec(T1, ?Expr:children()),
	Children2 = ?Query:exec(T2, ?Expr:children()),

	if
		length(Children1) == length(Children2) -> compare_terms(Children1, Children2);
		true                                   -> false
	end.

compare_cons(Con1, Con2) ->
	List_elems1 = construct_list_from_cons_expr(Con1, []),
	List_elems2 = construct_list_from_cons_expr(Con2, []),

	compare_lists_elems(List_elems1, List_elems2, true).

compare_simple_type(Pat, Par) ->
	?Expr:value(Pat) =:= ?Expr:value(Par).

compare_lists_elems(_, _, false) ->
	false;
compare_lists_elems(L, L, Status) -> Status;
compare_lists_elems([{'...', _Value}], _, _) ->
	possibly;
compare_lists_elems(_, [{'...', _Value}], _) ->
	possibly;
compare_lists_elems([], _L2, _) ->
	false;
compare_lists_elems(_L1, [], _) ->
	false;
compare_lists_elems([{variable, _} | T1], [_ | T2], _) ->
	compare_lists_elems(T1, T2, possibly);
compare_lists_elems([_ | T1], [{variable, _} | T2], _) ->
	compare_lists_elems(T1, T2, possibly);
compare_lists_elems([H1 | T1], [H2 | T2], Status) when erlang:is_list(H1) and erlang:is_list(H2) ->
	Result = compare_lists_elems(H1, H2, Status),

	case Result of
		false -> false;
		possibly -> compare_lists_elems(T1, T2, possibly);
		true     -> compare_lists_elems(T1, T2, Status)
	end;
compare_lists_elems([H1 | T1], [H2 | T2], Status) when erlang:is_tuple(H1) and erlang:is_tuple(H2) ->
	Tuple1 = erlang:tuple_to_list(H1),
	Tuple2 = erlang:tuple_to_list(H2),
	Result = compare_lists_elems(Tuple1, Tuple2, Status),

	case Result of
		false -> false;
		possibly -> compare_lists_elems(T1, T2, possibly);
		true     -> compare_lists_elems(T1, T2, Status)
	end;
compare_lists_elems([H1 | T1], [H2 | T2], Status) ->
	case H1 == H2 of
		true -> compare_lists_elems(T1, T2, Status);
		false -> false
	end.
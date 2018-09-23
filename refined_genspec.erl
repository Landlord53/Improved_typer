-module(refined_genspec).

%Сравнить результат тайпера и рузультат моего алгоритма. Отрбасывать все варианты тайпера, которые совсем не совпадают с результатом моего алгоритма. Например Если результат моего алгоритма выдаёт "integer | list", а тайпер "number | list | atom", то оставляем только "number | list". 

%------TODO list----------------
%1)Process guard expressions(В разделе "Defining actual clauses")
%2)Process fun expressions  (В разделе "Defining actual clauses")
%3)Добавить проверку, что если паттерн абсолютно совпадает с actual parameters, не проверять дальше.
%4)Функция get_fun_name не обрабатывает случай, когда можду именем функции и скобками есть пробелы.
%5)Добавить ":" d infix expressions.
%6)Добавить обработку случая, когда нет actual clauses для функции infer_internal_fun.
%7)Добавить обработку случая, для выражений типо [1,2 | B] = SomeList, а так же когда аргумент функции паттерматчат к дкакому-либо значению.
%8)Обрадотать случай, когда последнее выражение фнкции - funxepression.


-include("user.hrl").
-include("spec.hrl").

-compile(export_all).

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
define_bodies_type([Last_body], Variables) ->
	Clause_type = infer_expr_inf(Last_body, Variables),

	case Clause_type of
		{Var_name, {Type, Value}} -> {Type, Value};
		_                         -> Clause_type
	end;
define_bodies_type([Body | Bodies], Variables) ->
	Body_type = infer_expr_inf(Body, Variables),

	case Body_type of
		{_Var_name, {_Type, _Value}} -> define_bodies_type(Bodies, [Body_type | Variables]);
		_                  -> define_bodies_type(Bodies, Variables)
	end.

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

%---------------------------------Inference part-----------------------------------------------

infer_expr_inf(Expr, Variables) ->
	case ?Expr:type(Expr) of
		prefix_expr -> infer_prefix_expr_type(Expr, ?Expr:value(Expr), Variables);
		match_expr -> infer_match_expr_inf(Expr, Variables);
		infix_expr -> infer_infix_expr_type(Expr, ?Expr:value(Expr), Variables);
		variable   -> infer_var_type(Expr, Variables);
		parenthesis -> infer_parenthesis_inf(Expr, Variables);
		fun_expr    -> {fun_expr, Expr};
		application -> infer_fun_app_type(Expr, Variables);
		cons        -> infer_cons_expr_type(Expr, Variables);
		tuple       -> infer_tuple_expr_type(Expr,Variables);
		implicit_fun -> infer_implicit_fun_expr(Expr, Variables);
		Simple_type    -> infer_simple_type(Expr)
	end.

infer_implicit_fun_expr(Implicit_fun_expr, Variables) ->
	[Fun_info_expr, Arity_expr] = ?Query:exec(Implicit_fun_expr, ?Expr:children()),

	case ?Expr:value(Fun_info_expr) of
		':' -> 	[Mod_name_expr, Fun_name_expr] = ?Query:exec(Fun_info_expr, ?Expr:children()),
				{implicit_fun, {{external_mod, ?Expr:value(Mod_name_expr)}, ?Expr:value(Fun_name_expr), ?Expr:value(Arity_expr)}};
		_   ->  Function = ?Query:exec(Implicit_fun_expr, ?Expr:function()),
				[Fun_mod] = ?Query:exec(Function, ?Fun:module()),
				{implicit_fun, {{current_mod, ?Mod:name(Fun_mod)}, ?Expr:value(Fun_info_expr), ?Expr:value(Arity_expr)}}
	end.

infer_var_type(Expr, Variables) ->
	Var = find_variable_by_name(?Expr:value(Expr), Variables),	

	case Var of 
		[] -> {any, []};
		[{_Var_name, {Type, Value}}] -> {Type, Value}
	end.

infer_simple_type(Expr) ->
	case ?Expr:value(Expr) of
		true  -> {boolean, [true]};
		false -> {boolean, [false]};
		_     -> {?Expr:type(Expr), [?Expr:value(Expr)]}
	end.

infer_cons_expr_type(Expr, Variables) ->
	List_in_basic_form = construct_list_from_cons_expr(Expr, Variables),
	convert_value_in_basic_format_to_compound(List_in_basic_form).

infer_tuple_expr_type(Expr, Variables) ->
	Tuple_elems_list = construct_tuple(Expr, Variables),
	Tuple_in_basic_format = list_to_tuple(Tuple_elems_list),
	convert_value_in_basic_format_to_compound(Tuple_in_basic_format).

infer_fun_app_type(Fun_app, Variables) ->
	[Expr, Arg_list] = ?Query:exec(Fun_app, ?Expr:children()),

	case ?Expr:type(Expr) of 
			variable -> infer_anonymus_function(?Expr:value(Expr), Arg_list, Variables);
			_        ->	case ?Expr:value(Expr) of
							':'      -> [Module, Fun] = ?Query:exec(Expr, ?Expr:children()),
										infer_external_fun(?Expr:value(Module), ?Expr:value(Fun), Arg_list, Variables);
							_        -> Function = ?Query:exec(Fun_app, ?Expr:function()),
						                [Fun_mod] = ?Query:exec(Function, ?Fun:module()),
										infer_internal_fun(?Mod:name(Fun_mod), ?Expr:value(Expr), Arg_list, Variables)
						end
	end.

find_variable_by_name(Required_var_Name, Variables) ->
	lists:filter(fun({Var_name, _}) -> Required_var_Name == Var_name end, Variables).

is_bounded(Variable_name, Variables) ->
	Variable = find_variable_by_name(Variable_name, Variables),

	case Variable of
		[] -> false;
		_  -> true
	end.

infer_anonymus_function(Var_name, Arg_list_expr, Variables) ->
	case find_variable_by_name(Var_name, Variables) of
		[]                          -> infer_anonymus_func_app_without_body(Arg_list_expr, Variables);
		[{Var_name, {fun_expr, _}}] -> infer_anonymus_func_app(Var_name, Arg_list_expr, Variables);
		[{Var_name, {implicit_fun, {{current_mod, Mod_name}, Fun_name, _Arity}}}] -> infer_internal_fun(Mod_name, Fun_name, Arg_list_expr, Variables);
		[{Var_name, {implicit_fun, {{external_mod, Mod_name}, Fun_name, _Arity}}}] -> infer_external_fun(Mod_name, Fun_name, Arg_list_expr, Variables);
		_                           -> {none, []}
	end.

infer_anonymus_func_app_without_body(Arg_list_expr, Variables) ->
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, []) end, Arg_list_children),
	{func, [Arg_list, [any]]}.

infer_anonymus_func_app(Var_name, Arg_list_expr, Variables) ->
	[{_Var_name, {fun_expr, Fun_expr}}] = find_variable_by_name(Var_name, Variables),
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, Variables) end, Arg_list_children),


	Clause = ?Query:exec(Fun_expr, ?Expr:clauses()),
	Patterns = ?Query:exec(Clause, ?Clause:patterns()),
	[Fun_expr_vars] = replace_clauses_params_with_args([Patterns], Arg_list),

	New_var_list = replace_shadowed_vars_vals(Fun_expr_vars, Variables),
	
	get_clause_type(Clause, New_var_list).

replace_shadowed_vars_vals([], Vars) -> Vars;
replace_shadowed_vars_vals([Anon_fun_var | Anon_fun_vars], Vars) ->
	New_var_list = replace_shadowed_vars_val(Anon_fun_var, Vars, []),
	replace_shadowed_vars_vals(Anon_fun_vars, New_var_list).
	
replace_shadowed_vars_val(Anon_fun_var, [], New_var_list) ->
	[Anon_fun_var | New_var_list];
replace_shadowed_vars_val({Var_name, Value1}, [{Var_name, Value2} | Vars], New_var_list) ->
	[{Var_name, Value1} | New_var_list] ++ Vars;
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
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, Parent_fun_variables) end, Arg_list_children),
	Arity = length(Arg_list),
	Actual_clauses_with_pats = find_actual_clauses(Mod_name, Fun_name, Arity, Arg_list_children),
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
		variable -> [{?Expr:value(Par), Arg} | replace_clause_params_with_args(Pars, Args)];
		_        -> replace_clause_params_with_args(Pars, Args)
	end.

infer_parenthesis_inf(Expr, Variables) ->
	[Child] = get_children(Expr),
	infer_expr_inf(Child, Variables).

infer_match_expr_inf(Expr, Variables) ->
	[Variable, Sub_expr] = get_children(Expr),

	{?Expr:value(Variable), infer_expr_inf(Sub_expr, Variables)}.

bound_variables(Variable1, Variable2, Variables) ->
	case ?Expr:type(Variable1) of
		variable -> bound_single_variable(Variable1, Variable2, Variables);
		_        -> ok
	end.	

bound_single_variable(Variable, Expr, Variables) ->
	Is_bounded = is_bounded(Variable, Variables),	

	case Is_bounded of
		true  -> Variable1_type = infer_expr_inf(Variable, Variables),
				 Variable2_type = infer_expr_inf(Expr, Variables);



		false -> {?Expr:value(Variable), infer_expr_inf(Expr, Variables)}
	end.	

compare_types(Type, Type) ->
	true;
compare_types({any, _Val1}, _Type2) ->
	true;
compare_types(_Type1, {any, _Val2}) ->
	true;
compare_types({number, _Val1}, {Type2, _Val2}) when ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float) or (Type2 == number)) ->
	true;
compare_types({Type1, _Val1}, {number, _Val2}) when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float) or (Type1 == number)) ->
	true;
compare_types({list, Vals1}, {list, Vals2}) ->
	ok.

infer_infix_expr_type(Expr, Operation, Variables) ->
	[Sub_expr1, Sub_expr2] = get_children(Expr),
	Expr_inf1 = infer_expr_inf(Sub_expr1, Variables),
	Expr_inf2 = infer_expr_inf(Sub_expr2, Variables),
%Добавить проверку на правильность типа	
	compute_infix_expr(Expr_inf1, Expr_inf2, Operation).

infer_prefix_expr_type(Expr, Operation, Variables) ->
	[Sub_expr] = ?Query:exec(Expr, ?Expr:children()),
	Sub_expr_inf = infer_expr_inf(Sub_expr, Variables),
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

compute_infix_expr(_Expr1, {Type2, [0]}, '/') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '/') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float)) and
																   ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float)) ->
	{float, [Value1 / Value2]};


compute_infix_expr(_Expr1, {Type2, [0]}, 'div') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'div') when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer)) and
																     ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer)) ->
	{integer, [Value1 div Value2]};

compute_infix_expr(_Expr1, {Type2, [0]}, 'rem') ->
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
compute_infix_expr({Type1, Value1}, {Type2, Value2}, Operation) when ((Operation == 'and') or (Operation == 'or') or (Operation == 'xor')) and 
																	 ((Type1 == boolean) or (Type1 == any)) and ((Type2 == boolean) or (Type2 == any)) ->
	{boolean, []};

%Тут
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
convert_values_in_basic_format_to_compound([]) -> [];
convert_values_in_basic_format_to_compound([H | T]) ->
	[convert_value_in_basic_format_to_compound(H) | convert_values_in_basic_format_to_compound(T)].

convert_value_in_basic_format_to_compound([]) -> 
	[];
convert_value_in_basic_format_to_compound({list, []}) -> 
	{list, []};
convert_value_in_basic_format_to_compound('...') -> 
	'...';
convert_value_in_basic_format_to_compound(Value) when is_integer(Value)->
	{integer, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_float(Value) ->
	{float, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_atom(Value) ->
	{atom, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_boolean(Value) ->
	{boolean, [Value]};
convert_value_in_basic_format_to_compound({variable, Value}) ->
	{variable, Value};
convert_value_in_basic_format_to_compound(Value) when is_list(Value) ->
	{list, convert_values_in_basic_format_to_compound(Value)};
convert_value_in_basic_format_to_compound(Value) when is_tuple(Value) ->
	Tuple_elems_list = tuple_to_list(Value),
	{tuple, convert_values_in_basic_format_to_compound(Tuple_elems_list)}.

convert_values_in_compound_format_to_basic([]) -> [];
convert_values_in_compound_format_to_basic([H | T]) ->
	[convert_value_in_compound_format_to_basic(H) | convert_values_in_compound_format_to_basic(T)].

convert_value_in_compound_format_to_basic({list, []}) -> 
	[];
convert_value_in_compound_format_to_basic('...') -> 
	'...';
convert_value_in_compound_format_to_basic({Type, [Value]}) when is_integer(Type) or is_float(Type) or is_atom(Type) or is_boolean(Type) ->
	Value;
convert_value_in_compound_format_to_basic({variable, Value}) ->
	{variable, Value};
convert_value_in_compound_format_to_basic({list, Values}) ->
	convert_values_in_compound_format_to_basic(Values);
convert_value_in_compound_format_to_basic({tuple, Values}) ->
	Tuple_elems_list = convert_values_in_compound_format_to_basic(Values),
	list_to_tuple(Tuple_elems_list).

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
find_actual_clause([], _) -> [];
find_actual_clause([Pat | Pats], Pars) ->
	Res = compare_terms(Pat, Pars),

	case Res of 
		true  -> [Clause] = ?Query:exec(hd(Pat), ?Expr:clause()),
				 [{Clause, Pat} | find_actual_clause(Pats, Pars)];
		false -> find_actual_clause(Pats, Pars)
	end.	

compare_terms([], []) -> true;
compare_terms([Pat | Pats], [Par | Pars]) ->
	Param_type = ?Expr:type(Par),
	Pat_type = ?Expr:type(Pat),

	case {Param_type, Pat_type} of
		{cons, cons}     -> case compare_cons(Pat, Par) of
						   		true  -> compare_terms(Pats, Pars);
								false -> false
							end;
		{tuple, tuple} -> case compare_tuples(Pat, Par) of
						   		true  -> compare_terms(Pats, Pars);
								false -> false
							end;
		{_, variable}    -> true;
		{variable, _}    -> true;
		_                -> case compare_simple_type(Pat, Par) of
								true  -> compare_terms(Pats, Pars);
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

	erlang:display(List_elems1),
	erlang:display(List_elems2),

	compare_lists_elems(List_elems1, List_elems2).

compare_simple_type(Pat, Par) ->
	?Expr:value(Pat) =:= ?Expr:value(Par).

compare_lists_elems(L, L) -> true;
compare_lists_elems(['...'], _) ->
	true;
compare_lists_elems(_, ['...']) ->
	true;
compare_lists_elems([], L2) ->
	false;
compare_lists_elems(L1, []) ->
	false;
compare_lists_elems([{variable, _} | T1], [_ | T2]) ->
	compare_lists_elems(T1, T2);
compare_lists_elems([_ | T1], [{variable, _} | T2]) ->
	compare_lists_elems(T1, T2);
compare_lists_elems([H1 | T1], [H2 | T2]) when erlang:is_list(H1) and erlang:is_list(H2) ->
	compare_lists_elems(H1, H2) and compare_lists_elems(T1, T2);
compare_lists_elems([H1 | T1], [H2 | T2]) when erlang:is_tuple(H1) and erlang:is_tuple(H2) ->
	Tuple1 = erlang:tuple_to_list(H1),
	Tuple2 = erlang:tuple_to_list(H2),
	compare_lists_elems(Tuple1, Tuple2) and compare_lists_elems(T1, T2);
compare_lists_elems([H1 | T1], [H2 | T2]) ->
	case H1 == H2 of
		true -> compare_lists_elems(T1, T2);
		false -> false
	end.

extract_expr_vals([], _) -> [];
extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Variables) ->
	Left_cons_expr_list = extract_expr_val(Left_cons_expr, Variables),
	Right_cons_expr_list = extract_expr_val(Right_cons_expr, Variables),

	case Right_cons_expr_list of
		{list, []}    -> Left_cons_expr_list;
		{variable, _} -> Left_cons_expr_list ++ ['...'];
		_             -> Left_cons_expr_list ++ Right_cons_expr_list
	end;
extract_expr_vals([H | T], Variables) ->

	case ?Expr:type(H) of 
		cons -> [construct_list_from_cons_expr(H, Variables) | extract_expr_vals(T, Variables)];
		list -> construct_list_from_list_expr(H, Variables) ++ extract_expr_vals(T, Variables);
		tuple -> [construct_tuple(H, Variables) | extract_expr_vals(T, Variables)];
		variable -> [{variable, ?Expr:value(H)} | extract_expr_vals(T, Variables)];
		_        -> [?Expr:value(H) | extract_expr_vals(T, Variables)] 		
	end.

extract_expr_val(Expr, Variables) ->
	case ?Expr:type(Expr) of
		cons     -> construct_list_from_cons_expr(Expr, Variables);
		list     -> construct_list_from_list_expr(Expr, Variables);
		tuple    -> construct_tuple(Expr, Variables);
		variable -> {variable, ?Expr:value(Expr)};
		_        -> ?Expr:value(Expr)	
	end.

construct_tuple([], Variables) -> [];
construct_tuple(Tuple, Variables) ->
	Children = ?Query:exec(Tuple, ?Expr:children()),
	extract_expr_vals(Children, Variables).

construct_list_from_cons_expr(Cons, Variables) ->
	Children = ?Query:exec(Cons, ?Expr:children()),

	case length(Children) of
		0 -> {list, []};
		1 -> extract_expr_vals(Children, Variables);
		2 -> [Left_cons_expr, Right_cons_expr] = Children,
			 extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Variables)
	end.

construct_list_from_list_expr([], Variables) -> [];
construct_list_from_list_expr(L, Variables) ->
	Children = ?Query:exec(L, ?Expr:children()),
	extract_expr_vals(Children, Variables).

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
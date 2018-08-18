-module(refined_genspec).

%------TODO list----------------
%1)Process guard expressions(В разделе "Defining actual clauses")
%2)Process fun expressions  (В разделе "Defining actual clauses")
%3)Добавить проверку, что если паттерн абсолютно совпадает с actual parameters, не проверять дальше.
%4)Функция get_fun_name не обрабатывает случай, когда можду именем функции и скобками есть пробелы.
%5)Добавить ":" d infix expressions.
%6)Добавить обработку случая, когда нет actual clauses для функции infer_internal_fun.

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
	%erlang:display({Clause, Variables}),
	Bodies = get_bodies(Clause),
	define_bodies_type(Bodies, Variables).

get_clauses_type([], []) -> [];
get_clauses_type([Clause | Clauses], [Clause_variables | All_variables]) ->
	[get_clause_type(Clause, Clause_variables) | get_clauses_type(Clauses, All_variables)].

define_bodies_type([], _) -> [];
define_bodies_type([Last_body], Variables) ->
	infer_expr_inf(Last_body, Variables);
define_bodies_type([Body | Bodies], Variables) ->
	Body_type = infer_expr_inf(Body, Variables),
	%erlang:display(Body_type),

	case Body_type of
		{_Var_name, {_Type, _Value}} -> define_bodies_type(Bodies, [Body_type | Variables]);
		_                            -> define_bodies_type(Bodies, Variables)
	end.

find_actual_clauses(Mod_name, Fun_name, Arity, Actual_params) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	Patterns = [get_patterns(Clause) || Clause <- Clauses],

	case Actual_params of
		[] -> 	Fun_def = Fun_def,
				get_clauses(Fun_def);
		_  ->   find_actual_clause(Patterns, Actual_params)   
	end.

%---------------------------------Inference part-----------------------------------------------

infer_expr_inf(Expr, Variables) ->
	case ?Expr:type(Expr) of
		prefix_expr -> infer_prefix_expr_type(Expr, ?Expr:value(Expr), Variables);
		match_expr -> infer_match_expr_inf(Expr, Variables);
		infix_expr -> infer_infix_expr_type(Expr, ?Expr:value(Expr), Variables);
		variable   -> Var = find_variable_by_name(?Expr:value(Expr), Variables),	
					  case Var of 
					  	[] -> {any, []};
					  	[{_V, {Type, Val}}] -> {Type, Val}
					  end;
		parenthesis -> infer_parenthesis_inf(Expr, Variables);
		fun_expr    -> Expr;
		application -> infer_fun_app_type(Expr, Variables);
		Simple_type    -> infer_simple_type(Expr)
	end.

infer_simple_type(Expr) ->
	case ?Expr:value(Expr) of
		true  -> {boolean, [true]};
		false -> {boolean, [false]};
		_     -> {?Expr:type(Expr), [?Expr:value(Expr)]}
	end.

infer_fun_app_type(Fun_app, Variables) ->
	[Expr, Arg_list] = ?Query:exec(Fun_app, ?Expr:children()),

	case ?Expr:type(Expr) of 
			variable -> infer_anonymus_function(?Expr:value(Expr), Arg_list, Variables);
			_        ->	case ?Expr:value(Expr) of
							':'      -> infer_external_fun(Expr, Arg_list);
							_        -> Function = ?Query:exec(Fun_app, ?Expr:function()),
						                [Fun_mod] = ?Query:exec(Function, ?Fun:module()),
										infer_internal_fun(?Mod:name(Fun_mod), ?Expr:value(Expr), Arg_list)
						end
	end.

find_variable_by_name(Required_var_Name, Variables) ->
	lists:filter(fun({Var_name, _}) -> Required_var_Name == Var_name end, Variables).

infer_anonymus_function(Fun_name, Arg_list_expr, []) ->
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, []) end, Arg_list_children),
	{any, []};
infer_anonymus_function(Fun_name, Arg_list_expr, Variables) ->
	[{_Var_name, Fun_expr}] = find_variable_by_name(Fun_name, Variables),
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, Variables) end, Arg_list_children),

	%erlang:display(Arg_list),
	Clause = ?Query:exec(Fun_expr, ?Expr:clauses()),
	Patterns = ?Query:exec(Clause, ?Clause:patterns()),
	erlang:display(Patterns),
	[Fun_expr_vars] = replace_clauses_params_with_args([Patterns], Arg_list),

	erlang:display(Fun_expr_vars),
	get_clause_type(Clause, Fun_expr_vars).

infer_external_fun(Colon_op, Arg_list_expr) ->
	[Module, Fun] = ?Query:exec(Colon_op, ?Expr:children()),
	Arg_list = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Args = ?Query:exec(Arg_list, ?Expr:children()),
	Arity = length(Args),
	Mod_name = ?Expr:value(Module),
	Fun_name = ?Expr:value(Fun),
	{_, [Return_type]} = spec_proc:get_spec_type(Mod_name, Fun_name, Arity),
	Return_type.

infer_internal_fun(Mod_name, Fun_name, Arg_list_expr) ->
	Arg_list_children = ?Query:exec(Arg_list_expr, ?Expr:children()),
	Arg_list = lists:map(fun(Arg) -> infer_expr_inf(Arg, []) end, Arg_list_children),
	Arity = length(Arg_list),
	Actual_clauses_with_pats = find_actual_clauses(Mod_name, Fun_name, Arity, Arg_list_children),
	Actual_clauses = lists:map(fun({Clause, _}) -> Clause end, Actual_clauses_with_pats),
	Clauses_patterns = lists:map(fun({_, Pat}) -> Pat end, Actual_clauses_with_pats),
	Variables = replace_clauses_params_with_args(Clauses_patterns, Arg_list),
	erlang:display(Variables),
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

infer_infix_expr_type(Expr, Operation, Variables) ->
	[Sub_expr1, Sub_expr2] = get_children(Expr),
	Expr_inf1 = infer_expr_inf(Sub_expr1, Variables),
	Expr_inf2 = infer_expr_inf(Sub_expr2, Variables),
	%erlang:display({Expr_inf1, Expr_inf2}),
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

	A = 
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
	end,
	%erlang:display(A),
	A.

compare_tuples(T1, T2) ->
	Children1 = ?Query:exec(T1, ?Expr:children()),
	Children2 = ?Query:exec(T2, ?Expr:children()),

	if
		length(Children1) == length(Children2) -> compare_terms(Children1, Children2);
		true                                   -> false
	end.

compare_cons(Con1, Con2) ->
	Children1 = construct_list_from_cons_expr(Con1),
	Children2 = construct_list_from_cons_expr(Con2),
	%erlang:display(Children1),
	%erlang:display(Children2),
	compare_lists_elems(Children1, Children2).

compare_simple_type(Pat, Par) ->
	?Expr:value(Pat) =:= ?Expr:value(Par).

compare_lists_elems(L, L) -> true;
compare_lists_elems(empty_list, _)  ->
	false;
compare_lists_elems(_, empty_list)  ->
	false;
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
	compare_lists_elems(H1, H2) and compare_terms(T1, T2);
compare_lists_elems([H1 | T1], [H2 | T2]) when erlang:is_tuple(H1) and erlang:is_tuple(H2) ->
	Tuple1 = erlang:tuple_to_list(H1),
	Tuple2 = erlang:tuple_to_list(H2),
	compare_lists_elems(Tuple1, Tuple2) and compare_lists_elems(T1, T2);
compare_lists_elems([H1 | T1], [H2 | T2]) ->
	case H1 == H2 of
		true -> compare_lists_elems(T1, T2);
		false -> false
	end.

extract_expr_vals([]) -> [];
extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}]) ->
	Left_cons_expr_list = construct_list_from_expr(Left_cons_expr),
	Right_cons_expr_list = construct_list_from_expr(Right_cons_expr),

	case Right_cons_expr_list of
		empty_list    -> Left_cons_expr_list;
		{variable, _} -> Left_cons_expr_list ++ ['...'];
		_             -> Left_cons_expr_list ++ Right_cons_expr_list
	end;
extract_expr_vals([H | T]) ->
	case ?Expr:type(H) of 
		cons -> [construct_list_from_cons_expr(H)];
		list -> construct_list_from_list_expr(H);
		tuple -> [construct_tuple(H) | extract_expr_vals(T)];
		variable -> [{variable, [?Expr:value(H)]} | extract_expr_vals(T)];
		_        -> [?Expr:value(H) | extract_expr_vals(T)] 		
	end;
extract_expr_vals(Cons_child) ->
	case ?Expr:type(Cons_child) of 
		cons -> empty_list;
		list -> construct_list_from_list_expr(Cons_child);
		tuple -> construct_tuple(Cons_child);
		variable -> {variable, [?Expr:value(Cons_child)]};
		_        -> ?Expr:value(Cons_child)		
	end.

construct_list_from_expr(Expr) ->
	case ?Expr:type(Expr) of
		cons     -> construct_list_from_cons_expr(Expr);
		list     -> construct_list_from_list_expr(Expr);
		tuple    -> construct_tuple(Expr);
		variable -> {variable, [?Expr:value(Expr)]};
		_        -> ?Expr:value(Expr)	
	end.

construct_tuple([]) -> [];
construct_tuple(Tuple) ->
	Children = ?Query:exec(Tuple, ?Expr:children()),
	Vals = extract_expr_vals(Children).

construct_list_from_cons_expr(Cons) ->
	Children = ?Query:exec(Cons, ?Expr:children()),

	case length(Children) of
		0 -> extract_expr_vals(Cons);
		1 -> extract_expr_vals(Children);
		2 -> [Left_cons_expr, Right_cons_expr] = Children,
			 extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}])
	end.

construct_list_from_list_expr([]) -> [];
construct_list_from_list_expr(L) ->
	Children = ?Query:exec(L, ?Expr:children()),
	extract_expr_vals(Children).

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
	Actual_vals = extract_expr_vals([Expr]),

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
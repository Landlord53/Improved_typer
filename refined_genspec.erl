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
%12)Улучшить обработку случая типа bound_cons_elems({List_type1, [{'...', [Value]} | Elems1]}, {list, [{'...', [Value]} | Elems2]}).Так как я не знаю тип элемента до {'...', [Value]} пришлось поставить просто any.
%13)Добавить стринг
%14)Добавить типы pos_integer, neg_integer, etc о время вычисления infix expressions и prefix expressions

-include("user.hrl").
-include("spec.hrl").

-compile(export_all).


%Pay attention that the index values and the order number of elements in the POSSIBLE_TYPES macros has to match.
-define(ANY_INDEX, 1).
-define(BOOLS_INDEX, 2).
-define(NUMS_INDEX, 3).
-define(ATOMS_INDEX, 4).
-define(LISTS_INDEX, 5).
-define(TUPLES_INDEX, 6).
%Pay attention that the IMPROPER_PART_INDEX has to be always the last element of the POSSIBLE_TYPES macros.
-define(IMPROPER_PART_INDEX, 7). 

-define(POSSIBLE_TYPES, {
		{any, []}, {bools, []}, {nums, []}, {atoms, []}, {lists, []}, {tuples, []}, {improper_part, []}
	}).

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

	%erlang:display(Body_type),

	case Body_type of
		{_Var_name, {_Type, _Value}} -> define_bodies_type(Bodies, [Body_type | Variables]);
		Type when is_list(Type) -> define_bodies_type(Bodies, Body_type ++ Variables);
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
	[Leftside_expr, Rightside_expr] = get_children(Expr),

	%erlang:display(?Expr:type(Leftside_expr)),

	case ?Expr:type(Leftside_expr) of
		variable -> bound_a_single_var(Leftside_expr, Rightside_expr, Variables);
		cons     -> bound_cons(Leftside_expr, Rightside_expr, Variables)
	end.

	%{?Expr:value(Leftside_expr), infer_expr_inf(Rightside_expr, Variables)}.

bound_a_single_var(Rightside_expr, Leftside_expr, Variables) ->
	Right_var_name = ?Expr:value(Rightside_expr),
	Is_bounded = is_bounded(Right_var_name, Variables),
	

	case Is_bounded of
		true  -> Variable1_type = infer_expr_inf(Rightside_expr, Variables),
				 Variable2_type = infer_expr_inf(Leftside_expr, Variables),

				 case are_matching_types(Variable1_type, Variable2_type) of
				 	true -> {?Expr:value(Rightside_expr), Variable1_type};
				 	false -> {none, []}
				 end;
		false -> {?Expr:value(Rightside_expr), infer_expr_inf(Leftside_expr, Variables)}
	end.	

bound_cons(Leftside_cons, Rightside_expr, Variables) ->
	Leftside_cons_type = infer_expr_inf(Leftside_cons, Variables),
	Rightside_expr_type = infer_expr_inf(Rightside_expr, Variables),

	%erlang:display(Leftside_cons_type),
	%erlang:display(Rightside_expr_type),

	Are_matching_types = are_matching_types(Leftside_cons_type, Rightside_expr_type),

	%erlang:display(Are_matching_types),

	case Are_matching_types of
		true ->  Generalized_list_type = generalize_list_type(Rightside_expr_type, []),
				 bound_cons_elems(Leftside_cons_type, Generalized_list_type);
		false -> {none, []}
	end.

generate_type_value_table([], []) -> 
	[];
generate_type_value_table([Elem | Elems], [Occur_values_for_elem | Occur_values]) ->
	Upd_occur_values = generalize_elem(Elem, Occur_values_for_elem),
	[Upd_occur_values | generate_type_value_table(Elems, Occur_values)].

generalize_elems([], Possible_types) ->
	Possible_types_in_list = tuple_to_list(Possible_types),
	Generalized_elems = build_type_info(Possible_types_in_list, []),
	{Generalized_elems, Possible_types};
generalize_elems([Elem | Elems], Possible_types) ->
	Upd_possible_types = generalize_elem(Elem, Possible_types),
	generalize_elems(Elems, Upd_possible_types).

ge(A) ->
	generalize_elems(A, ?POSSIBLE_TYPES).

build_type_info([], Res) ->
	Type_info = lists:reverse(lists:concat(Res)),

	case length(Type_info) of
		0 -> [];
		1 -> Type_info;
		_ -> {union, Type_info}
	end;
build_type_info([{_Label, []} | T], Res) ->
	build_type_info(T, Res);

build_type_info([{lists, [List = {Pos_list_type, []}]} | T], Res) ->
	build_type_info(T, [[List | Res]]);
build_type_info([{lists, [{Pos_list_type, Elems_type}]} | T], Res) ->
	Elems_type_in_list = tuple_to_list(Elems_type),
	List = build_list(Pos_list_type, Elems_type_in_list, []),
	build_type_info(T, [[List] | Res]);
build_type_info([{_Label, Type} | T], Res) ->
	build_type_info(T, [Type | Res]).

generalize_elem({El_type, El_value}, Possible_types) when El_type == boolean ->
	generalize_elem_by_index({El_type, El_value}, Possible_types, ?BOOLS_INDEX);
generalize_elem({El_type, El_value}, Possible_types) when ((El_type == neg_integer) or (El_type == pos_integer) or (El_type == non_neg_integer) or (El_type == integer) or (El_type == float) or (El_type == number)) ->
	generalize_elem_by_index({El_type, El_value}, Possible_types, ?NUMS_INDEX);
generalize_elem({El_type, El_value}, Possible_types) when El_type == atom ->
	generalize_elem_by_index({El_type, El_value}, Possible_types, ?ATOMS_INDEX);
generalize_elem({El_type, El_value}, Possible_types) when (El_type == empty_list) or (El_type == improper_list) or (El_type == defined_list) or (El_type == non_empty_list) ->
	generalize_elem_by_index({El_type, El_value}, Possible_types, ?LISTS_INDEX);
generalize_elem({El_type, El_value}, Possible_types) when El_type == tuple ->
	generalize_elem_by_index({El_type, El_value}, Possible_types, ?TUPLES_INDEX);	


update_tuple_in_tvt({tuple, Elems}, Occur_values) when (Occur_values == {tuple, []}) or (Occur_values == []) ->
	Elems_num = length(Elems),
	Upd_occur_vals = generate_type_value_table(Elems, lists:duplicate(Elems_num, ?POSSIBLE_TYPES)),
	{tuple, [Upd_occur_vals]};	
update_tuple_in_tvt({tuple, Elems}, {tuple, [Tp_val_tbl | Tp_val_tbls]}) ->
	case length(Elems) == length(Tp_val_tbl) of
		true  -> Upd_tp_val_tbl = generate_type_value_table(Elems, Tp_val_tbl),
			     [Upd_tp_val_tbl | Tp_val_tbls];
		false -> update_tuple_in_tvt({tuple, Elems}, Tp_val_tbls)
	end.

generalize_elem_by_index({Type, Value}, Possible_types, Index) ->
	Elem = element(Index, Possible_types),

	Gen_elem_values = 
	case Index of
		?BOOLS_INDEX -> generalize_bools({Type, Value}, Elem);
		?NUMS_INDEX -> generalize_numbers({Type, Value}, Elem);
		?ATOMS_INDEX -> generalize_atoms({Type, Value}, Elem);
		?LISTS_INDEX -> generalize_lists({Type, Value}, Elem)
		?TUPLES_INDEX -> update_tuple_in_tvt({Type, Value}, Elem)
	end,
		
	setelement(Index, Possible_types, Gen_elem_values).

generalize_list_elems_by_index({List_type, [{El_type, El_value} | T]}, Possible_types, Index) ->
	Upd_possible_types = generalize_elem_by_index({El_type, El_value}, Possible_types, Index),
	generalize_list_type({non_empty_list, T}, Upd_possible_types).

generalize_single_elem({Type, Value}) when (Type == empty_list) or (Type == improper_list) or (Type == defined_list) or (Type == non_empty_list) ->
	{Generalized_elem, _} = generalize_list_type({Type, Value}, []),
	generalized_elem;
generalize_single_elem({Type, Value}) ->
	{Type, Value}.
	
%empty_list
generalize_list_type(Empty_list = {empty_list, []}, Possible_types) ->
	{Empty_list, Possible_types};

generalize_list_type({_Type, Elems}, [])->
	generalize_list_type({non_empty_list, Elems}, ?POSSIBLE_TYPES);

%improper list
generalize_list_type(List = {List_type, {Type, Value}}, Possible_types) ->
	Improp_elem = generalize_single_elem({Type, Value}),

	Possible_types_in_list = tuple_to_list(Possible_types),
	{Gen_list_type, Gen_Elems} = build_list(nonempty_improper_list, Possible_types_in_list, []),

	{improper_part, Improp_elems} = element(?IMPROPER_PART_INDEX, Possible_types),
	{improper_part, Upd_improp_elems} = generalize_improper_part(Improp_elem, {improper_part, Improp_elems}),	

	{{Gen_list_type, Gen_Elems ++ Upd_improp_elems}, setelement(?IMPROPER_PART_INDEX, Possible_types, {improper_part, Upd_improp_elems})};

generalize_list_type({List_type, []}, Possible_types) ->
	Possible_types_in_list = tuple_to_list(Possible_types),
	Gen_list = build_list(List_type, Possible_types_in_list, []),
	{improper_part, Improp_elems} = element(?IMPROPER_PART_INDEX, Possible_types),

	case Improp_elems of
		[{empty_list, []}] -> {Gen_list, Possible_types};
		[]                -> {Gen_list, setelement(?IMPROPER_PART_INDEX, Possible_types, {improper_part, [{empty_list, []}]})};
		Multiple_elems    -> {improper_part, Upd_improp_elems} = generalize_improper_part({empty_list, []}, {improper_part, Improp_elems}),
		                     {Gen_list, setelement(?IMPROPER_PART_INDEX, Possible_types, {improper_part, Upd_improp_elems})}
	end;

generalize_list_type({List_type, [_ | T]}, Possible_types) when element(?ANY_INDEX, Possible_types) == {any, [{any, []}]} ->
	generalize_list_type({non_empty_list, T}, Possible_types);

%nonempty_maybe_improper_list
generalize_list_type({non_empty_list, [{'...', Value}]}, Possible_types) ->
	Upd_possible_types = setelement(?LISTS_INDEX, Possible_types, {nonempty_maybe_improper_list, []}),
	{{undef_nonempty_maybe_improper_list, []}, Upd_possible_types};

generalize_list_type({List_type, [{variable, Value} | T]}, Possible_types) ->
	Upd_possible_types = setelement(1, ?POSSIBLE_TYPES, {any, [{any, []}]}),
	generalize_list_type({List_type, T}, Upd_possible_types);

generalize_list_type(List = {List_type, [{El_type, El_value} | T]}, Possible_types) when El_type == boolean ->
	generalize_list_elems_by_index(List, Possible_types, ?BOOLS_INDEX);
	
generalize_list_type(List = {List_type, [{El_type, El_value} | T]}, Possible_types) when ((El_type == neg_integer) or (El_type == pos_integer) or (El_type == non_neg_integer) or (El_type == integer) or (El_type == float) or (El_type == number)) ->
	generalize_list_elems_by_index(List, Possible_types, ?NUMS_INDEX);

generalize_list_type(List = {List_type, [{El_type, El_value} | T]}, Possible_types) when El_type == atom ->
	generalize_list_elems_by_index(List, Possible_types, ?ATOMS_INDEX);

generalize_list_type(List = {List_type, [{El_type, El_value} | T]}, Possible_types) when (El_type == empty_list) or (El_type == improper_list) or (El_type == defined_list) or (El_type == non_empty_list) ->
	generalize_list_elems_by_index(List, Possible_types, ?LISTS_INDEX).

generalize_improper_part(Improp_elem, {improper_part, []}) ->
	{improper_part, [Improp_elem]};
generalize_improper_part(Improp_elem, {improper_part, Elems}) ->
	case lists:member(Improp_elem, Elems) of
		true  -> {improper_part, Elems};
		false -> {improper_part, [Improp_elem | Elems]}
	end.

generalize_bools(Boolean, {bools, []}) ->
	{bools, [Boolean]};
generalize_bools({boolean, Value}, {bools, [{boolean, []}]}) ->
	{bools, [{boolean, []}]};
generalize_bools({boolean, [Value]}, {bools, [{boolean, [Value]}]}) ->
	{bools, [{boolean, [Value]}]};
generalize_bools({boolean, [false]}, {bools, [{boolean, [true]}]}) ->
	{bools, [{boolean, []}]};
generalize_bools({boolean, [true]}, {bools, [{boolean, [false]}]}) ->
	{bools, [{boolean, []}]}.

generalize_atoms(Atom, {atoms, []}) ->
	{atoms, [Atom]};
generalize_atoms({atom, []}, _) ->
	{atoms, [{atom, []}]};
generalize_atoms(_, {atoms, [{atom, []}]}) ->
	{atoms, [{atom, []}]};
generalize_atoms({Type, Value}, {atoms, Values}) ->
	case lists:member({Type, Value}, Values) of
		true -> {atoms, Values};
		false -> {atoms, [{Type, Value} | Values]}
	end.

generalize_numbers({Type, Value}, {nums, []}) ->
	{Type, [{Type, Value}]};
generalize_numbers({number, []}, _) ->
	{number, [{number, []}]};
generalize_numbers(_Number, Nums = {number, [{number, []}]}) ->
	Nums;

generalize_numbers({Type, Value}, {Type, [{Type, []}]}) ->
	{Type, [{Type, []}]};	
generalize_numbers({Type, []}, {Type, _}) ->
	{Type, [{Type, []}]};	
generalize_numbers({Type, Value}, {integer, [{integer, []}]}) when ((Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer)) -> 
	{integer, [{integer, []}]};
generalize_numbers({integer, Value}, {Gen_type, [{Gen_type, []}]}) when ((Gen_type == neg_integer) or (Gen_type == pos_integer) or (Gen_type == non_neg_integer)) ->
	{integer, [{integer, []}]};
generalize_numbers({non_neg_integer, Value}, {pos_integer, [{pos_integer, []}]}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
generalize_numbers({Type, Value}, {neg_integer, [{neg_integer, []}]}) when (Type == pos_integer) or (Type == non_neg_integer) ->
	{integer, [{integer, []}]};
generalize_numbers({pos_integer, Value}, {non_neg_integer, [{non_neg_integer, []}]}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
generalize_numbers({neg_integer, Value}, {Gen_type, [{Gen_type, []}]}) when (Gen_type == pos_integer) or (Gen_type == non_neg_integer) ->
	{integer, [{integer, []}]};		
generalize_numbers({float, Value}, {Gen_type, Values}) when ((Gen_type == neg_integer) or (Gen_type == pos_integer) or (Gen_type == non_neg_integer) or (Gen_type == integer)) ->
	{number, [{number, []}]};
generalize_numbers({Type, Value}, {float, Values}) when ((Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer) or (Type == integer)) ->
	{number, [{number, []}]};
generalize_numbers({Type, []}, {integer, Values}) when ((Type == neg_integer) or (Type == pos_integer) or (Type == non_neg_integer)) ->
	{integer, [{integer, []}]};
generalize_numbers({non_neg_integer, []}, {pos_integer, Values}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
generalize_numbers({Type, []}, {neg_integer, Values}) when (Type == pos_integer) or (Type == non_neg_integer) ->
	{integer, [{integer, []}]};
generalize_numbers({pos_integer, []}, {non_neg_integer, Values}) ->
	{non_neg_integer, [{non_neg_integer, []}]};
generalize_numbers({neg_integer, []}, {Gen_type, Values}) when (Gen_type == pos_integer) or (Gen_type == non_neg_integer) ->
	{integer, [{integer, []}]};
generalize_numbers({Num_type, [Value]}, {Gen_type, Values}) -> 

	case lists:member({Num_type, [Value]}, Values) of
		true -> {Num_type, Values};
		false -> {Num_type, [{Num_type, [Value]} | Values]}
	end.

generalize_lists(List, {lists, []}) ->
	{{List_type, Elems}, Possible_types} = generalize_list_type(List, []),
	{lists, [{List_type, Possible_types}]};
generalize_lists({List_type, Elems}, {lists, [{Gen_list_type, Prev_lst_possible_types}]}) when (Gen_list_type == undef_maybe_improper_list) or (Gen_list_type == undef_nonempty_maybe_improper_list) ->
	{{New_list_type, _}, New_possible_types} = generalize_list_type({List_type, Elems}, Prev_lst_possible_types),
	New_gen_list_type = generalize_two_lists(New_list_type, Gen_list_type),
	{lists, [{New_gen_list_type, ?POSSIBLE_TYPES}]};
generalize_lists({List_type, Elems}, {lists, [{Gen_list_type, Prev_lst_possible_types}]}) ->
	{{New_list_type, _}, New_possible_types} = generalize_list_type({List_type, Elems}, Prev_lst_possible_types),
	New_gen_list_type = generalize_two_lists(New_list_type, Gen_list_type),
	{lists, [{New_gen_list_type, New_possible_types}]}.

build_list(List_type, [{improper_part, Elems_type}], Res) ->
	List = lists:reverse(lists:concat(Res)),

	Improper_part = 
		case Elems_type of
			[] -> [];
			[{empty_list, []}] -> [];
			[Elem] -> [Elem];
			_ -> [{union, Elems_type}]
		end,

	case length(List) > 1 of
		false -> {List_type, List ++ Improper_part};
		true -> {List_type, [{union, List}] ++ Improper_part}
	end;
build_list(List_type, [{_Label, []} | T], Res) ->
	build_list(List_type, T, Res);
build_list(List_type, [{lists, [{Pos_list_type, []}]} | T], Res) ->
	build_list(List_type, T, [[{Pos_list_type, []}] | Res]);
build_list(List_type, [{lists, [{Pos_list_type, Elems_type}]} | T], Res) ->
	Elems_type_in_list = tuple_to_list(Elems_type),
	List = build_list(Pos_list_type, Elems_type_in_list, []),
	build_list(List_type, T, [[List] | Res]);
build_list(List_type, [{_Label, Type} | T], Res) ->
	build_list(List_type, T, [Type | Res]).

generalize_two_lists(List_type, List_type) ->
	List_type;

generalize_two_lists(List1, list) ->
	list;
generalize_two_lists(list, List2) ->
	list;

generalize_two_lists(undef_nonempty_maybe_improper_list, empty_list) ->
	undef_maybe_improper_list;
generalize_two_lists(empty_list, undef_nonempty_maybe_improper_list) ->
	undef_maybe_improper_list;

generalize_two_lists(undef_maybe_improper_list, _) ->
	undef_maybe_improper_list;
generalize_two_lists(_, undef_maybe_improper_list) ->
	undef_maybe_improper_list;

generalize_two_lists(undef_nonempty_maybe_improper_list, _) ->
	undef_nonempty_maybe_improper_list;
generalize_two_lists(_, undef_nonempty_maybe_improper_list) ->
	undef_nonempty_maybe_improper_list;

generalize_two_lists(maybe_improper_list, List2) when (List2 == non_empty_list) or (List2 == nonempty_improper_list) or (List2 == nonempty_maybe_improper_list) ->
	maybe_improper_list;
generalize_two_lists(List1, maybe_improper_list) when (List1 == non_empty_list) or (List1 == nonempty_improper_list) or (List1 == nonempty_maybe_improper_list)->
	maybe_improper_list;

generalize_two_lists(empty_list, nonempty_maybe_improper_list) ->
	maybe_improper_list;
generalize_two_lists(nonempty_maybe_improper_list, empty_list) ->
	maybe_improper_list;

generalize_two_lists(non_empty_list, empty_list) ->
	list;
generalize_two_lists(empty_list, non_empty_list) ->
	list;
generalize_two_lists(nonempty_improper_list, empty_list) ->
	maybe_improper_list;
generalize_two_lists(empty_list, nonempty_improper_list) ->
	maybe_improper_list;

generalize_two_lists(nonempty_maybe_improper_list, List2) when (List2 == non_empty_list) or (List2 == nonempty_improper_list) ->
	nonempty_maybe_improper_list;
generalize_two_lists(List1, nonempty_maybe_improper_list) when (List1 == non_empty_list) or (List1 == nonempty_improper_list) ->
	nonempty_maybe_improper_list;

generalize_two_lists(nonempty_improper_list, non_empty_list) ->
	nonempty_maybe_improper_list;	
generalize_two_lists(non_empty_list, nonempty_improper_list) ->
	nonempty_maybe_improper_list.


bound_cons_elems({List_type1, []}, _) ->
	[];

bound_cons_elems({List_type1, [{variable, [Value]} | Elems1]}, {defined_list, [{Type2, Value2} | Elems2]}) ->
	[{Value, {Type2, Value2}} | bound_cons_elems({List_type1, Elems1}, {defined_list, Elems2})];
bound_cons_elems({List_type1, [{variable, [Value]} | Elems1]}, {list, [Elem2]}) ->
	[{Value, Elem2} | bound_cons_elems({List_type1, Elems1}, {list, [Elem2]})];

bound_cons_elems({List_type1, [{'...', [Value]} | Elems1]}, {defined_list, Elems2}) ->
	[{Value, {defined_list, Elems2}}];

bound_cons_elems({List_type1, [{'...', [Value]} | Elems1]}, {list, [{'...', [Value]} | Elems2]}) ->
	{Value, {list, [{any, []}]}};
bound_cons_elems({List_type1, [{'...', [Value]} | Elems1]}, {list, [Type2]}) ->
	[{Value, {list, [Type2]}}];
bound_cons_elems({List_type1, [Elem1 | Elems1]}, {defined_list, [Elem2 | Elems2]}) ->
	bound_cons_elems({List_type1, Elems1}, {defined_list, Elems2});
bound_cons_elems({List_type1, [Elem1 | Elems1]}, {list, [Elem2]}) ->
	bound_cons_elems({List_type1, Elems1}, {list, [Elem2]}).


are_matching_types(Type, Type) ->
	true;

are_matching_types({any, _Val1}, _Type2) ->
	true;
are_matching_types(_Type1, {any, _Val2}) ->
	true;

are_matching_types({number, _Val1}, {Type2, _Val2}) when ((Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) or (Type2 == float) or (Type2 == number)) ->
	true;
are_matching_types({Type1, _Val1}, {number, _Val2}) when ((Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) or (Type1 == float) or (Type1 == number)) ->
	true;

are_matching_types({Type1, [Value]}, {Type2, [Value]}) when is_number(Value) ->
	true;

are_matching_types({neg_integer, [Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({pos_integer, [Value]}, {Type2, []}) when (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({non_neg_integer, [Value]}, {Type2, []}) when (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({integer, [Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;

are_matching_types({Type1, []}, {neg_integer, [Value]}) when (Type1 == neg_integer) or (Type1 == integer) ->
	true;
are_matching_types({Type1, []}, {pos_integer, [Value]}) when (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) ->
	true;
are_matching_types({Type1, []}, {non_neg_integer, [Value]}) when (Type1 == non_neg_integer) or (Type1 == integer) ->
	true;
are_matching_types({Type1, []}, {integer, [Value]}) when (Type1 == neg_integer) or (Type1 == pos_integer) or (Type1 == non_neg_integer) or (Type1 == integer) ->
	true;

are_matching_types({neg_integer, [Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({pos_integer, [Value]}, {Type2, []}) when (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({non_neg_integer, [Value]}, {Type2, []}) when (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;
are_matching_types({integer, [Value]}, {Type2, []}) when (Type2 == neg_integer) or (Type2 == pos_integer) or (Type2 == non_neg_integer) or (Type2 == integer) ->
	true;	


are_matching_types({Type, [Value1]}, {Type, [Value2]}) when Value1 == Value2 ->
	true;
are_matching_types({Type, [Value]}, {Type, []}) when (Type == float) or (Type == atom) or (Type == boolean) or (Type == fun_expr) or (Type == implicit_fun) ->
	true;
are_matching_types({Type, []}, {Type, [Value]}) when (Type == float) or (Type == atom) or (Type == boolean) or (Type == fun_expr) or (Type == implicit_fun)->
	true;
are_matching_types({Type, []}, {Type, []}) when (Type == float) or (Type == atom) or (Type == boolean) or (Type == fun_expr) or (Type == implicit_fun)->
	true;

are_matching_types({variable, _Value}, Type2) ->
	true;
are_matching_types(Type1, {variable, _Value}) ->
	true;

are_matching_types({Type1, Vals1}, {Type2, Vals2}) when ((Type1 == defined_list) or (Type1 == list) or (Type1 == non_empty_list) or (Type1 == improper_list)) and
														((Type2 == defined_list) or (Type2 == list) or (Type2 == non_empty_list) or (Type2 == improper_list)) ->
	are_matching_lists({Type1, Vals1}, {Type2, Vals2});

are_matching_types(Type1, Type2) ->
	false.

are_matching_lists(List, List) ->
	true;
are_matching_lists({empty_list, []}, {list, Val}) ->
	true;
are_matching_lists({list, Val}, {empty_list, []}) ->
	true;
are_matching_lists(List1, List2) ->
	are_lists_elems_matching(List1, List2).


are_lists_elems_matching({Type1, []}, {Type2, []}) ->
	true;
are_lists_elems_matching({Type1, Elems1}, {non_empty_list, [{'...', _}]}) ->
	true;
are_lists_elems_matching({non_empty_list, [{'...', _}]}, {Type2, Elems2}) ->
	true;
are_lists_elems_matching({defined_list, [Elem1 | Elems1]}, {defined_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({defined_list, Elems1}, {defined_list, Elems2});

are_lists_elems_matching({defined_list, [Elem1 | Elems1]}, {non_empty_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({defined_list, Elems1}, {non_empty_list, Elems2});
are_lists_elems_matching({non_empty_list, [Elem1 | Elems1]}, {defined_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching({non_empty_list, Elems1}, {defined_list, Elems2});

are_lists_elems_matching({List1_type, [Elem1 | Elems1]}, {list, [Elem2]}) ->
	are_matching_types(Elem1, Elem2);
are_lists_elems_matching({list, [Elem1]}, {List2_type, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2);

are_lists_elems_matching({non_empty_list, [Elem1 | Elems1]}, {non_empty_list, [Elem2 | Elems2]}) ->
	are_matching_types(Elem1, Elem2) and are_lists_elems_matching(Elems1, Elems2);

are_lists_elems_matching({Type1, [Elem1 | Elems1]}, {Type2, []}) ->
	false;
are_lists_elems_matching({Type1, []}, {Type2, [Elem2 | Elems2]}) ->
	false.

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
	{defined_list, lists:reverse(Converted_values)};
convert_list_elems_in_basic_format_to_compound([{'...', Value}], Converted_values) ->
	{non_empty_list, lists:reverse([{'...', Value} | Converted_values])};
convert_list_elems_in_basic_format_to_compound([H | T], Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),
	convert_list_elems_in_basic_format_to_compound(T, [Converted_value | Converted_values]);
convert_list_elems_in_basic_format_to_compound(Value, Converted_values) ->
	Converted_value = convert_value_in_basic_format_to_compound(Value),
	Reversed_values = lists:reverse(Converted_values),
	{improper_list, Reversed_values ++ Converted_value}.

convert_tuple_elems_in_basic_format_to_compound([]) -> [];
convert_tuple_elems_in_basic_format_to_compound([H | T]) ->
	Converted_value = convert_value_in_basic_format_to_compound(H),
	[Converted_value | convert_tuple_elems_in_basic_format_to_compound(T)].

convert_value_in_basic_format_to_compound([]) -> 
	{empty_list, []};
convert_value_in_basic_format_to_compound({empty_list, []}) -> 
	{empty_list, []};
convert_value_in_basic_format_to_compound({'...', Value}) -> 
	{'...', Value};
convert_value_in_basic_format_to_compound({Type, []}) ->
	{Type, []};
convert_value_in_basic_format_to_compound(Value) when is_integer(Value)->
	{integer, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_float(Value) ->
	{float, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_boolean(Value) ->
	{boolean, [Value]};
convert_value_in_basic_format_to_compound(Value) when is_atom(Value) ->
	{atom, [Value]};
convert_value_in_basic_format_to_compound({variable, Value}) ->
	{variable, Value};
convert_value_in_basic_format_to_compound(Value) when is_list(Value) ->
	convert_list_elems_in_basic_format_to_compound(Value, []);
convert_value_in_basic_format_to_compound(Value) when is_tuple(Value) ->
	Tuple_elems_list = tuple_to_list(Value),
	{tuple, convert_tuple_elems_in_basic_format_to_compound(Tuple_elems_list)}.

convert_values_in_compound_format_to_basic([]) -> [];
convert_values_in_compound_format_to_basic({empty_list, []}) ->
	{empty_list, []};
convert_values_in_compound_format_to_basic([H | T]) ->
	[convert_value_in_compound_format_to_basic(H) | convert_values_in_compound_format_to_basic(T)];
convert_values_in_compound_format_to_basic(Value) ->
	convert_value_in_compound_format_to_basic(Value).

convert_value_in_compound_format_to_basic({empty_list, []}) -> 
	[];
convert_value_in_compound_format_to_basic({'...', Value}) -> 
	{'...', Value};
convert_value_in_compound_format_to_basic({Type, []}) ->
	{Type, []};
convert_value_in_compound_format_to_basic({Type, [Value]}) when is_integer(Type) or is_float(Type) or is_atom(Type) or is_boolean(Type) ->
	Value;
convert_value_in_compound_format_to_basic({variable, Value}) ->
	{variable, Value};
convert_value_in_compound_format_to_basic({List_type, Values}) when (List_type == defined_list) or (List_type == list) or (List_type == improper_list) or (List_type == non_empty_list) ->
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
		true     -> [Clause] = ?Query:exec(hd(Pat), ?Expr:clause()),
				    [{Clause, Pat}];
		possibly -> [Clause] = ?Query:exec(hd(Pat), ?Expr:clause()),
				 	[{Clause, Pat} | find_actual_clause(Pats, Pars)];
		false    -> find_actual_clause(Pats, Pars)
	end.	

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
compare_lists_elems([{'...', Value}], _, _) ->
	possibly;
compare_lists_elems(_, [{'...', Value}], _) ->
	possibly;
compare_lists_elems([], L2, _) ->
	false;
compare_lists_elems(L1, [], _) ->
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

extract_expr_vals([], _) -> [];
extract_expr_vals([{left, Left_cons_expr}, {right, Right_cons_expr}], Variables) ->
	Left_cons_expr_list = extract_expr_val(Left_cons_expr, Variables),
	Right_cons_expr_list = extract_expr_val(Right_cons_expr, Variables),

	%erlang:display(Right_cons_expr_list),
	%erlang:display(Left_cons_expr_list),

	case Right_cons_expr_list of
		{empty_list, []}    -> Left_cons_expr_list;
		{variable, [Value]} -> Left_cons_expr_list ++ [{'...', [Value]}];
		_             -> Left_cons_expr_list ++ Right_cons_expr_list
	end;
extract_expr_vals([H | T], Variables) ->

	case ?Expr:type(H) of 
		cons -> [construct_list_from_cons_expr(H, Variables) | extract_expr_vals(T, Variables)];
		list -> construct_list_from_list_expr(H, Variables) ++ extract_expr_vals(T, Variables);
		tuple -> [construct_tuple(H, Variables) | extract_expr_vals(T, Variables)];
		variable -> [define_var_value(H, Variables) | extract_expr_vals(T, Variables)];
		_        -> [?Expr:value(H) | extract_expr_vals(T, Variables)] 		
	end.

extract_expr_val(Expr, Variables) ->
	case ?Expr:type(Expr) of
		cons     -> construct_list_from_cons_expr(Expr, Variables);
		list     -> construct_list_from_list_expr(Expr, Variables);
		tuple    -> construct_tuple(Expr, Variables);
		variable -> define_var_value(Expr, Variables);
		_        -> ?Expr:value(Expr)
	end.

define_var_value(Var_expr, Variables) ->
	Var_name = ?Expr:value(Var_expr),
	Variable = find_variable_by_name(Var_name, Variables),

	case Variable of
		[] -> {variable, [Var_name]};
		[{Var_name, Type}] -> convert_value_in_compound_format_to_basic(Type)
	end.

construct_tuple([], Variables) -> [];
construct_tuple(Tuple, Variables) ->
	Children = ?Query:exec(Tuple, ?Expr:children()),
	extract_expr_vals(Children, Variables).

construct_list_from_cons_expr(Cons, Variables) ->
	Children = ?Query:exec(Cons, ?Expr:children()),

	case length(Children) of
		0 -> {empty_list, []};
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
	erlang:display({test13, ei1, Test13 == [{defined_list,[{integer,[1]},{integer,[2]},{integer,[4]}]}]}),

	Test14 = infer_fun_type(unit_test, ei2, 0, []),
	erlang:display({test14, ei2, Test14 == [{defined_list,[{integer,[1]},{integer,[2]},{defined_list,[{integer,[1]},{integer,[2]},{integer,[3]}]}]}]}),

	Test15 = infer_fun_type(unit_test, ei3, 0, []),
	erlang:display({test15, ei3, Test15 == [{tuple,[{defined_list,[{integer,[1]},{integer,[2]}]},{defined_list,[{integer,[3]},{integer,[4]}]}]}]}),

	Test16 = infer_fun_type(unit_test, ei4, 0, []),
	erlang:display({test16, ei4, Test16 == [{defined_list,[{integer,[1]},{integer,[1]},{integer,[2]}]}]}),

	Test17 = infer_fun_type(unit_test, ei5, 0, []),
	erlang:display({test17, ei5, Test17 == [{improper_list,[{integer,[1]}|{integer,[2]}]}]}),

	Test18 = infer_fun_type(unit_test, ei6, 1, []),
	erlang:display({test18, ei6, Test18 == [{non_empty_list,[{integer,[1]}, {integer,[2]}, {integer,[3]}, {'...', ["A"]}]}]}),

	%Test19 = infer_fun_type(unit_test, pm, 0, []),
	%erlang:display({test19, pm, Test19 == [{integer,[3]}]}),

	%Test20 = infer_fun_type(unit_test, pm2, 0, []),
	%erlang:display({test20, pm2, Test20 == [{defined_list,[{integer,[1]},{integer,[2]}]}]}),

	%Generalization

	%Numbers

	T21 = c([1, {number, []}]),
	Test21 = g(T21),
	erlang:display({test21, Test21 == {non_empty_list, [{number, []}]}}),

	T22 = c([1, {number, []}]),
	Test22 = g(T22),
	erlang:display({test22, Test22 == {non_empty_list, [{number, []}]}}),

	T23 = c([1,2,3]),
	Test23 = g(T23),
	erlang:display({test23, Test23 == {non_empty_list,[{union,[{integer,[1]},
                         {integer,[2]},
                         {integer,[3]}]}]}}),

	T24 = c([1,2,3.5]),
	Test24 = g(T24),
	erlang:display({test24, Test24 == {non_empty_list, [{number, []}]}}),

	T25 = c([1.1, 1.2, 3]),
	Test25 = g(T25),
	erlang:display({test25, Test25 == {non_empty_list, [{number, []}]}}),

	%Booleans
	T26 = c([true, false]),
	Test26 = g(T26),
	erlang:display({test26, Test26 == {non_empty_list, [{boolean, []}]}}),

	T27 = c([false, false]),
	Test27 = g(T27),
	erlang:display({test27, Test27 == {non_empty_list, [{boolean, [false]}]}}),

	T28 = c([true, true]),
	Test28 = g(T28),
	erlang:display({test28, Test28 == {non_empty_list, [{boolean, [true]}]}}),

	T29 = c([{boolean, []}, true]),
	Test29 = g(T29),
	erlang:display({test29, Test29 == {non_empty_list, [{boolean, []}]}}),

	T30 = c([ok, error]),
	Test30 = g(T30),	
	erlang:display({test30, Test30 == {non_empty_list, [{union, [{atom, [ok]}, {atom, [error]}]}]}}),

	T31 = c([1,2, []]),
	Test31 = g(T31),
	erlang:display({test31, Test31 == {non_empty_list,[{union,[
						 {integer,[1]},
                         {integer,[2]},
                         {empty_list, []}
                    ]}]}}),

	T32 = c([[1,2,3], [ok, error]]),
	Test32 = g(T32),
	erlang:display({test32, Test32 == {non_empty_list,
									    [{non_empty_list,
									         [{union,
									              [{integer,[1]},
									               {integer,[2]},
									               {integer,[3]},
									               {atom,[ok]},
									               {atom,[error]}]}]}]}}),

	T33 = c([[1,2,3], [ok, true], []]),
	Test33 = g(T33),	
	erlang:display({test33, Test33 == {non_empty_list,
										[{list,
											[{union,[{boolean,[true]},{integer,[1]},{integer,[2]},{integer,[3]},{atom,[ok]}]}]}]}}),

	T34 = c([[1,2 | 3], [4,5 | 6]]),
	Test34 = g(T34),	
	erlang:display({test34, Test34 == {non_empty_list,
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
	erlang:display({test38, Test38 == {non_empty_list,[{union,[{atom,[ok]},
                         				{undef_nonempty_maybe_improper_list,[]}]}]}}).


g(List) -> 
	{Res, _} = generalize_list_type(List, []),
	Res.

c(Value) ->
	convert_value_in_basic_format_to_compound(Value).














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
-module(refined_genspec).

%------TODO list----------------
%1)Process guard expressions(В разделе "Defining actual clauses")
%2)Process fun expressions  (В разделе "Defining actual clauses")
%3)Добавить проверку, что если паттерн абсолютно совпадает с actual parameters, не проверять дальше.
%4)Функция get_fun_name не обрабатывает случай, когда можду именем функции и скобками есть пробелы.
%5)Добавить ":" d infix expressions.
-include("user.hrl").
-include("spec.hrl").

-compile(export_all).

test_expr_inference(Mod_name, Fun_name, Arity) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	lists:map(fun(Clause) -> get_clause_type(Clause) end, Clauses).

get_clause_type(Clause) ->
	Bodies = get_bodies(Clause),
	define_bodies_type(Bodies, []).

define_bodies_type([], _) -> [];
define_bodies_type([Last_body], Variables) ->
	infer_expr_inf(Last_body, Variables);
define_bodies_type([Body | Bodies], Variables) ->
	Body_type = infer_expr_inf(Body, Variables),
	%erlang:display(Body_type),

		case Body_type of
			{_Var_name, {_Type, _Value}} -> define_bodies_type(Bodies, [Body_type | Variables]);
			_                         -> define_bodies_type(Bodies, Variables)
		end.


test_finding_actual_clauses(Mod_name, Fun_name, Arity) ->
	Fun_node = get_fun_node(Mod_name, Fun_name, Arity),
	Applications = get_applications(Fun_node),
	Application  = hd(Applications), %--------------------------------for testing
	Actual_params = get_actual_params(Application),
	%[?Expr:type(Actual_param) || Actual_param <- Actual_params]. %--------------------------------for testing
	Fun_def = get_fundef(Fun_node),
	Clauses = get_clauses(Fun_def),
	Patterns = [get_patterns(Clause) || Clause <- Clauses],

	case Actual_params of
		[] -> 	Fun_def = Fun_def,
				get_clauses(Fun_def);
		_  ->   find_actual_clause(Patterns, Actual_params)   
	end.
%	lists:map(fun(Clause) -> get_clause_type(Clause) end, Actual_clause).

%---------------------------------Inference part-----------------------------------------------

infer_expr_inf(Expr, Variables) ->
	case ?Expr:type(Expr) of
		prefix_expr -> infer_prefix_expr_type(Expr, ?Expr:value(Expr), Variables);
		match_expr -> infer_match_expr_inf(Expr, Variables);
		infix_expr -> infer_infix_expr_type(Expr, ?Expr:value(Expr), Variables);
		variable   -> Var = lists:filter(fun({V, _}) -> ?Expr:value(Expr) == V end, Variables),
					  %erlang:display(Var),	
					  case Var of 
					  	[] -> {any, []};
					  	[{_V, {Type, Val}}] -> {Type, Val}
					  end;
		parenthesis -> infer_parenthesis_inf(Expr, Variables);
		application -> get_fun_app_type(Expr);
		Simple_type    -> {Simple_type, [?Expr:value(Expr)]}
	end.

get_fun_app_type(Fun_app) ->
	[Expr, Arglist] = ?Query:exec(Fun_app, ?Expr:children()),
	[Module, Fun] = 
		case ?Expr:value(Expr) of
			':' -> ?Query:exec(Expr, ?Expr:children());
			_   -> [4, 5]
		end,

	Args = ?Query:exec(Arglist, ?Expr:children()),
	Arity = length(Args),
	Module_name = ?Expr:value(Module),
	Fun_name = ?Expr:value(Fun),
	{_, [Return_type]} = spec_proc:get_spec_type(Module_name, Fun_name, Arity),
	Return_type.

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
%Добавить проверку на правильность типа	
	compute_infix_expr(Expr_inf1, Expr_inf2, Operation).

infer_prefix_expr_type(Expr, Operation, Variables) ->
	[Sub_expr] = ?Query:exec(Expr, ?Expr:children()),
	Sub_expr_inf = infer_expr_inf(Sub_expr, Variables),
	compute_prefix_expr(Sub_expr_inf, Operation).

compute_prefix_expr({Type, [Value]}, '-') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) ->
	{Type, [-Value]};
compute_prefix_expr({Type, []}, '-') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == number) or (Type == any) ->
	{Type, []};

compute_prefix_expr({Type, [Value]}, 'bnot') when (Type == integer) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) ->
	if
		Value < 0 -> {Type, [bnot (Value)]};
		true         -> {Type, [bnot (Value)]}
	end;
compute_prefix_expr({Type, []}, 'bnot') when (Type == integer) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == number) or (Type == any) ->
	{Type, []};

compute_prefix_expr({_Type, _Value}, _Operation) ->
	{none, []}.


compute_infix_expr({float, [Value1]}, {Type, [Value2]}, '+') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 + Value2]};
compute_infix_expr({Type, [Value1]}, {float, [Value2]}, '+') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 + Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '+') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer) or (Type2 == any)) ->
	{integer, [Value1 + Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '+') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer) or (Type2 == any))  and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer)) ->
	{integer, [Value1 + Value2]};
compute_infix_expr({any, _Value1}, {any, _Value2}, '+') ->
	{number, []};


compute_infix_expr({float, [Value1]}, {Type, [Value2]}, '-') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 - Value2]};
compute_infix_expr({Type, [Value1]}, {float, [Value2]}, '-') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 - Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '-') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer) or (Type2 == any)) ->
	{integer, [Value1 - Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '-') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer) or (Type2 == any))  and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer)) ->
	{integer, [Value1 - Value2]};
compute_infix_expr({any, _Value1}, {any, _Value2}, _Operation) ->
	{number, []};


compute_infix_expr({float, [Value1]}, {Type, [Value2]}, '*') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 * Value2]};
compute_infix_expr({Type, [Value1]}, {float, [Value2]}, '*') when (Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == any) ->
	{float, [Value1 * Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '*') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer) or (Type2 == any)) ->
	{integer, [Value1 * Value2]};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '*') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer) or (Type2 == any))  and
														       ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer)) ->
	{integer, [Value1 * Value2]};


compute_infix_expr(_Expr1, {_Type2, [0]}, '/') -> 
	{none, []};	
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, '/') when ((Type1 == integer) or (Type1 == float) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
															       ((Type2 == integer) or (Type2 == float) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer))
	-> {float, [Value1 / Value2]};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, '/') when ((Type1 == number) or (Type1 == integer) or (Type1 == float) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer) or (Type1 == any)) and
													   ((Type2 == number) or (Type2 == integer) or (Type2 == float) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer) or (Type1 == any))
	-> {float, []};

compute_infix_expr(_Expr1, {_Type2, [0]}, 'div') ->
	{none, []};
compute_infix_expr({Type1, [Value1]}, {Type2, [Value2]}, 'div') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
															         ((Type2 == integer) or (Type2 == float) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer))
	-> {integer, [Value1 div Value2]};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, 'div') when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) and
															         ((Type2 == integer) or (Type2 == float) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer))
	-> {integer, []};


compute_infix_expr({float, _Value1}, {Type, _Value2}, _Operation) when ((Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == number) or (Type == any))																	
	-> {float, []};
compute_infix_expr({Type, _Value1}, {float, _Value2}, _Operation) when ((Type == integer) or (Type == float) or (Type == non_neg_integer) or (Type == pos_integer) or (Type == neg_integer) or (Type == number) or (Type == any))
	-> {float, []};


compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, _Operation) when  ((Type1 == any) or (Type1 == number)) and 
														                ((Type2 == number) or (Type2 == integer) or (Type2 == float) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer) or (Type2 == any)) 
	-> {number, []};
compute_infix_expr({Type1, _Value1}, {Type2, _Value2}, _Operation) when  ((Type2 == any) or (Type2 == number)) and
														                ((Type1 == number) or (Type1 == integer) or (Type1 == float) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer) or (Type1 == any))
	-> {number, []};	


compute_infix_expr({integer, _Value1}, {Type2, _Value2}, _Operation) when ((Type2 == integer) or (Type2 == non_neg_integer) or (Type2 == pos_integer) or (Type2 == neg_integer)) ->
	{integer, []};
compute_infix_expr({Type1, _Value1}, {integer, _Value2}, _Operation) when ((Type1 == integer) or (Type1 == non_neg_integer) or (Type1 == pos_integer) or (Type1 == neg_integer)) ->
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
	Res = compare_expressions(Pat, Pars),
	case Res of 
		true  -> [?Query:exec(hd(Pat), ?Expr:clause())];
		possibly -> [?Query:exec(hd(Pat), ?Expr:clause()) | find_actual_clause(Pats, Pars)];
		false -> find_actual_clause(Pats, Pars)
	end.	

compare_expressions(Pats, Pars) ->
	Res = compare_elems(Pats, Pars),
	conclude(Res, true).

compare_elems([], []) -> [];
compare_elems([Pat | Pats], [Par | Pars]) ->
	Param_type = ?Expr:type(Par),
	Pat_type = ?Expr:type(Pat),

	case {Param_type, Pat_type} of
		{cons, cons}     -> case compare_cons(Pat, Par) of
						   		true     -> [true | compare_elems(Pats, Pars)];
						   		possibly -> [possibly | compare_elems(Pats, Pars)];
								false -> [false]
							end;
		{tuple, tuple} -> case compare_tuples(Pat, Par) of
						   		true -> [true | compare_elems(Pats, Pars)];
						   		possibly -> [possibly | compare_elems(Pats,Pars)];
								false -> [false]
							end;
		{_, variable}    -> [possibly | compare_elems(Pats, Pars)];
		{variable, _}    -> [possibly | compare_elems(Pats, Pars)];
		_                -> case compare_simple_type(Pat, Par) of
								true  -> [true | compare_elems(Pats, Pars)];
								false -> [false]
							end
	end.

compare_tuples(T1, T2) when length(T1) == length(T2) ->
	Children1 = ?Query:exec(T1, ?Expr:children()),
	Children2 = ?Query:exec(T2, ?Expr:children()),

	compare_expressions(Children1, Children2);
compare_tuples(_T1, _T2) ->
	false.

compare_cons(Con1, Con2) ->
	Children1 = construct_list_from_cons_expr(Con1),
	Children2 = construct_list_from_cons_expr(Con2),
	%erlang:display(Children1),
	%erlang:display(Children2),
	Res = compare_lists_elems(Children1, Children2),
	conclude(Res, true).

conclude([], Status) ->
	Status;
conclude([false | _T], _) ->
	false; 
conclude([possibly | T], _Status) ->
	conclude(T, possibly);
conclude([true | T], possibly) ->
	conclude(T, possibly);
conclude([H | T], _) ->
	conclude(T, H).

compare_lists_elems([], []) ->
	[true];
compare_lists_elems([any  | T1], [_H2 | T2]) ->
	[possibly | compare_lists_elems(T1, T2)];
compare_lists_elems([_H1  | T1], [any | T2]) ->
	[possibly | compare_lists_elems(T1, T2)];
compare_lists_elems([], ['...'])  ->
	[possibly];
compare_lists_elems(['...'], [])  ->
	[possibly];
compare_lists_elems(['...'], ['...'])  ->
	[possibly];
compare_lists_elems(_, [])  ->
	[false];
compare_lists_elems([], 	_)  ->
	[false];
compare_lists_elems(['...'], _) ->
	[possibly];
compare_lists_elems(_, ['...']) ->
	[possibly];
compare_lists_elems([H1 | T1], [H2 | T2]) ->
	case H1 == H2 of
		true -> [true | compare_lists_elems(T1, T2)];
		false -> [false]
	end.

construct_list_from_cons_expr(Cons) ->
	Children = ?Query:exec(Cons, ?Expr:children()),
	lists:flatten(extract_expr_vals(Children)).

extract_expr_vals([]) -> [];
extract_expr_vals([H | T]) ->
	case ?Expr:type(H) of
		list     -> [constract_list_from_list_expr(H) | extract_expr_vals(T)];
		cons     -> [construct_list_from_cons_expr(H) | extract_expr_vals(T)];
		variable -> case T of
						[] -> ['...' | extract_expr_vals(T)];
						_  -> [H | extract_expr_vals(T)]
				    end;
		_        -> [?Expr:value(H) | extract_expr_vals(T)] 
	end.

constract_list_from_list_expr([]) -> [];
constract_list_from_list_expr(L) ->
	Children = ?Query:exec(L, ?Expr:children()),
	extract_expr_vals(Children).

compare_simple_type(Pat, Par) ->
	?Expr:value(Pat) =:= ?Expr:value(Par).

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
-module(unit_test).
-compile(export_all).

%Anonymus functions
af1() ->
	A = 5,
	Af = fun(A, B) -> A + B end,
	Af(300, A).

af2() ->
	Af = fun(B, C) -> B + C end,
	af2_2(Af, 3, 4).

af2_2(Fun, A, B) ->
	Fun(A, B).

af3() ->
	Af = fun sum/2,
	Af(1,2).

af3_2() ->
	%Для данного теста нужно создать модуль external_module и добавить функцию sum
	Af = fun unit_test2:sum2/2,
	Af(1,2).

af3_3() ->
	%Для данного теста нужно создать модуль external_module и добавить функцию sum со спецификацией
	Af = fun unit_test2:sum/2,
	Af(1,2).

af4() ->
	fun(B, C) -> B + C end.

af4_2() ->
	A = af4(),
	A(1,2).

sum(A, B) ->
	A + B.

%Looking for actual claueses

lfac([H | _T]) ->
	H.

lfac_2() ->
	lfac([1,2]).

lfac2([1,2,3]) ->
	ok.

lfac2_2() ->
	lfac2([1,2,3]).

lfac3([1,2,3,4]) ->
	ok.

lfac3_3(A) ->
	lfac3([1, 2 | A]).

lfac4([[1,2,3,4] | A]) ->
	ok.

lfac4_4() ->
	lfac4([[1,2,3,4],55]).

lfac5([1,2,3 | [4,5,6]]) ->
	ok.

lfac5_5() ->
	lfac5([1,2,3,4,5,6]).	

lfac6([[1,2,3] | [4,5,6]]) ->
	ok.

lfac6_6() ->
	lfac6([[1,2,3] | [4,5,6]]).

lfac7([1,2,3 | 4]) ->
	ok.

lfac7_7() ->
	lfac7([1,2,3 | 4]).

%Elems insertion
ei1() ->
	A = 4,
	[1,2,A].

ei2() ->
	A = [1,2,3],
	[1,2,A].

ei3() ->
	A = [1,2],
	B = [3,4],
	{A, B}.

ei4() ->
	A = [1,2],
	[1 | A].

ei5() ->
	A = 1,
	[A | 2].
	
ei6(A) ->
	[1,2,3 | A].

%Pattern matching tests

pm() ->
	B = [1,2,3],
	[A, C, 3] = B,
	A + C.

pm2() ->
	A = 5,
	[A | B] = [5, 1, 2],
	B.	

%Cons bounding 

cons_bound(A) ->
	[B, 1, 2] = A,
	B.

cons_bound2(A) ->
	B = [A],
	[C, 1, 2] = B,
	C.

cons_bound3(A) ->
	B = A + 2,
	C = [[B], 1, 2],
	[[D], 1, 2] = C,
	D.

cons_bound4() -> 
	B = [[2],1 | 3],
	[[C], 1 | 3] = B,
	C.

cons_bound5() -> 
	B = [[[87]], 3,4],
	[[[C]], 3, 4] = B,
	C.

cons_bound6() -> 
	A = [1,2 | 3],
	[1,2 | B] = A,
	B.

cons_bound7() -> 
	A = [1,2, 3],
	[1,2 | B] = A,
	B.

cons_bound8() -> 
	A = [1,2 | 3],
	[B,2 | 3] = A,
	B.

cons_bound9() ->
	A = [{1,2,3}, 4,5],
	[{B, C, D}, 4,5] = A,
	{B, C, D}.

cons_bound10() -> 
	A = [{1,2}, {3,4,5}, 6],
	[{1,2}, {B, C, D}, 6] = A,
	{B, C, D}.


%Tuple bounding
tuple_bound() -> 
	A = {1,2,3},
	{B, 2, 3} = A,
	B.

tuple_bound2() ->
	A = {[1],2,3},
	{[B], 2, 3} = A,
	B.

tuple_bound3() ->
	A = {{4,5},2,3},
	{{B,C}, 2, 3} = A,
	{B, C}.

tuple_bound4(R) -> 
	A = {{R,5},2,3},
	{{B,C}, 2, 3} = A,
	{B, C}.

match_expr(A) -> 
	4 = A,
	A.

%Clause matching 

cl_mat() ->
	A = {1,2,{1,2,3}},
	cl_mat_hp(A, da).

cl_mat_hp(ok, da) ->
	ok;
cl_mat_hp({1, 2, C}, net) ->
	error;
cl_mat_hp({A, B, C}, da) ->
	horoso.


cl_mat2(A) -> 
	A = 2,
	cl_mat_hp2(A, 7).

cl_mat_hp2(A, 4) ->
	ok;
cl_mat_hp2(Var1, A) when A == 7 ->
	eror.


cl_mat3(A) -> 
	Var1 = 2,
	cl_mat_hp3(Var1, 7).

cl_mat_hp3(A, 7) when A > 1 ->
	ok;
cl_mat_hp3(Var1, A) when A == 7 ->
	eror.


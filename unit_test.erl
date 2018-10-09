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

lfac([H | T]) ->
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
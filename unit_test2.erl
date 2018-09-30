-module(unit_test2).
-compile(export_all).

-spec sum(number(), number()) -> number().

sum(A, B) ->
	A + B.

sum2(A, B) ->
	A + B.
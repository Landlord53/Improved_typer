-module(spec_test).
-compile(export_all).

-spec sum(number(), number()) -> number().

sum(A, B) ->
	A + B.

sum2(A, B) ->
	A + B.
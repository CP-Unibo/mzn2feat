include "atleast.mzn";

predicate at_least(int: n, array[int] of var int: x, int: v);

predicate at_least(int: n, array[int] of var set of int: x, set of int: v);


include "atmost.mzn";

predicate at_most(int: n, array[int] of var int: x, int: v);

predicate at_most(int: n, array[int] of var set of int: x, set of int: v);


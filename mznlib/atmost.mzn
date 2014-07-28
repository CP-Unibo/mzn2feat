include "at_most.mzn";

predicate atmost(int: n, array[int] of var int: x, int: v);

predicate atmost(int: n, array[int] of var set of int: x, set of int: v);


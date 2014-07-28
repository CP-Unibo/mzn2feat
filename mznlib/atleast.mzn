include "at_least.mzn";

predicate atleast(int: n, array[int] of var int: x, int: v);

predicate atleast(int: n, array[int] of var set of int: x, set of int: v);


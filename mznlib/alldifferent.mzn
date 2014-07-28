include "all_different.mzn";

predicate alldifferent(array[int] of var int: x);

predicate alldifferent(array[int] of var set of int: x);


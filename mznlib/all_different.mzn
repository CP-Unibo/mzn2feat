include "alldifferent.mzn";

predicate all_different(array[int] of var int: x);

predicate all_different(array[int] of var set of int: x);


include "count.mzn";

predicate count_eq(array[int] of var int: x, var int: y, var int: c);

predicate count_reif(
  array[int] of var int: x, var int: y, var int: c, var bool: b
);

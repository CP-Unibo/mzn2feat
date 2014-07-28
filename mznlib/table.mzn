predicate table(array[int] of var bool: x, array[int, int] of bool: t);

predicate table(array[int] of var int: x, array[int, int] of int: t);

predicate table_reif(
  array[int] of var bool: x, array[int, int] of bool: t, var bool: b
);

predicate table_reif(
  array[int] of var int: x, array[int, int] of int: t, var bool: b
);

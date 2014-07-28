%-----------------------------------------------------------------------------%
% Requires that a set of tasks given by start times 's' and durations 'd' only
% run in sequence.  Tasks of duration zero cannot begin running in the middle
% of another task.
% Assumptions:
% - forall i, d[i] >= 0
%-----------------------------------------------------------------------------%

predicate disjunctive(array[int] of var int: s, array[int] of var int: d) =
    assert(index_set(s) == index_set(d),
         "disjunctive: 1st and 2nd arguments must have the same index set",
    assert(lb_array(d) >= 0,
         "disjunctive: durations must be non-negative",
    forall(i, j in index_set(s) where i < j)
        (s[i] + d[i] <= s[j] \/  s[j] + d[j] <= s[i])
    ));

%-----------------------------------------------------------------------------%

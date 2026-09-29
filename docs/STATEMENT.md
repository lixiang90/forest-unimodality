# Correspondence to the original problem

`ForestUnimodality.CompleteTarget` quantifies over every natural number `n` and
every `SimpleGraph (Fin n)`. Its only graph hypothesis is `G.IsAcyclic`.
The definition has no connectivity, positive-order, bounded-order or numerical
certificate hypothesis. Empty forests, isolated vertices and disconnected
forests are included. Labelling a finite vertex set by `Fin n` preserves adjacency
and independent-set cardinalities; this is the mathematical representation
argument, not a claim that a separate relabelling lemma has been checked here.

`independentCount G k` counts all independent subsets with exactly `k` vertices.
It does not count only maximal or maximum independent sets, and does not quotient
by graph isomorphism. `WeaklyUnimodal` permits a plateau: for some natural `p`,
the sequence is nondecreasing before `p` and nonincreasing from `p` onward.
The zero tail beyond `n` is included.

The required unconditional declaration is
`ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`.
The `checks/SubmissionCheck.lean` entry explicitly checks that type and prints
the transitive axioms of all four final declarations.

The assembly uses separate small, middle and large order arguments. Its two
finite-domain premises must be discharged by `Completed.rectangles_valid` and
`Completed.parents_valid`. Intermediate conditional theorems and coverage counts
alone do not establish the final result.

This explanation follows the reviewed development definitions. The publication
contains a candidate final declaration from the reviewed template; its actual
compilation and complete portable reproduction remain pending. This explanation
is not a proof-acceptance report.

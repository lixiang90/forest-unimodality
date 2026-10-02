# Proof simplification workstream

Branch: `simplify-proof-20261003`.

The starting point is evidence commit `7237cc8d9fe6adba65e8a3e4dd6f4b518bf2e15d`, whose proof sources are the fully checked snapshot `fc5696dbd7a5d708c0bf32755b9027031e6a19e0`. Published verification results for that snapshot remain historical evidence. The simplification branch is a new candidate; its full downstream closure must be rebuilt before updating the awards submission's selected proof commit.

## First experiment: constant certificate functions

Generated rational coefficient functions sometimes branch on an index while returning exactly the same literal in every branch. For example:

```lean
fun i => if i.val = 0 then (7/11) else if i.val = 1 then (7/11) else (7/11)
```

can be written as:

```lean
fun _ => (7/11)
```

The equality follows from function extensionality and `ite_self`. No certificate numbers, inequalities, theorem statements or proof methods are changed. The existing `decide +kernel` checks are retained.

`scripts/simplify_constant_lambdas.py` recognizes only the generated syntax with identical rational literals, preserves other bytes, and defaults to a dry run. It deliberately leaves distinct spellings such as `1/2` and `2/4` alone. Unit checks cover unequal branches, nonliteral expressions, negative rationals, byte preservation and idempotence.

The first changed module is `ForestUnimodality.Stage80MessageSourceData.Case005.Batch018`: 1,440 redundant branching functions removed, reducing source size from 1,476,009 to 1,201,765 bytes (18.58%). Its candidate source-manifest entry is updated; the final statement and theorem source remain unchanged.

## Validation

- Python transformation tests: `python scripts/test_simplify_constant_lambdas.py`.
- Candidate source identity: `python scripts/verify.py --candidate --source-only` passed for all 31,598 module hashes and the dependency closure; it does not run Lean. [Receipt](../verification/simplification-20261003/source-identity.json).
- Cloud experiment: generic Lean equality check followed by a paired original/simplified module compilation, using Lean 4.32.2, one Lean thread per job, and verified imports from the completed benchmark. Outputs go into a separate experimental directory. This is a module-level test, not a full downstream rebuild.

Both module compilations and the generic Lean equality check passed. Each module's `cells_checked` axiom report contains exactly `propext`, `Classical.choice`, and `Quot.sound`. [Recorded results](../verification/simplification-20261003/pilot-results.json).

| Metric | Original | Simplified |
| --- | ---: | ---: |
| Source bytes | 1,476,009 | 1,201,765 |
| Wall time (seconds) | 256.248 | 243.673 |
| Peak RSS (KiB) | 8,339,924 | 8,178,676 |
| Object bytes | 21,959,488 | 22,153,312 |

This one paired run observed 4.91% lower wall time and 1.93% lower peak RSS, but 0.88% larger compiled output. Both jobs ran concurrently on the same server with cached imports. It is an exploratory measurement, not an estimate of full-project speedup. Source compression is established; aggregate runtime and downstream compatibility still require broader validation.

## Remaining Stage80 compression opportunity

A read-only scan of the branch found another **2,294 modules** with **3,157,563** redundant constant-branch functions. Their combined source size could decrease from **2,310,421,985** to **1,737,750,154 bytes**, saving **572,671,831 bytes (546.14 MiB)**. These files have not been modified or recompiled. This scan predicts source-size reduction only, not runtime improvement. [Scan summary](../verification/simplification-20261003/stage80-dry-run-summary.json).

## Next steps

1. Use the paired module result to decide whether to expand constant-function compression across generated Stage80 modules.
2. Investigate repeated certificate subexpressions and opportunities to share them without adding axioms or weakening kernel verification.
3. Rebuild changed modules and all dependent modules with a refreshed candidate manifest, then run the final target and axiom check and evidence audit.
4. Keep the accepted baseline and awards submission pinned to the existing proof until the simplified candidate completes that validation.

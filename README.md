# Forest independence polynomial unimodality

Independent Lean formalization project for **JSP-000826 / Erdős 993**.

**Complete Lean compilation and final verification passed.** All **31,598 project
modules**, the final statement and axiom checks, and the separate evidence audit
passed for proof commit
[`fc5696dbd7a5d708c0bf32755b9027031e6a19e0`](https://github.com/lixiang90/forest-unimodality/tree/fc5696dbd7a5d708c0bf32755b9027031e6a19e0).
The final theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

A subsequent clean project build reused **zero project objects** and passed the
same final checks and evidence audit on October 2, 2026. On **2 x AMD EPYC 7B12
(128 physical cores / 256 threads), 503.65 GiB RAM**, it took **8 h 57 min 28.828 s**
including preparation, final checks and audit; module compilation took
**8 h 50 min 34.742 s**. Lean and external dependency caches were reused.
See the [completed build and audit report](verification/benchmark-128x64-20261002/REPORT.md)
and [final axiom log](verification/benchmark-128x64-20261002/final-target.log).
The evidence audit verifies identities, hashes, module results and dependency
closure; it is separate from compilation and does not perform another kernel replay.

The formalization is submitted in [awards PR #4631](https://github.com/TheJustinSunPrize/awards/pull/4631).
Organizer acceptance, eligibility and award decisions remain separate from these
completed machine checks. Proof simplification experiments are maintained on
`simplify-proof-20261003` and do not replace this verified proof snapshot.

The target is weak unimodality of the numbers of independent vertex sets of each
size in every finite forest, including empty and disconnected forests and
isolated vertices. The verified final theorem is
`ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`.

The mathematical reference is Tong Zhang's *Exact Certificates for Unimodality
of Forest Independence Polynomials*, September 26 version at commit
[`7cee5104a983dd1271db14be7606e96c504aa370`](https://github.com/zhangzenozhang-jpg/-forest-unimodality-proof/blob/7cee5104a983dd1271db14be7606e96c504aa370/paper/forest_unimodality_Tong_Zhang.pdf).
This project concerns formalization, not a claim to that mathematical discovery.
See [attribution](docs/ATTRIBUTION.md) for the version and contribution boundaries.

- [Reproduction instructions and current limitations](docs/REPRODUCING.md)
- [Statement correspondence](docs/STATEMENT.md)
- [Submission checklist](docs/SUBMISSION.md)
- [Awards submission and verification status](docs/AWARDS_PR_DRAFT.md)
- [Machine-readable preparation status](submission-status.json)
- [Resource observations and verification scope](docs/RESOURCE_REQUIREMENTS.md)

Lean is pinned to `leanprover/lean4:v4.32.2`; mathlib is pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`. The committed dependency manifest
records all nine external revisions. External dependencies and generated proof
objects are excluded from this repository.

Run `python scripts/verify.py --candidate --source-only` to check the recorded
source identity. The `--candidate` flag and development-manifest filename are
retained from the original publication tooling; this source-only command does
not run Lean. Completed compilation, final checks and audit are documented in
the linked verification report. The historical reproduction guide describes the
project's pinned toolchain and build commands.

Published and maintained through the `lixiang90` account, with substantial OpenAI
Codex assistance in formalization, implementation and checking. Mathematical
source credit is recorded separately. The distribution license remains
unspecified; no independent human verification or identity verification is claimed.

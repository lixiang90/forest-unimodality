# Forest independence polynomial unimodality

Independent Lean formalization project for **JSP-000826 / Erdős 993**.

**Development snapshot: final verification pending.** This repository publishes
the current candidate source closure while its final integration compilation is
still running. The final declaration is a proof candidate, not an accepted proof.
No complete formalization, successful full reproduction, organizer acceptance,
award eligibility or priority determination is claimed.

The publication snapshot includes `Completed.lean` materialized from the reviewed
generator template and an umbrella import of that candidate. These two publication
changes do not alter the live compiler's inputs or claim that the development
generator's acceptance gates passed. All other included Lean files are copied
byte-for-byte from the recorded development snapshot. Details are in
`verification/development-source-manifest.json`.

The target is weak unimodality of the numbers of independent vertex sets of each
size in every finite forest, including empty and disconnected forests and
isolated vertices. The planned final theorem is
`ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`.

The mathematical reference is Tong Zhang's *Exact Certificates for Unimodality
of Forest Independence Polynomials*, September 26 version at commit
[`7cee5104a983dd1271db14be7606e96c504aa370`](https://github.com/zhangzenozhang-jpg/-forest-unimodality-proof/blob/7cee5104a983dd1271db14be7606e96c504aa370/paper/forest_unimodality_Tong_Zhang.pdf).
This project concerns formalization, not a claim to that mathematical discovery.
See [attribution](docs/ATTRIBUTION.md) for the version and contribution boundaries.

- [Reproduction instructions and current limitations](docs/REPRODUCING.md)
- [Statement correspondence](docs/STATEMENT.md)
- [Submission checklist](docs/SUBMISSION.md)
- [Draft awards PR](docs/AWARDS_PR_DRAFT.md)
- [Machine-readable preparation status](submission-status.json)
- [Resource observations and verification scope](docs/RESOURCE_REQUIREMENTS.md)

Lean is pinned to `leanprover/lean4:v4.32.2`; mathlib is pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c`. The committed dependency manifest
records all nine external revisions. External dependencies and generated proof
objects are excluded from this repository.

Run `python scripts/verify.py --candidate --source-only` to check candidate source
identity. This does not compile or certify a theorem. The default accepted-source
mode deliberately refuses this unaccepted snapshot. Candidate full reproduction
instructions are in `docs/REPRODUCING.md`.

Published and maintained through the `lixiang90` account, with substantial OpenAI
Codex assistance in formalization, implementation and checking. Mathematical
source credit is recorded separately. The distribution license remains
unspecified; no independent human verification or identity verification is claimed.

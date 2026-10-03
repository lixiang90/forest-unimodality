# Awards submission — completed Lean verification

The formal submission is [PR #4631](https://github.com/TheJustinSunPrize/awards/pull/4631).
This file replaces the pre-verification draft text.

## Contribution and fixed source

- **JSP-000826 / Erdős 993:** weak unimodality of independent-set counts of every
  finite forest, including empty forests, disconnected forests and isolated vertices.
- Contribution: an independent, AI-assisted Lean formalization.
- Repository: https://github.com/lixiang90/forest-unimodality, branch `main`.
- Verified proof commit: **`fc5696dbd7a5d708c0bf32755b9027031e6a19e0`**.
- Specification: `ForestUnimodality.CompleteTarget` in `ForestUnimodality/Statement.lean`.
- Verified theorem: `ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`.
- Final statement and axiom check: `checks/SubmissionCheck.lean`.

## Completed verification

**31,598 / 31,598 project modules compiled successfully.** The final theorem and
all four checked final declarations report exactly `propext`, `Classical.choice`,
and `Quot.sound`. The separate evidence audit passed, checking source and dependency
identities, module results, source/output/log hashes, dependency closure and the
final check. It does not perform a second kernel replay.

The initial campaign reused 6,907 hash-audited modules across machines. A subsequent
clean project build on the high-memory server compiled all 31,598 modules with
**zero project-object reuse** and passed the final checks and separate audit.
Lean and verified external dependency caches were reused; external dependencies
were not rebuilt from source.

- [Clean-project build report](../verification/benchmark-128x64-20261002/REPORT.md)
- [Timing record](../verification/benchmark-128x64-20261002/timing-report.json)
- [Final theorem and axiom log](../verification/benchmark-128x64-20261002/final-target.log)
- [Evidence audit](../verification/benchmark-128x64-20261002/audit.json)
- [Statement correspondence](STATEMENT.md)

## Hardware and measured runtime

- **2 x AMD EPYC 7B12**, **128 physical cores / 256 hardware threads**.
- **503.65 GiB** OS-visible memory; Ubuntu **22.04.3 LTS**, x86_64.
- Lean **4.32.2**, compiler commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`; nine pinned external revisions.
- Configured concurrency: **128 global / 64 Stage80**; observed peaks: **128 / 45**.
- Sampled peak working memory: **201.435 GiB**.
- Project module compilation: **8 h 50 min 34.742 s**.
- Total including preparation, final checks, audit and controller overhead:
  **8 h 57 min 28.828 s**, October 2, 2026, **08:26:42.539–17:24:11.367 UTC**.

This is one measured clean project build on the same server after the initial
campaign, with cached external dependencies. It is not a cold-cache benchmark or
a minimum hardware requirement.

## Mathematical source and attribution

The mathematical reference is Tong Zhang's *Exact Certificates for Unimodality
of Forest Independence Polynomials*, Theorem 1.1 and supporting Sections 2–5 and
Supplements A/B, fixed September 26 manuscript at
[commit `7cee5104a983dd1271db14be7606e96c504aa370`](https://github.com/zhangzenozhang-jpg/-forest-unimodality-proof/blob/7cee5104a983dd1271db14be7606e96c504aa370/paper/forest_unimodality_Tong_Zhang.pdf).
This formalization does not claim that mathematical discovery.

Publication and maintenance use the `lixiang90` account, with substantial OpenAI
Codex assistance in formalization, implementation and checking. See
[attribution disclosure](ATTRIBUTION.md). Organizer review, award eligibility,
priority and prize decisions are separate from completed machine verification.
Independent human review is not claimed.

## Checklist

- [x] Complete all-forest theorem compiled and final axioms recorded.
- [x] Clean build of every project module completed with no project-object reuse.
- [x] Final statement check and separate evidence audit passed.
- [x] Fixed proof SHA, hardware and measured runtime published.
- [x] Mathematical reference and formalization contribution distinguished.
- [ ] Organizer statement-correspondence review and acceptance.

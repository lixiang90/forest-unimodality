# Prepared PR text — source commit to be filled after snapshot commit

## Submission type and draft status

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information — **development candidate, final verification pending**

**Please keep this PR in draft. It is not a request to accept an incomplete proof
as a complete solution.** The current source is being made public while the last
integration compile and the new complete independent rebuild remain unfinished.
Known failures and incomplete checks are disclosed below. `Current status` stays
**Open**, `Lean proof` stays **No**, and `Eligible to claim` stays **No**.

The public snapshot records the code and its provenance. Publication time alone
does not establish priority, candidate status, eligibility or an award. We will
update this same PR with fixes and exact source versions as verification proceeds.

## Problem and mathematical source

- **JSP-000826 / Erdős 993:** weak unimodality of independent-set counts of every
  finite forest, including empty forests, disconnected forests and isolated vertices.
- Original problem: Alavi–Malde–Schwenk–Erdős, *The Vertex Independence Sequence
  of a Graph Is Not Constrained* (1987), Problem 3,
  [PDF page 7 / printed page 21](https://www.renyi.hu/~p_erdos/1987-33.pdf#page=7).
- Mathematical reference: Tong Zhang, *Exact Certificates for Unimodality of
  Forest Independence Polynomials*, Theorem 1.1 and supporting Sections 2–5 and
  required Supplements A/B, fixed September 26 manuscript at
  [commit `7cee5104a983dd1271db14be7606e96c504aa370`](https://github.com/zhangzenozhang-jpg/-forest-unimodality-proof/blob/7cee5104a983dd1271db14be7606e96c504aa370/paper/forest_unimodality_Tong_Zhang.pdf).
- This is an independent, AI-assisted Lean formalization effort, not a claim to
  the mathematical discovery. Mathematical review acceptance is not verified.
- Related submissions: [#4551](https://github.com/TheJustinSunPrize/awards/pull/4551)
  is the mathematical submission; [#3889](https://github.com/TheJustinSunPrize/awards/pull/3889)
  describes the four-vertex path special case; [#4318](https://github.com/TheJustinSunPrize/awards/pull/4318)
  is a formalization-status record. This draft targets all forests and explicitly
  leaves its own complete verification pending.

## Original repository and fixed source

```json
[
  {
    "repository": "https://github.com/lixiang90/forest-unimodality",
    "branch": "main",
    "commit": "PENDING_PUBLICATION_COMMIT"
  }
]
```

- Statement origin: proposed all-forest statement requiring maintainer correspondence review; no maintainer-approved Lean reference is claimed.
- Specification: [`ForestUnimodality.CompleteTarget`](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/ForestUnimodality/Statement.lean).
- Proposed final theorem: [`ForestUnimodality.Completed.completeTarget`](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/ForestUnimodality/Completed.lean).
- Explicit statement-to-proof check and four final axiom commands:
  [`checks/SubmissionCheck.lean`](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/checks/SubmissionCheck.lean).
- [Statement correspondence](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/docs/STATEMENT.md).

The candidate final file was materialized from the reviewed development generator
template, and its import added to the published umbrella. These publication-only
changes do not claim that the generator's verification gates passed and do not
modify the live compiler's inputs. The source manifest records these changes.
The source declares the all-order target without added mathematical premises;
actual acceptance of that declaration by Lean remains pending.

## Reproduction and resource observations

- Lean: `leanprover/lean4:v4.32.2`, compiler commit
  `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`; all nine external revisions
  are recorded in `lake-manifest.json`.
- [Candidate reproduction instructions](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/docs/REPRODUCING.md).
- [Resource and runtime report](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/docs/RESOURCE_REQUIREMENTS.md).

Candidate commands, **not yet a successful full reproduction**:

```sh
python scripts/verify.py --candidate --source-only
lake exe cache get
python scripts/verify.py --candidate
```

The implementation uses many exact arithmetic certificates and kernel-checked
reductions, including `decide +kernel`, along with structural and analytic lemmas.
This can require substantially more time and memory than short structural proof
terms. These are costs of this implementation, not proof that every solution of
the original problem intrinsically needs such resources.

Observed reference environment: approximately 64 GiB host RAM; Ubuntu WSL with
approximately 31 GiB RAM and 8 GiB swap. A Windows integration attempt failed
after roughly 43 minutes with `std::bad_alloc`. The Linux recovery began
`IntermediateBridgeRemaining.lean` at 2026-09-29 19:19:17 UTC. At 22:22:20 UTC,
it was still running after about **3 hours 3 minutes**, with approximately
26.3 GiB resident memory, 2.8 GiB swapped pages and 140.9 GiB virtual address space.
Virtual memory is not physical RAM demand. No reliable completion percentage or
successful full-build duration is available. These observations do not establish
a sufficient minimum hardware configuration. Complete independent rebuilding
will need additional time and disk space, to be measured separately.

The published candidate closure contains **31,598 Lean modules** and
**5,754,689,467 bytes** of uncompressed Lean source (about 5.36 GiB), excluding
external dependencies and compiled objects. File hashes are recorded in the
candidate source manifest.

Update at 2026-09-29 23:25 UTC: the remaining-region integration module finished
successfully in **14,604.37 seconds (about 4 hours 3 minutes)**, with six permitted
axiom reports, and its separate audit passed. The next parent integration module
is running. This successful local module check is not a complete independent
rebuild or acceptance of the final all-forest theorem.

## Actual verification status

- Historical partial isolated audit: 1,784 modules / 6,121 standard-axiom reports,
  combining 899 previously accepted prefix modules and 885 new rebuilds. This is
  not a clean rebuild of the final full closure.
- Separate local catalog checks reached all 896 required regional interfaces;
  their final integration is still being compiled.
- The last accepted main checkpoint had 669 regions and 130 parents, with 227
  region hypotheses remaining. Its old object is not proof of the refreshed source.
- The four actual final `Completed.*` axiom outputs are **pending**. Earlier
  permitted axioms were `propext`, `Classical.choice`, `Quot.sound`; no final output
  is fabricated or inferred from those earlier results.
- Complete independent rebuild, final source/statement binding and portable
  reproduction of the selected public commit are **pending**.
- External dependency caches were used; mathlib source rebuilding and an
  independent human verification are not claimed.

Any discovered compiler error will be recorded and repaired in a later commit,
the selected SHA updated, and affected checks rerun before requesting acceptance.

## Attribution

Publication and project maintenance use [`lixiang90`](https://github.com/lixiang90),
with substantial OpenAI Codex assistance in formalization, implementation and
checking. This is not an assertion of unaided human authorship or independently
verified claimant identity. Mathematical source credit is version-specific and
separate, as above. [Attribution disclosure](https://github.com/lixiang90/forest-unimodality/blob/PENDING_PUBLICATION_COMMIT/docs/ATTRIBUTION.md).

## Checklist

- [x] This diff changes only JSP-000826 catalog references and attribution.
- [x] Lean source, dependencies and build files remain in the external repository.
- [x] Mathematical reference and formalization contribution are distinguished.
- [x] No private identity documents, contact addresses, payment details or credentials are included.
- [ ] Complete all-forest theorem compiled and final axioms recorded.
- [ ] Complete independent rebuild and public-commit reproduction passed.
- [ ] Final statement correspondence and mathematical review accepted.
- [ ] Ready for maintainer acceptance as a complete Lean contribution.

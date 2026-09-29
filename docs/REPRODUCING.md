# Reproduction

**Status: commands prepared; complete portable reproduction has not yet run.**
The candidate source closure is published before final integration and independent
full rebuild finish. Do not interpret source packaging or preparation tooling
tests as successful Lean verification.

## Pinned environment

- Lean: `leanprover/lean4:v4.32.2`, compiler commit
  `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`.
- All nine external repository revisions: `lake-manifest.json`.
- Python 3.11 or later and Git for the portable checking script.
- Linux is the intended verification platform. The Windows final integration
  attempt ran out of memory; the ongoing Linux run does not yet establish
  a tested minimum memory requirement or a successful full build.

## Candidate commands (complete build not yet tested successfully)

Use a fresh checkout of the selected 40-character proof commit. Install the
pinned Lean toolchain with elan, keep the lockfile unchanged, and run:

```sh
python scripts/verify.py --candidate --source-only
lake exe cache get
python scripts/verify.py --candidate
```

`lake exe cache get` is intended to obtain official external dependency artifacts.
The checker rejects an existing project `.lake/build` directory; if setup creates
one, preserve it and investigate before attempting the clean verification. Do not
silently treat reused project objects as a fresh build. The setup/build sequence
still needs end-to-end testing at the final source version.

The explicit `--candidate` option selects `verification/development-source-manifest.json`.
Default mode requires a separate accepted-source manifest, which is absent in
this development publication. Neither source manifest is a proof certificate.

The checker checks source hashes and dependency revisions, strips inherited Lean
path overrides, invokes `lake build ForestUnimodality`, and then runs:

```sh
lake env lean -Dpp.fullNames=true checks/SubmissionCheck.lean
```

It requires the four exact final axiom reports and accepts only `propext`,
`Classical.choice` and `Quot.sound`. Results and full command logs are written to
an ignored, new `verification/runs/` directory. Failures are preserved. The script
does not stop long-running compilers on a timer.

A successful checker run establishes only its stated checks for the recorded
source. It does not certify mathematical source attribution, original-problem
correspondence, independent kernel replay by a second checker, or prize acceptance.
Official dependency cache use must not be described as rebuilding mathlib sources.

## Source and evidence versions

After verification, select proof commit **A** and confirm it belongs to the named
branch. Publish authorized reports in a later evidence commit **B**, explicitly
stating that they concern **A**. A report about the development snapshot does not
automatically verify a different public source commit. Preserve both success and
failure logs, and review evidence for private local paths before publication.

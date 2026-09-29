# Verification scope, resource observations and runtime

This is an explicitly incomplete development report, recorded on September 29,
2026 UTC / September 30, 2026 in Asia/Shanghai. No successful elapsed time for
the complete proof is available. The public snapshot is being shared while the
final integration compiler runs; it is not ready for mathematical acceptance.

## Scope of prior checks

- A historical isolated prefix audit covers 1,784 project modules and 6,121
  standard-axiom reports. That audit combines 899 previously accepted prefix
  modules and 885 newly rebuilt modules; it is **not** the whole final closure.
- All 896 required regional interfaces were separately catalogued as checked,
  with two supplemental entries. Those local checks do not establish successful
  integration of the complete theorem.
- The last accepted main checkpoint contained 669 regions and 130 parent domains,
  with 227 remaining region hypotheses. Its old object must not be confused with
  the refreshed all-region source now being compiled.
- The final four `ForestUnimodality.Completed.*` axiom reports and the new complete
  independent rebuild are still pending. No final successful axiom output is
  supplied or inferred from the earlier checks.

Earlier audits permitted only `propext`, `Classical.choice` and `Quot.sound`.
The final proof must establish its own actual transitive dependencies. Official
external dependency caches were used; recompilation of all mathlib sources is
not claimed. Evidence digests are listed in `verification/development-evidence.json`;
these summaries do not substitute for reproducible final proof verification.

## Published source size

The candidate import closure contains **31,598 Lean modules** and
**5,754,689,467 bytes** of uncompressed Lean source (about 5.36 GiB). This excludes
external dependencies and all compiled objects. The source manifest records each
file and hash. Git transfer size will differ because objects are compressed.

## Observed execution

Lean is version 4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
The reference host has approximately 64 GiB physical RAM. The current Ubuntu WSL
environment has approximately 31 GiB RAM and 8 GiB swap. These are observed
resources, **not a demonstrated sufficient minimum** for the complete proof.

The Windows final integration attempt ran for roughly 43 minutes and terminated
with `std::bad_alloc`. The same-version Linux recovery began checking
`IntermediateBridgeRemaining.lean` at **2026-09-29 19:19:17 UTC**, using one Lean
worker. At **22:22:20 UTC** it was still running after about **3 hours 3 minutes**,
with no terminal success or failure. The snapshot then showed roughly **26.3 GiB
resident memory**, **2.8 GiB swapped pages**, and **140.9 GiB virtual address space**.
Virtual address space is not physical RAM demand. Read and CPU counters continued
to increase; no reliable percentage-complete indicator was available.

The full independent project rebuild has not started. Its duration and peak
resources are unknown, and must be reported separately after execution. Allow
substantial time and disk capacity; do not interpret the current elapsed time as
an upper bound or a completion estimate.

Update at 2026-09-29 23:25 UTC: the remaining-region integration module finished
successfully in **14,604.37 seconds (about 4 hours 3 minutes)**, with six permitted
axiom reports, and its separate audit passed. The next parent integration module
is running. This successful local module check is not a complete independent
rebuild or acceptance of the final all-forest theorem.

## Why this implementation is expensive

This implementation uses many exact arithmetic certificates and kernel-checked
reductions, including `decide +kernel`, in addition to graph-theoretic and analytic
lemmas. Such reductions and the large import closure can cost substantially more
than short structural proof terms. This describes the present implementation;
it is not evidence that every solution to this problem requires these resources,
nor that time spent computing resolves any outstanding proof obligation.

The repository excludes development `.olean` files, caches and binaries. A fresh
reproduction must build project sources and inspect final axiom reports. Future
compiler errors will be preserved and corrected in subsequent commits, with the
selected PR source SHA updated and any affected verification rerun. No failed or
unfinished check will be relabelled as a success.

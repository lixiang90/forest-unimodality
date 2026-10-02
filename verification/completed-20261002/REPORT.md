# Completed verification of JSP-000826 / Erdos 993

Proof repository: https://github.com/lixiang90/forest-unimodality

Selected proof commit: `fc5696dbd7a5d708c0bf32755b9027031e6a19e0`. The files in this evidence directory describe that proof commit; the later commit publishing this report adds evidence only.

## Result

**PASS:** all **31,598 project modules**, the final statement-to-proof check, and a separate complete evidence audit passed. The final Lean check finished on **2026-10-02 at 08:19:57 UTC**; the evidence audit finished at **08:26:37 UTC**. The verification controller exited with code 0.

The exact target is `ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`. It states that for every natural number n and every acyclic simple graph on Fin n, the independent-set counts are weakly unimodal. This includes empty and disconnected forests and isolated vertices.

All four final transitive axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. See [actual output](final-target.log) and [audit result](audit.json). No `sorryAx`, `Lean.ofReduceBool`, or additional axiom occurs in these reports.

## Verification method and coverage

The verification campaign compiled the published source dependency graph with Lean 4.32.2 (compiler commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`), using explicit Lean invocations and `-j 1` per process. The pinned mathlib revision is `905b95818eb32af7874a58b427f50c1711a5e96c`. The campaign reused official external dependency caches.

The campaign started on a smaller Linux cloud machine and continued on the server below. **6,907 successful modules from the same campaign** were transferred, with source, output, log and dependency hashes checked before reuse; the remaining **24,691** were compiled on the final server. The complete 31,598-module ledger and dependency closure were then audited. This is a completed cross-machine campaign, not a claim that the final server alone rebuilt every module from zero.

The separate audit checked the fixed Git commit and source manifest, compiler hash, pinned external dependencies and their artifacts, each module's successful command and source/output/log hashes, dependency order and closure, all emitted axiom reports, the absence of extra project modules, and the successful final statement-to-proof check. It reused the completed Lean results and did not perform a second kernel replay. The submitted proof source is unchanged.

The scheduler's pre-audit progress flag is deliberately false until the separate audit runs; [audit.json](audit.json) records the authoritative completed audit result. The run exited successfully.

## Hardware and benchmark

The final server runs **Ubuntu 22.04.3 LTS (x86_64)** on **two AMD EPYC 7B12 processors**, with **128 physical cores / 256 hardware threads**, **503.65 GiB of OS-visible RAM** (540,791,611,392 bytes), and an approximately **915.32 GiB NVMe-backed filesystem**. The first completed campaign on this server used memory-aware upper limits of **64 global jobs / 32 Stage80 jobs**, with one Lean thread per job. These are measured machine specifications, not minimum requirements.

A separate clean project benchmark is running on the same server with upper limits of **128 global jobs / 64 Stage80 jobs**. It starts with zero project build objects, while reusing Lean and the verified external dependency cache. Preparation, module compilation, final checking, evidence auditing and total wall-clock times will be added after this run completes. Its elapsed time is not combined with the earlier campaign, and it is not a cold-cache or external-dependency-source benchmark.

## Evidence

[checksums.json](checksums.json) identifies the source manifest, complete module ledger, compiler, final log, audit result and full retained evidence archive. The 30,211,885-byte archive contains 38,573 evidence files; its archive and all individual file hashes were verified after download. It includes all module logs, the complete ledger, external artifact records, imported-module provenance and sealed verifier scripts. The compact report, raw audit, final log and hardware summary are published here; the complete archive is retained by the submitter.

The completed check establishes the reported Lean compilation and evidence results. Mathematical correspondence review and submission acceptance are handled by the prize maintainers under their published process.

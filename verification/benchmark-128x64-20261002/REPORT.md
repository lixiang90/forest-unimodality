# Completed clean-project benchmark: JSP-000826 / Erdos 993

**PASS: 31,598 / 31,598 project modules, final target check, and separate evidence audit.** The selected proof commit remains `fc5696dbd7a5d708c0bf32755b9027031e6a19e0`. This publication adds verification evidence only.

The run started at **2026-10-02 08:26:42.539 UTC** and finished at **17:24:11.367 UTC**, for a total of **8 h 57 min 28.828 s**. The project module build took **8 h 50 min 34.742 s**. Both the build and audit returned exit code 0.

## Timing

| Phase | Seconds |
| --- | ---: |
| Preparation | 45.987 |
| Project module build | 31,834.742 |
| Final statement and axiom check | 60.191 |
| Separate evidence audit | 290.484 |
| Other build/controller overhead | 17.424 |
| Total wall-clock | 32,248.828 |

Times are taken from the retained [timing-report.json](timing-report.json). Total time starts with this run's preparation, excludes waiting for the earlier campaign, and includes controller overhead. The earlier campaign's runtime is not added to these figures.

## Hardware, concurrency and scope

- CPU: **2 x AMD EPYC 7B12**, **128 physical cores / 256 hardware threads**.
- Memory: **503.65 GiB OS-visible**; Ubuntu **22.04.3 LTS**, x86_64; approximately **915.32 GiB NVMe-backed filesystem**. See [hardware.json](hardware.json).
- Configured upper limits: **128 global jobs / 64 Stage80 jobs**, one Lean thread per process, with memory-aware admission.
- Observed peak concurrency: **128 global jobs / 45 Stage80 jobs**.
- Sampled peak working memory: **216,289,521,664 bytes (201.435 GiB)**. This is the controller's host/cgroup working-memory measure, not the sum of process RSS or an exact unsampled peak.
- **Zero project build objects reused**: all 31,598 project modules were compiled into a fresh project directory on the same server after the previous campaign. Lean and verified external dependency caches were reused. This measures a clean project build, not a cold-cache run or an external-dependency-source rebuild.

## Verification and retained evidence

The final target is `ForestUnimodality.Completed.completeTarget : ForestUnimodality.CompleteTarget`. The [final log](final-target.log) reports exactly `propext`, `Classical.choice`, and `Quot.sound` for all four checked declarations, including the final theorem. The [audit](audit.json) passed at **2026-10-02 17:24:11.252 UTC**.

The separate evidence audit checked source and dependency identities, all module results and source/output/log hashes, dependency closure, and the final check. It did not recompile the modules or perform another kernel replay. This successful run provides a complete fresh project compilation in addition to the earlier cross-machine campaign.

The full evidence archive, module ledger, logs, sealed scripts and timing report are retained locally with every file hash verified after download. Compiled objects from both runs remain preserved on the server. See [checksums.json](checksums.json) for the archive and published-file hashes.

# Preparation tooling checks

On 2026-09-30 (Asia/Shanghai), this command passed 17 Python tests:

```sh
python -m unittest discover -s tests -v
```

Tests cover fixed configuration, exact final axiom-report names, permitted and
unexpected axioms, unsafe module names, and synthetic source-package identity.
The source-package fixtures exercise changed and missing sources, extra files,
missing export edges, dependency cycles, and a changed final checking entry.
Fixture hash constants are patched only within test contexts; these small
fixtures are not mathematical proofs and are never imported into the library.

The actual incomplete package was also checked with `--source-only` and returned
exit code 2 because the accepted final source manifest is absent. The development
importer refused the absent final rebuild audit, without copying sources.

No Lean compiler ran during these tests. The real source-import success path,
portable full build and final theorem audit remain pending.

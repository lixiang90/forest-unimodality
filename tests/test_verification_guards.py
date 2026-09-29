"""Synthetic tooling checks only: these do not compile or certify a Lean proof."""
import importlib.util
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

path = Path(__file__).resolve().parents[1] / 'scripts/verify.py'
spec = importlib.util.spec_from_file_location('submission_verify', path)
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


def reports(axioms='propext, Classical.choice, Quot.sound'):
    return '\n'.join("'" + name + "' depends on axioms: [" + axioms + ']' for name in verify.THEOREMS)


class VerificationGuards(unittest.TestCase):
    def test_pinned_configuration(self):
        self.assertEqual(len(verify.configuration()), 9)

    def test_standard_axioms(self):
        self.assertEqual(set(verify.parse_axioms(reports())), set(verify.THEOREMS))

    def test_empty_axiom_dependencies(self):
        text = '\n'.join("'" + name + "' does not depend on any axioms" for name in verify.THEOREMS)
        self.assertTrue(all(not x for x in verify.parse_axioms(text).values()))

    def test_multiline_axioms(self):
        self.assertEqual(len(verify.parse_axioms(reports('propext,\n Classical.choice,\n Quot.sound'))), 4)

    def test_sorry_rejected(self):
        with self.assertRaises(ValueError):
            verify.parse_axioms(reports('propext, sorryAx'))

    def test_added_assumption_rejected(self):
        with self.assertRaises(ValueError):
            verify.parse_axioms(reports('MyMissingProof'))

    def test_missing_report_rejected(self):
        with self.assertRaises(ValueError):
            verify.parse_axioms('\n'.join(reports().splitlines()[:-1]))

    def test_duplicate_report_rejected(self):
        with self.assertRaises(ValueError):
            verify.parse_axioms(reports() + '\n' + reports().splitlines()[0])

    def test_wrong_theorem_rejected(self):
        with self.assertRaises(ValueError):
            verify.parse_axioms(reports().replace('Completed.completeTarget', 'Other.completeTarget'))

    def test_unsafe_module_path_rejected(self):
        for name in ('../secret', 'ForestUnimodality...Other', 'Erdos953Lower', '/tmp/x'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                verify.module_path(name)


class SourcePackageGuards(unittest.TestCase):
    """Small synthetic byte fixtures; no fixture is a mathematical proof."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='forest-package-test-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'checks/SubmissionCheck.lean'):
            destination = self.root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((verify.ROOT / name).read_bytes())
        data = {
            'ForestUnimodality.Statement': b'-- synthetic statement identity fixture\n',
            'ForestUnimodality.Completed': b'import ForestUnimodality.Statement\n',
            'ForestUnimodality': b'import ForestUnimodality.Completed\n',
        }
        files = {}
        previous = None
        for name, contents in data.items():
            destination = self.root / verify.module_path(name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(contents)
            files[name] = {'sha256': verify.sha(destination), 'local': [previous] if previous else [], 'external': []}
            previous = name
        self.manifest = {
            'roots': verify.ROOTS, 'source_import_complete': True,
            'module_order': list(data), 'files': files,
            'configuration_sha256': {name: verify.sha(self.root / name) for name in (
                'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'checks/SubmissionCheck.lean')},
        }
        (self.root / 'verification').mkdir()
        self.save_manifest()
        # Patch reviewed-source identities only within this synthetic test context.
        patches = (
            patch.object(verify, 'ROOT', self.root),
            patch.object(verify, 'STATEMENT', files['ForestUnimodality.Statement']['sha256']),
            patch.object(verify, 'TEMPLATE', hashlib.sha256(data['ForestUnimodality.Completed']).hexdigest()),
        )
        for context in patches:
            context.start()
            self.addCleanup(context.stop)

    def save_manifest(self):
        (self.root / 'verification/source-manifest.json').write_text(json.dumps(self.manifest), encoding='utf-8')

    def test_intact_fixture_identity(self):
        self.assertEqual(len(verify.check_sources()['files']), 3)

    def test_source_edit_rejected(self):
        (self.root / 'ForestUnimodality/Statement.lean').write_text('-- changed\n')
        with self.assertRaisesRegex(ValueError, 'Source changed'):
            verify.check_sources()

    def test_missing_source_rejected(self):
        (self.root / 'ForestUnimodality/Completed.lean').unlink()
        with self.assertRaises(FileNotFoundError):
            verify.check_sources()

    def test_extra_source_rejected(self):
        (self.root / 'ForestUnimodality/Extra.lean').write_text('-- extra\n')
        with self.assertRaisesRegex(ValueError, 'source set differs'):
            verify.check_sources()

    def test_missing_export_rejected(self):
        self.manifest['files']['ForestUnimodality']['local'] = []
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'unrelated project modules'):
            verify.check_sources()

    def test_dependency_cycle_rejected(self):
        self.manifest['files']['ForestUnimodality.Statement']['local'] = ['ForestUnimodality.Completed']
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'dependency order'):
            verify.check_sources()

    def test_changed_check_entry_rejected(self):
        (self.root / 'checks/SubmissionCheck.lean').write_text('-- changed\n')
        with self.assertRaisesRegex(ValueError, 'Configuration changed'):
            verify.check_sources()


if __name__ == '__main__':
    unittest.main()

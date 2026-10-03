import unittest
from simplify_shared_rationals import simplify

Q = b'(12345678901234567890123456789/10000000000000000000000000000)'
def sample(body, nl=b'\n'):
    return nl.join([b'namespace Batch000', b'def cell00 : Cell :=', body,
        b'theorem checked00 : cell00.check parameters domain=true := by decide +kernel', b'end Batch000', b''])

class SharingTests(unittest.TestCase):
    def test_lossless_and_idempotent(self):
        for nl in (b'\n', b'\r\n'):
            original = sample(b'[' + b', '.join([Q] * 4) + b']', nl)
            updated, count, uses = simplify(original)
            self.assertEqual((count, uses), (1, 4))
            self.assertIn(b'private def sharedRat0000 : Rat := ' + Q + nl, updated)
            self.assertEqual(simplify(updated), (updated, 0, 0))
            self.assertEqual(updated.count(b'\r\n'), updated.count(b'\n') if nl == b'\r\n' else 0)
    def test_short_and_infrequent_unchanged(self):
        original = sample(b'[(1/2), (1/2), (1/2), ' + Q + b', ' + Q + b']')
        self.assertEqual(simplify(original), (original, 0, 0))
    def test_distinct_and_negative_literals(self):
        negative = b'(-' + Q[1:]
        updated, count, uses = simplify(sample(b'[' + b', '.join([Q, negative] * 4) + b']'))
        self.assertEqual((count, uses), (2, 8))
        self.assertIn(b': Rat := ' + negative, updated)
    def test_proofs_and_other_definitions_untouched(self):
        original = sample(b'[' + b', '.join([Q] * 4) + b']') + b'def unrelated := ' + Q + b'\n'
        updated, _, _ = simplify(original)
        self.assertTrue(updated.endswith(b'def unrelated := ' + Q + b'\n'))
    def test_unrecognized_source_rejected(self):
        for original in (b'', sample(b'-- comment'), sample(b'sharedRat0000')):
            with self.assertRaises(ValueError): simplify(original)

if __name__ == '__main__': unittest.main()

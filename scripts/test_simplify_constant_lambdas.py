import unittest
from simplify_constant_lambdas import simplify

class ConstantLambdaTests(unittest.TestCase):
    def test_equal_branches(self):
        self.assertEqual(simplify(b'(fun i=>if i.val=0 then (7/11) else if i.val=1 then (7/11) else (7/11))'),(b'(fun _ => (7/11))',1))
    def test_unequal_branch_is_untouched(self):
        s=b'(fun i=>if i.val=0 then (7/11) else if i.val=1 then (8/11) else (7/11))'
        self.assertEqual(simplify(s),(s,0))
    def test_textually_different_equal_rationals_untouched(self):
        s=b'(fun i=>if i.val=0 then (1/2) else (2/4))'
        self.assertEqual(simplify(s),(s,0))
    def test_preserves_surrounding_bytes_and_line_endings(self):
        s=b'prefix\r\n(fun i=>if i.val=0 then (-3/5) else (-3/5))\r\nsuffix'
        out,n=simplify(s)
        self.assertEqual((out,n),(b'prefix\r\n(fun _ => (-3/5))\r\nsuffix',1))
        self.assertEqual(simplify(out),(out,0))
    def test_does_not_rewrite_nonliteral_expressions(self):
        s=b'(fun i=>if i.val=0 then (x/5) else (x/5))'
        self.assertEqual(simplify(s),(s,0))

if __name__ == '__main__':
    unittest.main()

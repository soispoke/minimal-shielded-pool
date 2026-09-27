import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_formal as c  # noqa: E402


class CheckFormal(unittest.TestCase):
    def test_lock_covers_the_concrete_definitions(self):
        names = {p.relative_to(c.FORMAL).as_posix() for p in c.statement_files()}
        for name in ('SPEC.md', 'Spec.lean', 'Spec/System.lean', 'Spec/Hash.lean', 'Spec/Circuit.lean',
                     'Poseidon/Constants.lean', 'Keccak/Hash.lean', 'Artifacts/Spend.lean',
                     'Artifacts/PathBitsData.lean', 'Artifacts/Compression.lean'):
            self.assertIn(name, names)
        self.assertIn('Primality/PrattCertificate.lean', names)  # a `public import`
        self.assertIn('Proofs/AxiomAudit.lean', names)
        self.assertNotIn('Proofs/Model.lean', names)

    def test_import_forms(self):
        text = 'import A.B\npublic import C\nprivate meta import D\nimport all E\n-- import F\n'
        self.assertEqual(c.IMPORT.findall(text), ['A.B', 'C', 'D', 'E'])

    def test_banned_words_outside_comments(self):
        for code in ('theorem t : False := sorry', '@[simp] axiom bad : False',
                     'private unsafe def f : Nat := 0', 'theorem t : 1 = 1 := by native_decide',
                     '@[implemented_by g] def f : Nat := 0',
                     'set_option debug.skipKernelTC true in', 'noncomputable axiom bad : False',
                     'example : 2 + 2 = 4 := by decide +native', 'by bv_decide',
                     'decide (config := { native := true })'):
            self.assertTrue(c.BANNED.search(c.strip_comments(code)), code)
        for code in ('/- sorry, axiom -/ def f := 0', '-- unsafe\ndef f := 0',
                     '/- nested /- axiom -/ still comment -/ def f := 0', '#print axioms f',
                     'theorem sorry_free : True := trivial'):
            self.assertFalse(c.BANNED.search(c.strip_comments(code)), code)


if __name__ == '__main__':
    unittest.main()

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


    def test_literals_cannot_hide_code(self):
        for code in ('def s := "/-"\naxiom bad : False\ndef t := "-/"',
                     "def c := '\"'\naxiom bad : False", 'def s := "a\\"b"\naxiom bad : False'):
            self.assertTrue(c.BANNED.search(c.strip_comments(code)), code)
        self.assertFalse(c.BANNED.search(c.strip_comments('def s := "sorry, axiom"')))
        self.assertEqual(c.strip_comments("theorem h' : x' = x'"), "theorem h' : x' = x'")

    def test_raw_and_interpolated_strings_cannot_hide_code(self):
        hidden = ('def s : String := r"\\"\nopen Lean in\nrun_cmd pure ()\ndef t : String := "x"',
                  'def s : String := r#"a"b"#\n#eval 1',
                  'def s : String := s!"{"\\""}"\nopen Lean in\ndef t := "x"',
                  'def s := r"/-\\"\n#eval 1\ndef t := "-/"',
                  'def s := s!"{ "/-" }"\n#eval 1\ndef t := "-/"')
        for code in hidden:
            self.assertTrue(c.META.search(c.strip_comments(code)), code)
        self.assertTrue(c.BANNED.search(c.strip_comments('def s := r"\\"\naxiom bad : False\ndef t := "x"')))
        self.assertTrue(c.BANNED.search(c.strip_comments('def s := s!"{"\\""}"\naxiom bad : False')))
        # interpolation keeps its code: a banned word inside the braces is still seen
        self.assertTrue(c.BANNED.search(c.strip_comments('def s := s!"x {sorry} y"')))
        self.assertFalse(c.BANNED.search(c.strip_comments('def s := s!"sorry {1 + 1} axiom"')))
        # unprefixed interpolation and guillemet identifiers
        for code in ('#check println! "{ "\\"" }"\nopen Lean in\nrun_cmd pure ()',
                     'def \u00abx"\u00bb : Nat := 0\n#eval 1\ndef \u00aby"\u00bb : Nat := 1'):
            self.assertTrue(c.META.search(c.strip_comments(code)), code)
        self.assertTrue(c.BANNED.search(c.strip_comments(
            'def \u00abx"\u00bb : Nat := 0\naxiom choice : False\ndef \u00aby"\u00bb : Nat := 1')))

    def test_metaprograms(self):
        for code in ('#eval IO.FS.writeFile "a" "b"', 'macro_rules | `(x) => `(y)', 'run_cmd pure ()',
                     'open Lean in', '#guard_msgs in example : False := sorry', 'syntax "x" : term',
                     'elab "x" : term => pure default', 'initialize foo : IO.Ref Nat ← IO.mkRef 0',
                     'def x := eval% 1 + 1', 'local notation "q" => 1'):
            self.assertTrue(c.META.search(c.strip_comments(code)), code)
        for code in ('theorem elaborate_ok : True := trivial', 'def prefix_len := 0', '-- #eval 1'):
            self.assertFalse(c.META.search(c.strip_comments(code)), code)


if __name__ == '__main__':
    unittest.main()

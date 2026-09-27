import shutil
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))

import differential_model as dm  # noqa: E402

W = dm.W


class HarnessTests(unittest.TestCase):
    def test_parser_rejects_duplicates_and_malformed_lines(self):
        self.assertEqual(dm.parse_lean_output("x\nR a b 12\n"), {("a", "b"): 12})
        with self.assertRaisesRegex(ValueError, "duplicate"):
            dm.parse_lean_output("R a b 1\nR a b 1\n")
        with self.assertRaisesRegex(ValueError, "malformed"):
            dm.parse_lean_output("R a b -1\n")

    def test_compare_reports_mismatch_and_missing_value(self):
        problems = dm.compare({("a", "x"): 1, ("a", "y"): 2}, {("a", "x"): 3})
        self.assertEqual([(p["field"], p["lean"]) for p in problems], [("x", "3"), ("y", None)])

    def test_generation_is_seeded_and_in_range(self):
        cases = dm.generate(7, 8, direct_spend=2)
        self.assertEqual(cases, dm.generate(7, 8, direct_spend=2))
        for kind, _, a in cases:
            if kind == "note":
                self.assertLess(a["i"], 1 << dm.DEPTH)
            if kind == "domain":
                self.assertTrue(a["c"] < 1 << 256 and a["a"] < 1 << 160 and a["e"] < 1 << 64)
            if kind in ("spend", "spenddirect"):
                self.assertTrue(0 <= a["f"] < a["v"] < dm.U128 and 0 < a["rcp"] < 1 << 160)
                self.assertEqual(a["L"][a["i"]], W.commitment(a["sk"], a["rho"], a["v"]))


@unittest.skipUnless(shutil.which("lake"), "lake is not on PATH")
class EndToEndTests(unittest.TestCase):
    """One small Lean run, compared with the wallet and with deliberately
    broken wallet variants, each of which the comparison must catch."""

    @classmethod
    def setUpClass(cls):
        cls.cases = dm.generate(11, 4)  # 4: the first three statements are boundary cases
        cls.observed, _, _ = dm.run_lean(dm.lean_source(cls.cases, 3))

    def problems(self):
        return dm.compare(dm.expectations(self.cases, 3), self.observed)

    def failing_fields(self):
        return {(p["case"].split("/")[0], p["field"]) for p in self.problems()}

    def test_wallet_agrees(self):
        self.assertEqual(self.problems(), [])

    def test_reversed_fingerprint_is_caught(self):
        def reversed_fingerprint(sigma, stmt):
            acc = 0
            for x in stmt:
                acc = (acc * sigma + x) % dm.P
            return acc
        with mock.patch.object(W, "fingerprint", reversed_fingerprint):
            self.assertIn(("compression", "gamma"), self.failing_fields())

    def test_swapped_nullifier_inputs_are_caught(self):
        def swapped(domain, spend_key, cm, index):
            return W.tagged(W.TAG_OCCURRENCE_NULL, W.p2(domain, spend_key), W.p2(index, cm))
        with mock.patch.object(W, "nullifier", swapped):
            fields = self.failing_fields()
        self.assertTrue({("note", "nf"), ("spend", "x0"), ("spend", "x1")} <= fields)

    def test_dummy_index_convention_is_caught(self):
        original = W.nullifier

        def dummy_at_one(domain, spend_key, cm, index):
            return original(domain, spend_key, cm, 1 if index == 0 else index)
        with mock.patch.object(W, "nullifier", dummy_at_one):
            self.assertIn(("spend", "x1"), self.failing_fields())

    def test_wrong_domain_tag_is_caught(self):
        with mock.patch.object(W, "DOMAIN_TAG", bytes(32)):
            fields = self.failing_fields()
        self.assertTrue({("const", "DOMAIN_TAG"), ("domain", "D"), ("spend", "x5")} <= fields)

    def test_wrong_auth_path_is_caught(self):
        original = W.Tree.auth_path

        def shifted(tree, idx):
            sibs, bits = original(tree, idx)
            return [sibs[0] + 1] + sibs[1:], bits
        with mock.patch.object(W.Tree, "auth_path", shifted):
            fields = self.failing_fields()
        self.assertTrue({("tree", "sib0"), ("spend", "sib0_0")} <= fields)


if __name__ == "__main__":
    unittest.main()

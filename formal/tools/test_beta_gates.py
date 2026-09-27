import copy
import os
from pathlib import Path
import unittest
from unittest.mock import patch
import beta_gates as beta
import r1cs_artifact as r


class BetaGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        cls.artifact = r.parse_r1cs(cls.data, pinned_compat=True)
        cls.node_modules = Path(os.environ.get('MSP_NODE_MODULES', r.ROOT / 'tooling/node_modules'))

    def test_exact_data_and_all_affine_stages(self):
        self.assertEqual(beta.render(self.data, self.node_modules).encode(), beta.DESTINATION.read_bytes())

    def test_changed_artifact_rejected(self):
        data = bytearray(self.data)
        data[-1] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            beta.prepare(data, self.node_modules)

    def test_wrong_statement_field_coefficient_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        # Preserve all three S-box equations' sign/reuse pattern while changing
        # its first statement input from nf1 to 2*nf1. Initial binding must fail.
        for constraint, side, coefficient in [(9, 0, r.P-2), (9, 1, 2), (11, 1, 2)]:
            terms = artifact['constraints'][constraint][side]
            artifact['constraints'][constraint][side] = [(w, coefficient if w == 99 else c) for w, c in terms]
        with patch.object(beta, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'initial state mismatch'):
                beta.prepare(self.data, self.node_modules)

    def test_wrong_round_constant_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        # Shift an optimized S-box output's affine constant. The local nonlinear
        # triple still has the expected shape, but its next round no longer binds.
        terms = artifact['constraints'][11][2]
        artifact['constraints'][11][2] = [(w, (c+1) % r.P if w == 0 else c) for w, c in terms]
        with patch.object(beta, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'prefix 0'):
                beta.prepare(self.data, self.node_modules)


if __name__ == '__main__':
    unittest.main()

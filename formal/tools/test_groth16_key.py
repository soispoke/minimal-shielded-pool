#!/usr/bin/env python3
"""Negative checks for the exact-key exporter and G2 encoding convention."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
import groth16_key as g


class KeyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.key = json.loads((g.ROOT / 'contracts/vectors/spend_vkey.json').read_text())

    def rejected(self, edit):
        key = copy.deepcopy(self.key)
        edit(key)
        with self.assertRaises((ValueError, KeyError)):
            g.parse_key(json.dumps(key))

    def test_exact_export(self):
        self.assertEqual(g.DEST.read_text(), g.render_from_pinned())

    def test_coordinate_aliases(self):
        for value in (str(g.Q), '01', '+1', '-1', '1.0', 1):
            self.rejected(lambda k: k['vk_alpha_1'].__setitem__(0, value))

    def test_metadata(self):
        for field, value in (('protocol', 'plonk'), ('curve', 'bls12381'), ('nPublic', 3.0), ('nPublic', True), ('nPublic', 4)):
            self.rejected(lambda k: k.__setitem__(field, value))

    def test_affine_and_ic_shape(self):
        self.rejected(lambda k: k['vk_alpha_1'].__setitem__(2, '0'))
        self.rejected(lambda k: k['vk_beta_2'].__setitem__(2, ['0', '0']))
        self.rejected(lambda k: k['IC'].pop())
        self.rejected(lambda k: k['vk_beta_2'][0].pop())

    def test_g2_order(self):
        key = g.parse_key(json.dumps(self.key))
        self.assertEqual(key['gamma2'][:2], [
            10857046999023057135944570762232829481370756359578518086990519993285655852781,
            11559732032986387107991004021392285783925812861821192530917403151452391805634])

    def test_pin_precedes_parse(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            path = root / next(iter(g.PINS))
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(self.key) + '\n')
            with self.assertRaisesRegex(ValueError, 'SHA256 mismatch'):
                g.render_from_pinned(root)


if __name__ == '__main__':
    unittest.main()

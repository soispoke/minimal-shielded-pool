import copy
import os
from pathlib import Path
import unittest
from unittest.mock import patch

import r1cs_artifact as r
import small_hash_gates as small
import small_hash_affine as affine


class SmallHashAffineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        cls.mapping = small.MAP.read_bytes()
        cls.artifact = r.parse_r1cs(cls.data, pinned_compat=True)
        cls.records = small.prepare(cls.data, cls.mapping)
        cls.node_modules = Path(os.environ.get('MSP_NODE_MODULES', r.ROOT / 'tooling/node_modules'))

    def test_exact_data_and_all_certificate_sources(self):
        for name, expected in affine.outputs(self.data, self.mapping, self.node_modules).items():
            with self.subTest(file=name):
                self.assertEqual((affine.DESTINATION / name).read_bytes(), expected)

    def test_changed_r1cs_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned R1CS'):
            affine.prepare(self.data + b'\0', self.mapping, self.node_modules)

    def test_changed_instance_map_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'instance map changed'):
            affine.prepare(self.data, self.mapping + b'\n', self.node_modules)

    def test_wrong_interface_input_rejected(self):
        records = copy.deepcopy(self.records)
        records[0]['input_forms'][0][0][1] = '2'
        with patch.object(affine.small, 'prepare', return_value=records):
            with self.assertRaisesRegex(r.InvalidArtifact, 'instance 0: initial state mismatch'):
                affine.prepare(self.data, self.mapping, self.node_modules)

    def test_changed_affine_output_constant_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        # Alter an S-box output LC without changing its valid x^5 triple shape.
        # The next affine stage must reject this otherwise coherent local gate.
        offset = self.records[0]['constraint_start']
        terms = artifact['constraints'][offset + 2][2]
        artifact['constraints'][offset + 2][2] = terms + [(0, 1)]
        with patch.object(affine, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'instance 0: prefix 0'):
                affine.prepare(self.data, self.mapping, self.node_modules)

    def test_wrong_interface_output_rejected(self):
        records = copy.deepcopy(self.records)
        records[0]['output_form'][0][1] = '2'
        with patch.object(affine.small, 'prepare', return_value=records):
            with self.assertRaisesRegex(r.InvalidArtifact, 'instance 0: final output'):
                affine.prepare(self.data, self.mapping, self.node_modules)

    def test_changed_constant_folded_coordinate_rejected(self):
        records = copy.deepcopy(self.records)
        # This leaf-hash coordinate was eliminated entirely by the compiler.
        # Its fixed domain value must still agree with the advertised input.
        records[2]['constant_folded_first_coordinates']['1'] = 3
        with patch.object(affine.small, 'prepare', return_value=records):
            with self.assertRaisesRegex(r.InvalidArtifact, 'instance 2: initial state mismatch'):
                affine.prepare(self.data, self.mapping, self.node_modules)


if __name__ == '__main__':
    unittest.main()

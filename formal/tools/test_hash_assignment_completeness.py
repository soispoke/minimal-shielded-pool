import copy
import unittest
from unittest.mock import patch

import hash_assignment_completeness as assignment
import small_hash_gates as small
import r1cs_artifact as r


class HashAssignmentCompletenessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (r.ROOT/'build/spend.r1cs').read_bytes()
        cls.mapping = small.MAP.read_bytes()
        cls.artifact = r.parse_r1cs(cls.data, pinned_compat=True)
        cls.records = small.prepare(cls.data, cls.mapping)

    def test_exact_generated_sources(self):
        for name, expected in assignment.outputs(self.data, self.mapping).items():
            with self.subTest(file=name):
                self.assertEqual((assignment.DESTINATION/name).read_text(), expected)

    def test_changed_r1cs_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned R1CS'):
            assignment.prepare(self.data+b'\0', self.mapping)

    def test_changed_map_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'instance map changed'):
            assignment.prepare(self.data, self.mapping+b'\n')

    def test_wrong_power_coefficient_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        offset = self.records[0]['constraint_start']+1
        wire, _ = artifact['constraints'][offset][1][0]
        artifact['constraints'][offset][1] = [(wire, 2)]
        with patch.object(assignment, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'power wire coefficient'):
                assignment.prepare(self.data, self.mapping)

    def test_overlapping_power_wires_rejected(self):
        artifact = copy.deepcopy(self.artifact)
        offset = self.records[0]['constraint_start']+1
        wire, _ = artifact['constraints'][offset][1][0]
        artifact['constraints'][offset][2] = [(wire, r.P-1)]
        with patch.object(assignment, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'power wire schedule'):
                assignment.prepare(self.data, self.mapping)

    def test_input_overwrite_rejected(self):
        records = copy.deepcopy(self.records)
        offset = records[0]['constraint_start']+1
        wire, _ = self.artifact['constraints'][offset][1][0]
        records[0]['input_forms'][0] = [[wire, '1']]
        with patch.object(assignment.small, 'prepare', return_value=records):
            with self.assertRaisesRegex(r.InvalidArtifact, 'input overwritten'):
                assignment.prepare(self.data, self.mapping)

    def test_duplicate_retained_stage_rejected(self):
        records = copy.deepcopy(self.records)
        stages = records[0]['sigma_constraint_offsets']
        stages['sigmaF[0][2]'] = stages['sigmaF[0][1]']
        with patch.object(assignment.small, 'prepare', return_value=records):
            with self.assertRaisesRegex(r.InvalidArtifact, 'duplicate retained stage'):
                assignment.prepare(self.data, self.mapping)


if __name__ == '__main__':
    unittest.main()

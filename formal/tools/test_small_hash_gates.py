import copy
import unittest
from unittest.mock import patch
import small_hash_gates as small
import r1cs_artifact as r


class SmallHashGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        cls.mapping = small.MAP.read_bytes()

    def test_exact_data_and_proof_sources(self):
        self.assertEqual(small.render(self.data, self.mapping), small.DESTINATION.read_text())
        self.assertEqual(small.render_certificates(), small.CERTIFICATES.read_text())

    def test_changed_r1cs_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned R1CS'):
            small.prepare(self.data + b'\0', self.mapping)

    def test_changed_instance_map_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'instance map changed'):
            small.prepare(self.data, self.mapping + b'\n')

    def test_changed_square_relation_rejected(self):
        artifact = copy.deepcopy(r.parse_r1cs(self.data, pinned_compat=True))
        # Change the actual square constraint's output sign while retaining its
        # wire and every source-stage index. The local relation must be rejected.
        wire, _ = artifact['constraints'][697][2][0]
        artifact['constraints'][697][2] = [(wire, 1)]
        with patch.object(small, 'parse_r1cs', return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact, 'square output sign at 697'):
                small.prepare(self.data, self.mapping)


if __name__ == '__main__':
    unittest.main()

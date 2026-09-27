import unittest
import range_fragment as fragment
import r1cs_artifact as r


class RangeFragmentTests(unittest.TestCase):
    def test_exact_pinned_range_data(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        self.assertEqual(fragment.render(data).encode('utf-8'), fragment.DESTINATION.read_bytes())

    def test_mutated_source_is_rejected(self):
        data = bytearray((r.ROOT / 'build/spend.r1cs').read_bytes())
        data[32] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            fragment.render(data)


if __name__ == '__main__':
    unittest.main()

import json
import unittest
import path_bits_fragment as paths
import r1cs_artifact as r


class PathBitsTests(unittest.TestCase):
    def test_mutated_r1cs_is_rejected_before_symbols(self):
        data = bytearray((r.ROOT / 'build/spend.r1cs').read_bytes())
        data[32] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            paths.render(data, b'')

    def test_unpinned_symbol_bytes_are_rejected(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        with self.assertRaisesRegex(r.InvalidArtifact, 'symbol SHA-256'):
            paths.render(data, b'1,1,0,main.beta\n')

    def test_required_private_input_may_not_be_eliminated(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'required witness signal is eliminated'):
            paths.wire({'main.in_value[0]': {'wire': None}}, 'main.in_value[0]')

    def test_all_forty_constraints_match_saved_pinned_wire_map(self):
        _, artifact = r.read_pinned(r.ROOT / 'build/spend.r1cs')
        signals = json.loads(r.MANIFEST.read_text())['signals']
        for k, start in [(0, 636), (1, 6988)]:
            for bit in range(20):
                name = f'main.in_bits[{k}][{bit}]'
                wire = signals[name]['wire']
                with self.subTest(signal=name):
                    self.assertEqual(artifact['labels'][wire], signals[name]['label'])
                    self.assertEqual(artifact['constraints'][start+bit],
                                     [[(0, r.P-1), (wire, 1)], [(wire, 1)], []])


if __name__ == '__main__':
    unittest.main()

import unittest
import range_address_fragment as addresses
import r1cs_artifact as r


class AddressRangeTests(unittest.TestCase):
    def test_exact_pinned_address_data(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        self.assertEqual(addresses.render(data).encode('utf-8'), addresses.DESTINATION.read_bytes())

    def test_mutated_artifact_rejected(self):
        data = bytearray((r.ROOT / 'build/spend.r1cs').read_bytes())
        data[32] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            addresses.render(data)

    def test_two_gate_layouts_and_eliminated_top_coefficients(self):
        _, artifact = r.read_pinned(r.ROOT / 'build/spend.r1cs')
        for name, start, wire_start, _, wire in addresses.GATES:
            with self.subTest(address=name):
                constraints = artifact['constraints'][start:start + 160]
                for i, constraint in enumerate(constraints[:159]):
                    self.assertEqual(constraint, [[(0, r.P-1), (wire_start+i, 1)],
                                                  [(wire_start+i, 1)], []])
                a, b, c = constraints[159]
                self.assertEqual(a, [(0, r.P-1)] + b)
                self.assertEqual(c, [])
                scaled = sorted((w, (2**159 * coefficient) % r.P) for w, coefficient in b)
                expected = [(wire, 1)] + [(wire_start+i, (-2**i) % r.P) for i in range(159)]
                self.assertEqual(scaled, sorted(expected))


if __name__ == '__main__':
    unittest.main()

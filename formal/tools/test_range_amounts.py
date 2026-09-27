import unittest
import range_amounts as amounts
import r1cs_artifact as r


class AmountRangeTests(unittest.TestCase):
    def test_exact_pinned_amount_data(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        self.assertEqual(amounts.render(data).encode('utf-8'), amounts.DESTINATION.read_bytes())

    def test_mutated_artifact_rejected(self):
        data = bytearray((r.ROOT / 'build/spend.r1cs').read_bytes())
        data[-1] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            amounts.render(data)

    def test_five_gate_layout_and_eliminated_fee_coefficients(self):
        # Independent integer-mod-p check of the optimizer's reconstruction.
        # The corresponding field certificate is also kernel-checked in Lean.
        _, artifact = r.read_pinned(r.ROOT / 'build/spend.r1cs')
        for name, start, wire_start, _, wire in amounts.GATES:
            with self.subTest(gate=name):
                constraints = artifact['constraints'][start:start + 128]
                for i, constraint in enumerate(constraints[:127]):
                    self.assertEqual(constraint, [[(0, r.P - 1), (wire_start + i, 1)],
                                                  [(wire_start + i, 1)], []])
                a, b, c = constraints[127]
                self.assertEqual(a, [(0, r.P - 1)] + b)
                self.assertEqual(c, [])
                scaled = sorted((w, (2**127 * coefficient) % r.P) for w, coefficient in b)
                target = [(wire, 1)] if wire is not None else [(10, 1), (11, 1), (94, r.P-1), (95, r.P-1), (96, r.P-1)]
                target += [(wire_start + i, (-2**i) % r.P) for i in range(127)]
                self.assertEqual(scaled, sorted(target))


if __name__ == '__main__':
    unittest.main()

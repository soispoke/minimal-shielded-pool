import unittest
import sink_gates as sink
import r1cs_artifact as r


def output_assignment(inners, values):
    """Concrete inverse witnesses for the two output gate fragments."""
    wires = {0: 1}
    for k, (inner, value) in enumerate(zip(inners, values)):
        wires[92 + k], wires[94 + k] = inner, value
        for x, out_wire, inv_wire in [(1-inner, 13904+2*k, 13905+2*k),
                                      (2-inner, 13908+2*k, 13909+2*k),
                                      (value, 13912+2*k, 13913+2*k)]:
            x %= r.P
            wires[out_wire] = int(x == 0)
            wires[inv_wire] = pow(x, -1, r.P) if x else 0
    return wires


class SinkGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        cls.constraints = r.parse_r1cs(cls.data, pinned_compat=True)['constraints']

    def failed_constraints(self, wires):
        def evaluate(side):
            return sum(coefficient * wires[wire] for wire, coefficient in side) % r.P
        return {i for i in [*sink.CONTROLS, *sink.GADGETS]
                if (evaluate(self.constraints[i][0]) * evaluate(self.constraints[i][1])
                    - evaluate(self.constraints[i][2])) % r.P != 0}

    def test_exact_data(self):
        self.assertEqual(sink.render(self.data).encode(), sink.DESTINATION.read_bytes())

    def test_changed_r1cs_rejected(self):
        data = bytearray(self.data)
        data[-1] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            sink.render(data)

    def test_valid_zero_and_positive_outputs(self):
        for inners, values in [([1, 2], [0, 0]), ([3, 4], [5, 6]),
                               ([1, 7], [0, 8]), ([9, 2], [10, 0])]:
            with self.subTest(inners=inners, values=values):
                self.assertEqual(self.failed_constraints(output_assignment(inners, values)), set())

    def test_each_control_rejects_its_forbidden_output(self):
        # Each witness violates R7 and exactly the named control. Deleting that
        # control admits it to this fragment. This is not a whole-R1CS witness.
        cases = [(468, [3, 2], [0, 0]), (469, [1, 2], [7, 0]),
                 (470, [2, 2], [7, 0]), (471, [1, 3], [0, 0]),
                 (472, [1, 1], [0, 7]), (473, [1, 2], [0, 7])]
        for control, inners, values in cases:
            with self.subTest(control=control):
                self.assertEqual(self.failed_constraints(output_assignment(inners, values)), {control})


if __name__ == '__main__':
    unittest.main()

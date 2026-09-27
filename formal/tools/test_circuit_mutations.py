#!/usr/bin/env python3
"""Focused validator regressions; the full runner checks actual compiled cases."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import circuit_mutations as m


class MutationChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (m.ROOT / 'circuits/spend.circom').read_text()
        cls.cases = m.input_cases()

    def test_exact_relation_failure_for_each_input(self):
        for name, inp in self.cases.items():
            with self.subTest(name=name):
                result = m.semantics(inp)
                self.assertEqual(result['failed_clauses'], m.EXPECTED_FAILURE[name])
                self.assertTrue(result['integer_conservation'])

    def test_source_mutations_are_guarded_and_preserve_output_distinctness(self):
        for name in m.EXPECTED_FAILURE:
            changed = m.mutate(self.source, name)
            self.assertIn('    sameOutput.out === 0;', changed)
            self.assertIn('        outCm[k] = Poseidon(3);', changed)
            self.assertIn('    component sameNullifier = IsEqual();', changed)
        with self.assertRaises(ValueError):
            m.mutate(m.mutate(self.source, 'membership'), 'membership')
        with self.assertRaises(ValueError):
            m.mutate(self.source + '\n    sameNullifier.out === 0;\n', 'duplicate')

    def test_statement_coordinate_mutation_is_rejected(self):
        inp = self.cases['baseline']
        expected = [int(v) for v in m.semantics(inp)['statement']]
        expected[0] = (expected[0] + 1) % m.P
        with self.assertRaisesRegex(ValueError, 'statement disagrees'):
            m.semantics(inp, expected)

    def test_independent_equation_checker_rejects_bad_witness(self):
        decoded = dict(prime=str(m.P), wires=2, constraint_count=1,
                       constraints=[[[[1, '1']], [[1, '1']], [[0, '4']]]], witness=['1', '2'])
        self.assertEqual(m.check_constraints(decoded, [1, 2])['constraints_checked'], 1)
        decoded['witness'][1] = '3'
        with self.assertRaisesRegex(ValueError, 'constraint failures'):
            m.check_constraints(decoded, [1, 3])

    def test_independent_equation_checker_rejects_bad_metadata(self):
        decoded = dict(prime=str(m.P), wires=2, constraint_count=1,
                       constraints=[[[[1, str(m.P)]], [], []]], witness=['1', '2'])
        with self.assertRaisesRegex(ValueError, 'coefficient'):
            m.check_constraints(decoded, [1, 2])
        decoded['constraints'] = [[[ [1, '1'], [1, '1'] ], [], []]]
        with self.assertRaisesRegex(ValueError, 'coefficient'):
            m.check_constraints(decoded, [1, 2])

    def test_wtns_decoder_rejects_trailing_bytes_and_noncanonical_values(self):
        def u(v, n):
            return v.to_bytes(n, 'little')
        def binary(value):
            header = u(32, 4) + u(m.P, 32) + u(2, 4)
            data = u(1, 32) + u(value, 32)
            return b'wtns' + u(2, 4) + u(2, 4) + u(1, 4) + u(len(header), 8) + header + u(2, 4) + u(len(data), 8) + data
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'test.wtns'
            path.write_bytes(binary(2))
            self.assertEqual(m.read_wtns(path), [1, 2])
            path.write_bytes(binary(2) + b'\0')
            with self.assertRaises(ValueError):
                m.read_wtns(path)
            path.write_bytes(binary(m.P))
            with self.assertRaisesRegex(ValueError, 'noncanonical'):
                m.read_wtns(path)


if __name__ == '__main__':
    unittest.main()

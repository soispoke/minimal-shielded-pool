"""Mutation tests for exact constraint-occurrence coverage generation."""
import unittest
from constraint_coverage import MAP, ROOT, DESTINATION, InvalidArtifact, segments, validate, group_pieces, render


class ConstraintCoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mapping = MAP.read_bytes()
        cls.data = (ROOT/'build/spend.r1cs').read_bytes()
        cls.rows = segments(cls.mapping)

    def test_partition_counts(self):
        ownership = validate(self.rows)
        self.assertEqual(sum(map(len, ownership.values())), 14802)
        self.assertEqual({k: len(ownership[k]) for k in ['gamma', 'beta', 'ranges', 'controls', 'paths']},
                         dict(gamma=9, beta=459, ranges=1088, controls=26, paths=122))
        self.assertEqual(sum(len(v) for k, v in ownership.items() if k.startswith('small ')), 13098)

    def test_group_boundaries(self):
        sizes = [sum(count for _, _, count in group) for group in group_pieces(self.rows)]
        self.assertEqual(sizes, [256]*57 + [210])

    def test_missing_actual_occurrence_rejected(self):
        with self.assertRaisesRegex(InvalidArtifact, 'gap or overlapping'):
            validate(self.rows[:2] + self.rows[3:])

    def test_duplicate_local_occurrence_rejected(self):
        rows = self.rows.copy()
        n = next(i for i, row in enumerate(rows) if row[0] == 634)
        start, length, family, offset = rows[n]
        rows[n] = (start, length, family, offset-1)
        with self.assertRaisesRegex(InvalidArtifact, 'duplicated or missing local'):
            validate(rows)

    def test_changed_artifact_rejected(self):
        with self.assertRaisesRegex(InvalidArtifact, 'pinned R1CS'):
            render(self.data[:-1] + bytes([self.data[-1]^1]), self.mapping)

    def test_regeneration(self):
        self.assertEqual(DESTINATION.read_text(), render(self.data, self.mapping))


if __name__ == '__main__':
    unittest.main()

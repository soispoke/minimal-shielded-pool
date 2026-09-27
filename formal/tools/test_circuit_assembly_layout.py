"""Mutation checks for physical circuit ownership and shared reads."""
import unittest
from circuit_assembly_layout import ROOT, PLAN, MAP, InvalidArtifact, prepare, exports, validate


class CircuitAssemblyLayoutTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=(ROOT/'build/spend.r1cs').read_bytes()
        cls.plan=PLAN.read_bytes()
        cls.mapping=MAP.read_bytes()

    def test_exact_counts(self):
        spans,outputs=prepare(self.data,self.plan,self.mapping)
        counts=[sum(hi-lo for lo,hi in ss) for ss in spans]
        self.assertEqual(len(spans),59)
        self.assertEqual(counts[0],459)
        self.assertEqual(sum(counts[1:55]),13098)
        self.assertEqual(counts[55:],[1080,19,8,0])
        self.assertEqual(len(outputs),55)

    @staticmethod
    def miniature():
        return [{i} for i in range(55)]+[set() for _ in range(4)],list(range(55)),[[] for _ in range(59)]

    def test_overlap_rejected(self):
        ownership,outputs,ranges=self.miniature()
        ownership[55].add(54)
        with self.assertRaisesRegex(InvalidArtifact,'write sets overlap'):
            validate(ownership,outputs,ranges,[])

    def test_extra_boundary_write_rejected(self):
        ownership,outputs,ranges=self.miniature()
        ownership[0].add(55)
        with self.assertRaisesRegex(InvalidArtifact,'boundary intersection'):
            validate(ownership,outputs,ranges,[])

    def test_unowned_read_rejected(self):
        ownership,outputs,ranges=self.miniature()
        ranges[0]=[0]
        with self.assertRaisesRegex(InvalidArtifact,'unsupported read'):
            validate(ownership,outputs,ranges,[([(1000,1)],[],[])])

    def test_changed_plan_rejected(self):
        with self.assertRaisesRegex(InvalidArtifact,'assignment plan pin'):
            prepare(self.data,self.plan+b' ',self.mapping)

    def test_regeneration(self):
        for file,expected in exports(self.data,self.plan,self.mapping).items():
            self.assertEqual(file.read_text(),expected,file.name)


if __name__=='__main__':
    unittest.main()

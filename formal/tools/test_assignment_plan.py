import json
import os
from pathlib import Path
import unittest
import assignment_plan as plan
import r1cs_artifact as r


class AssignmentPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=(r.ROOT/'build/spend.r1cs').read_bytes()
        cls.source=(r.ROOT/'circuits/spend.circom').read_bytes()
        modules=Path(os.environ.get('MSP_NODE_MODULES',r.ROOT/'tooling/node_modules'))
        cls.constants=(modules/'circomlib/circuits/poseidon_constants.circom').read_bytes()
        cls.sym=Path(os.environ['MSP_SPEND_SYM']).read_bytes()

    def test_exact_plan_and_coverage(self):
        rendered=plan.render(self.data,self.sym,self.source,self.constants)
        self.assertEqual(rendered,plan.DESTINATION.read_bytes())
        report=json.loads(rendered)
        self.assertEqual(report['coverage']['wires'],14842)
        self.assertEqual(report['coverage']['constraints'],14802)
        self.assertEqual(len(report['hash_blocks']),55)
        self.assertTrue(all(not b['unresolved_after_scalar_solves'] for b in report['hash_blocks'][1:]))
        beta=report['hash_blocks'][0]
        self.assertEqual(beta['full_inverse_rank'],153)
        self.assertEqual(len(beta['inverse_wire_forms']),153)

    def test_pinned_mutation_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'exact pinned'):
            plan.analyze(self.data+b'\0',self.sym,self.source,self.constants)

    def test_symbol_mutation_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'symbol SHA-256'):
            plan.analyze(self.data,self.sym+b'\n',self.source,self.constants)

    def test_singular_alias_matrix_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'singular'):
            plan.solve_matrix([[(7,1),(8,1)],[(7,2),(8,2)]])

    def test_coupled_invertible_aliases(self):
        forms=[[(0,11),(7,1),(8,1)],[(7,1),(8,2)]]
        self.assertEqual(plan.triangular_plan(forms)[1],[7,8])
        wires,inverse=plan.solve_matrix(forms)
        self.assertEqual(wires,[7,8])
        self.assertEqual(inverse,[[(0,2),(1,r.P-1)],[(0,r.P-1),(1,1)]])
        inverse[0][0]=(0,3)
        with self.assertRaisesRegex(r.InvalidArtifact,'invalid inverse'):
            plan.verify_inverse([[1,1],[1,2]],inverse)

    def test_wire_collision_rejected(self):
        owners={}
        plan.claim(owners,[5,6],'first hash')
        with self.assertRaisesRegex(r.InvalidArtifact,'collision at 6'):
            plan.claim(owners,[6,7],'second hash')


if __name__=='__main__':unittest.main()

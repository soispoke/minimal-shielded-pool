import ast
import re
import unittest
import path_gates as gates
import r1cs_artifact as r


class PathGatesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data, cls.artifact = r.read_pinned(r.ROOT/'build/spend.r1cs')

    def test_changed_artifact_rejected(self):
        data = bytearray(self.data)
        data[-1] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            gates.render(data, b'')

    def test_unpinned_symbols_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact, 'symbol SHA-256'):
            gates.render(self.data, b'')

    def test_all_raw_constraint_literals_match_pinned_bytes(self):
        text = gates.DESTINATION.read_text()
        literals = [ast.literal_eval('['+literal+']')
                    for literal in re.findall(r'⟨(.*?)⟩', text)]
        fragments = [self.artifact['constraints'][start:end+1] for start,end in gates.LOCATIONS]
        expected = fragments[0]+fragments[1]
        expected += [c[2*i] for c in fragments for i in range(20)]
        expected += [c[2*i+1] for c in fragments for i in range(20)]
        expected += [c[40] for c in fragments]
        self.assertEqual(literals, expected)

    def holds(self, constraint, wires):
        def ev(side):
            return sum(coefficient*wires[wire] for wire,coefficient in side)%r.P
        a,b,c = constraint
        return (ev(a)*ev(b)-ev(c))%r.P == 0

    def test_each_selector_rejects_wrong_selected_output(self):
        # Fragment witnesses only; this does not assert full-R1CS satisfiability.
        for k,(start,end) in enumerate(gates.LOCATIONS):
            for i in range(20):
                cur = [770,7100][k]+i
                left = [730,7060][k]+i
                right = [750,7080][k]+i
                bit = [52,72][k]+i
                sibling = [12,32][k]+i
                for b in [0,1]:
                    wires={cur:101,sibling:307,bit:b,left:307 if b else 101,right:101 if b else 307}
                    for j,out in enumerate([left,right]):
                        constraint=self.artifact['constraints'][start+2*i+j]
                        self.assertTrue(self.holds(constraint,wires))
                        mutated=dict(wires)
                        mutated[out]+=1
                        self.assertFalse(self.holds(constraint,mutated))

    def test_gated_root_requires_agreement_only_for_nonzero_value(self):
        for k,(_,end) in enumerate(gates.LOCATIONS):
            constraint=self.artifact['constraints'][end]
            final=[790,7120][k]
            value=10+k
            for amount in [0,1,r.P-1]:
                self.assertTrue(self.holds(constraint,{4:31,final:31,value:amount}))
                self.assertEqual(self.holds(constraint,{4:31,final:37,value:amount}),amount==0)


if __name__ == '__main__':
    unittest.main()

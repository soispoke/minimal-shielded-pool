import copy
import json
import os
from pathlib import Path
import unittest
from unittest.mock import patch
import hash_instances as inventory
import r1cs_artifact as r


class HashInstanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dependencies=Path(os.environ.get('MSP_NODE_MODULES',r.ROOT/'tooling/node_modules'))
        cls.data=(r.ROOT/'build/spend.r1cs').read_bytes()
        cls.source=(r.ROOT/'circuits/spend.circom').read_bytes()
        cls.constants=(cls.dependencies/'circomlib/circuits/poseidon_constants.circom').read_bytes()
        if 'MSP_SPEND_SYM' in os.environ:
            cls.sym=Path(os.environ['MSP_SPEND_SYM']).read_bytes()
        else:
            data,_,rows=r.reproduce(cls.dependencies)
            if data!=cls.data:raise AssertionError('recompiled R1CS differs')
            cls.sym=''.join(f'{v["label"]},{-1 if v["wire"] is None else v["wire"]},{v["component"]},{n}\n'
                            for n,v in sorted(rows.items(),key=lambda row:row[1]['label'])).encode()

    def test_exact_inventory(self):
        rendered=inventory.render(self.data,self.sym,self.source,self.constants)
        self.assertEqual(rendered,inventory.DESTINATION.read_bytes())
        records=json.loads(rendered)['instances']
        self.assertEqual(len(records),54)
        self.assertEqual(sum(r['arity']==2 for r in records),46)
        self.assertEqual(sum(r['arity']==3 for r in records),8)
        self.assertEqual(sum(r['constraint_end_exclusive']-r['constraint_start'] for r in records),13098)

    def test_mutated_r1cs_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'exact pinned'):
            inventory.analyze(self.data+b'\0',self.sym,self.source,self.constants)

    def test_mutated_symbols_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'symbol SHA-256'):
            inventory.analyze(self.data,self.sym+b'\n',self.source,self.constants)

    def test_mutated_source_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'circuit source changed'):
            inventory.analyze(self.data,self.sym,self.source+b'\n',self.constants)

    def test_mutated_constants_rejected(self):
        with self.assertRaisesRegex(r.InvalidArtifact,'optimized constants changed'):
            inventory.analyze(self.data,self.sym,self.source,self.constants+b'\n')

    def test_changed_affine_output_rejected_after_local_triple_checks(self):
        artifact=copy.deepcopy(r.parse_r1cs(self.data,pinned_compat=True))
        artifact['constraints'][699][2].append((0,1))
        with patch.object(inventory,'parse_r1cs',return_value=artifact):
            with self.assertRaisesRegex(r.InvalidArtifact,'prefix affine mismatch'):
                inventory.analyze(self.data,self.sym,self.source,self.constants)


if __name__=='__main__':unittest.main()

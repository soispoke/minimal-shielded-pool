import json
import unittest
from unittest.mock import patch
import assignment_recovery as recovery
import r1cs_artifact as r


class AssignmentRecoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=(r.ROOT/'build/spend.r1cs').read_bytes()

    def test_generated_proof_modules_match(self):
        files=recovery.render(self.data)
        self.assertEqual(len(files),22)
        for name,text in files.items():
            with self.subTest(name=name):
                self.assertEqual(text,(recovery.DESTINATION/name).read_text())

    def test_recovery_matches_frozen_inventory(self):
        beta=json.loads((r.ROOT/'formal/Artifacts/assignment-plan.json').read_text())['hash_blocks'][0]
        expected=[(w,[(i,int(c)) for i,c in form]) for w,form in beta['inverse_wire_forms']]
        self.assertEqual(recovery.prepare(self.data),expected)

    def test_small_generated_modules_match(self):
        files=recovery.render_small(self.data)
        self.assertEqual(len(files),60)
        for name,text in files.items():
            with self.subTest(name=name):
                self.assertEqual(text,(recovery.DESTINATION/name).read_text())

    def test_small_templates_cover_disjoint_write_sets(self):
        templates,instances=recovery.prepare_small(self.data)
        self.assertEqual([len(t['recovered']) for t in templates],[80,86,85])
        self.assertEqual(len(instances),54)
        wires=[w for inst in instances for w in inst['wires']]
        self.assertEqual(len(wires),4366)
        self.assertEqual(len(set(wires)),4366)
        self.assertNotIn(0,wires)

    def test_changed_frozen_map_pin_rejected(self):
        with patch.object(recovery,'SMALL_PLAN_PIN','0'*64):
            with self.assertRaisesRegex(r.InvalidArtifact,'frozen assignment plan changed'):
                recovery.prepare_small(self.data)

    def test_mutated_artifact_rejected(self):
        changed=bytearray(self.data)
        changed[len(changed)//2]^=1
        with self.assertRaisesRegex(r.InvalidArtifact,'exact pinned'):
            recovery.prepare(bytes(changed))


if __name__=='__main__':unittest.main()

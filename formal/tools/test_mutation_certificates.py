import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import mutation_certificates as c


class MutationCertificates(unittest.TestCase):
    def test_all_archives_and_complete_decodings(self):
        for name, count in [('membership', 14800), ('range', 14674),
                            ('duplicate', 14803), ('sink', 14796)]:
            with self.subTest(name=name):
                artifact, values, _ = c.load(name)
                self.assertEqual(len(artifact['constraints']), count)
                self.assertEqual(len(values), artifact['header']['wires'])
                self.assertEqual(values[0], 1)

    def test_changed_binary_or_wrong_case_rejected_before_normalization(self):
        path = c.EVIDENCE / 'membership'
        with tarfile.open(path / 'artifacts.tar.gz') as t:
            raw = t.extractfile('spend.r1cs').read()
        digest = json.loads((path / 'result.json').read_text())['decoded_constraints_sha256']
        changed = bytearray(raw)
        changed[-1] ^= 1
        for name, data in [('membership', bytes(changed)), ('range', raw)]:
            with self.assertRaisesRegex(ValueError, 'unknown mutant'):
                c.decode_mutant(name, data, digest)
        with self.assertRaisesRegex(ValueError, 'decodings disagree'):
            c.decode_mutant('membership', raw, '0' * 64)

    def test_changed_canonical_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'circuits').mkdir()
            (root / 'circuits/spend.circom').write_text('different source')
            with mock.patch.object(c, 'ROOT', root):
                with self.assertRaisesRegex(ValueError, 'canonical source pin mismatch'):
                    c.load('membership')


if __name__ == '__main__':
    unittest.main()

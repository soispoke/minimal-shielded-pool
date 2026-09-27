#!/usr/bin/env python3
"""Negative tests hit structural parsing separately from the digest gate."""
from pathlib import Path
import struct
import tempfile
import unittest

import r1cs_artifact as r
import compression_fragment as compression


def u32(n):
    return struct.pack('<I', n)


def u64(n):
    return struct.pack('<Q', n)


def fixture(*, modulus=r.P, wires=3, labels=None, coefficient=1, term_wire=1,
            duplicate_term=False, declared=3, section_order=(1, 2, 3), trailing=b''):
    labels = [0, 1, 2] if labels is None else labels
    header = u32(32) + modulus.to_bytes(32, 'little') + u32(wires) + u32(1) + u32(1) + u32(0) + u64(3) + u32(1)
    term = u32(term_wire) + coefficient.to_bytes(32, 'little')
    lc = u32(2 if duplicate_term else 1) + term * (2 if duplicate_term else 1)
    constraints = lc + u32(1) + u32(0) + (1).to_bytes(32, 'little') + lc
    sections = {1: header, 2: constraints, 3: b''.join(u64(x) for x in labels)}
    return b'r1cs' + u32(1) + u32(declared) + b''.join(u32(k) + u64(len(sections[k])) + sections[k] for k in section_order) + trailing


class ParserTests(unittest.TestCase):
    def rejected(self, data):
        with self.assertRaises(r.InvalidArtifact):
            r.parse_r1cs(data, pinned_compat=True)

    def test_valid_and_section_order(self):
        a = r.parse_r1cs(fixture())
        b = r.parse_r1cs(fixture(section_order=(2, 1, 3)))
        self.assertEqual(a['constraints'], [[[(1, 1)], [(0, 1)], [(1, 1)]]])
        self.assertEqual(a['constraints'], b['constraints'])

    def test_every_truncation(self):
        data = fixture()
        for size in range(len(data)):
            with self.subTest(size=size):
                self.rejected(data[:size])

    def test_bad_header_and_sections(self):
        good = fixture()
        for data in [b'R1CS' + good[4:], good[:4] + u32(2) + good[8:],
                     fixture(declared=5), fixture(section_order=(1, 2, 2)),
                     fixture(section_order=(1, 2)), fixture(trailing=b'x'),
                     fixture(modulus=r.P + 1), fixture(wires=0),
                     fixture(labels=[1, 0, 2]), fixture(labels=[0, 1, 3]),
                     fixture(labels=[0, 1, 1]), fixture(labels=[0, 1])]:
            with self.subTest(data=data[:32]):
                self.rejected(data)
        malformed = bytearray(good)
        malformed[16:24] = u64(2**64 - 1)
        self.rejected(malformed)
        malformed = bytearray(good)
        malformed[12:16] = u32(4)
        self.rejected(malformed)
        malformed = bytearray(good)
        malformed[24:28] = u32(64)
        self.rejected(malformed)

    def test_terms(self):
        for args in [dict(coefficient=r.P), dict(term_wire=3), dict(duplicate_term=True)]:
            with self.subTest(args=args):
                self.rejected(fixture(**args))

    def test_huge_counts_are_bounded_by_payload(self):
        data = bytearray(fixture())
        data[84:88] = u32(2**32 - 1)  # header nConstraints
        self.rejected(data)
        data = bytearray(fixture())
        data[100:104] = u32(2**32 - 1)  # first LC term count
        self.rejected(data)

    def test_pin_rejects_structurally_valid_alternative(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'alternative.r1cs'
            path.write_bytes(fixture())
            with self.assertRaisesRegex(r.InvalidArtifact, 'SHA-256'):
                r.read_pinned(path)

    def test_pinned_defect_and_mutation(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        artifact = r.parse_r1cs(data, pinned_compat=True)
        self.assertEqual(artifact['header']['constraints'], 14802)
        self.assertEqual(artifact['header']['wires'], 14842)
        with self.assertRaisesRegex(r.InvalidArtifact, 'section count mismatch'):
            r.parse_r1cs(data)
        mutant = bytearray(data)
        mutant[32] ^= 1  # first coefficient, still structurally valid field value
        self.rejected(mutant)  # compatibility does not generalize to mutations
        fixed_header = data[:8] + u32(3) + data[12:]
        self.assertEqual(r.parse_r1cs(fixed_header)['constraints'], artifact['constraints'])
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'fixed-header.r1cs'
            path.write_bytes(fixed_header)
            with self.assertRaisesRegex(r.InvalidArtifact, 'SHA-256'):
                r.read_pinned(path)

    def test_export_is_deterministic_and_requires_pinned_provenance(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        with tempfile.TemporaryDirectory() as tmp:
            a, b = Path(tmp) / 'A.lean', Path(tmp) / 'B.lean'
            r.export_lean(data, a)
            r.export_lean(data, b)
            self.assertEqual(a.read_bytes(), b.read_bytes())
            self.assertEqual(a.read_bytes(), (r.ROOT / 'formal/Artifacts/Spend.lean').read_bytes())
            r.check_lean(data, a)
            b.write_bytes(b.read_bytes().replace(b'(98, ', b'(97, ', 1))
            with self.assertRaisesRegex(r.InvalidArtifact, 'Lean constraints differ'):
                r.check_lean(data, b)
            self.assertIn(r.PIN, a.read_text())
            self.assertIn(f'⟨[(98, {r.P - 1})], [(1, 1), (3, 1)], [(97, 1), (110, {r.P - 1})]⟩', a.read_text())
            with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
                r.export_lean(fixture(), b)


class CompressionFragmentTests(unittest.TestCase):
    def test_exact_pinned_prefix_is_the_checked_in_data(self):
        data = (r.ROOT / 'build/spend.r1cs').read_bytes()
        self.assertEqual(compression.render(data).encode('utf-8'), compression.DESTINATION.read_bytes())

    def test_fragment_rejects_mutated_artifact(self):
        data = bytearray((r.ROOT / 'build/spend.r1cs').read_bytes())
        data[32] ^= 1
        with self.assertRaisesRegex(r.InvalidArtifact, 'exact pinned'):
            compression.render(data)


if __name__ == '__main__':
    unittest.main()

"""Provenance negative controls for the width-11 optimized data generator."""

import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import optimized_generate as generator


class OptimizedProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.dependencies = Path(os.environ.get(
            "MSP_NODE_MODULES", generator.ROOT / "tooling/node_modules"))

    def test_committed_data_is_exact_export(self):
        self.assertEqual(
            (generator.HERE / "OptimizedData.lean").read_bytes(),
            generator.render(self.dependencies))

    def test_changed_optimized_source_rejected(self):
        relative = Path("circomlib/circuits/poseidon_constants.circom")
        with tempfile.TemporaryDirectory(prefix="msp-optimized-source-") as directory:
            root = Path(directory)
            altered = root / relative
            altered.parent.mkdir(parents=True)
            altered.write_bytes((self.dependencies / relative).read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "optimized Circom constants changed"):
                generator.prepare(root)

    def test_changed_reference_source_rejected(self):
        relative = Path("reference/poseidon_bn254_constants.json")
        with tempfile.TemporaryDirectory(prefix="msp-optimized-reference-") as directory:
            root = Path(directory)
            altered = root / relative
            altered.parent.mkdir(parents=True)
            altered.write_bytes((generator.ROOT / relative).read_bytes() + b"\n")
            with patch.object(generator, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "reference constants changed"):
                    generator.prepare(self.dependencies)


if __name__ == "__main__":
    unittest.main()

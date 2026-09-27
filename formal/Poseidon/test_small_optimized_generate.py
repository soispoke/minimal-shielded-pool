"""Exact-export and provenance controls for width-3/4 proof specializations."""

import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import small_optimized_generate as generator


class SmallOptimizedProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.dependencies = Path(os.environ.get(
            "MSP_NODE_MODULES", generator.ROOT / "tooling/node_modules"))

    def test_all_committed_files_are_exact_exports(self):
        for name, expected in generator.outputs(self.dependencies).items():
            with self.subTest(file=name):
                self.assertEqual((generator.HERE / name).read_bytes(), expected)

    def test_changed_optimized_source_rejected(self):
        relative = Path("circomlib/circuits/poseidon_constants.circom")
        with tempfile.TemporaryDirectory(prefix="msp-small-optimized-source-") as directory:
            root = Path(directory)
            altered = root / relative
            altered.parent.mkdir(parents=True)
            altered.write_bytes((self.dependencies / relative).read_bytes() + b"\n")
            for width in generator.WIDTHS:
                with self.subTest(width=width):
                    with self.assertRaisesRegex(ValueError, "optimized Circom constants changed"):
                        generator.prepare(root, width)

    def test_changed_reference_source_rejected(self):
        relative = Path("reference/poseidon_bn254_constants.json")
        with tempfile.TemporaryDirectory(prefix="msp-small-optimized-reference-") as directory:
            root = Path(directory)
            altered = root / relative
            altered.parent.mkdir(parents=True)
            altered.write_bytes((generator.ROOT / relative).read_bytes() + b"\n")
            with patch.object(generator, "ROOT", root):
                for width in generator.WIDTHS:
                    with self.subTest(width=width):
                        with self.assertRaisesRegex(ValueError, "reference constants changed"):
                            generator.prepare(self.dependencies, width)

    def test_unlisted_width_rejected(self):
        with self.assertRaisesRegex(ValueError, "unsupported width"):
            generator.prepare(self.dependencies, 11)


if __name__ == "__main__":
    unittest.main()

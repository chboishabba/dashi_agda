import importlib.util
import pathlib
import sys
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).with_name("adk_pdb_cv_fixture.py")


class FixtureScriptTests(unittest.TestCase):
    def load(self):
        spec = importlib.util.spec_from_file_location("adk_pdb_cv_fixture", SCRIPT)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module

    def atomline(self, serial, name, residue, x, y, z, chain="A", alt="", element="C"):
        return (
            f"ATOM  {serial:5d} {name:>4s}{alt:1s}ALA {chain:1s}{residue:4d}    "
            f"{x:8.3f}{y:8.3f}{z:8.3f}  1.00 10.00          {element:>2s}  \n"
        )

    def minimal(self, shift=(0, 0, 0), model=None):
        points = [
            (1, (0, 0, 0)),
            (50, (1, 0, 0)),
            (79, (0, 1, 0)),
            (104, (0, 2, 0)),
            (123, (1, 1, 0)),
            (161, (1, 2, 0)),
            (190, (0, 3, 0)),
        ]
        text = f"MODEL     {model}\n" if model is not None else ""
        for serial, (residue, point) in enumerate(points, 1):
            xyz = tuple(point[index] + shift[index] for index in range(3))
            text += self.atomline(serial, "CA", residue, *xyz)
        if model is not None:
            text += "ENDMDL\n"
        return text

    def test_translation_invariance(self):
        m = self.load()
        first = m.evaluate_adk_cv(m.parse_pdb_text(self.minimal(), "A"))
        shifted = m.evaluate_adk_cv(
            m.parse_pdb_text(self.minimal((5, -2, 9)), "A")
        )
        self.assertAlmostEqual(first["theta1_degrees"], shifted["theta1_degrees"], 12)
        self.assertAlmostEqual(
            first["dln_angstrom"]["domain_backbone"],
            shifted["dln_angstrom"]["domain_backbone"],
            12,
        )

    def test_explicit_model_selection(self):
        m = self.load()
        text = self.minimal(model=1) + self.minimal((10, 0, 0), model=2)
        first = m.parse_pdb_text(text, "A", model=1)
        second = m.parse_pdb_text(text, "A", model=2)
        self.assertEqual({atom.model for atom in first}, {1})
        self.assertEqual({atom.model for atom in second}, {2})
        self.assertNotEqual(first[0].x, second[0].x)

    def test_missing_chain_fails_closed(self):
        m = self.load()
        with self.assertRaises(ValueError):
            m.parse_pdb_text(self.minimal(), "B")

    def test_malformed_selected_record_fails_closed(self):
        m = self.load()
        good = self.atomline(1, "CA", 1, 0, 0, 0)
        bad = good[:30] + "NOTFLOAT" + good[38:]
        with self.assertRaises(ValueError):
            m.parse_pdb_text(bad, "A")

    def test_receipt_has_schema_hashes_and_boundary(self):
        m = self.load()
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "4AKE.pdb"
            path.write_text(self.minimal(), encoding="utf-8")
            receipt = m.file_receipt(path, "A", "blank-or-A", 1, "4AKE")
        self.assertEqual(receipt["artifact_schema"], "dashi.adk.pdb_cv_fixture.v1")
        self.assertEqual(receipt["pdb_deposition_doi"], "10.2210/pdb4AKE/pdb")
        self.assertEqual(len(receipt["source_sha256"]), 64)
        manifests = receipt["cv"]["selection_manifests"]
        self.assertIn("theta1_lid_backbone", manifests)
        self.assertEqual(len(manifests["theta1_lid_backbone"]["sha256"]), 64)
        self.assertFalse(receipt["cv"]["dln_source_atom_subset_resolved"])
        self.assertIn("does not", receipt["promotion_boundary"])


if __name__ == "__main__":
    unittest.main()

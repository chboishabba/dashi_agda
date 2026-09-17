import importlib.util
import pathlib
import sys
import unittest

BASE = pathlib.Path(__file__).with_name("adk_pdb_cv_fixture.py")
CANON = pathlib.Path(__file__).with_name("adk_selection_content.py")


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class SelectionContentTests(unittest.TestCase):
    def setUp(self):
        self.base = load(BASE, "adk_pdb_cv_fixture")
        self.canon = load(CANON, "adk_selection_content")

    def atom(self, serial, residue, x, y, z):
        return self.base.Atom(
            serial=serial,
            name="CA",
            altloc="",
            resname="ALA",
            chain="A",
            residue=residue,
            x=x,
            y=y,
            z=z,
            element="C",
            model=1,
        )

    def test_canonical_rows_are_explicit_and_deterministic(self):
        atoms = [self.atom(2, 123, 1.0, 2.0, 3.0), self.atom(1, 122, 4.0, 5.0, 6.0)]
        packet = self.canon.selection_content_packet(atoms)
        self.assertEqual(packet["schema"], "dashi.adk.selection_content.v1")
        self.assertEqual(packet["mass_source_doi"], self.base.ATOMIC_MASS_DOI)
        self.assertEqual(packet["count"], 2)
        self.assertEqual(packet["rows"], sorted(packet["rows"]))
        self.assertIn("|12.011000|", packet["rows"][0])
        self.assertIn("|4.000|5.000|6.000", packet["rows"][0])

    def test_equal_payload_is_direct_content_evidence_not_hash_inference(self):
        left = [self.atom(1, 122, 4.0, 5.0, 6.0)]
        right = [self.atom(1, 122, 4.0, 5.0, 6.0)]
        self.assertTrue(self.canon.same_selection_content(left, right))

    def test_coordinate_change_breaks_content_equality(self):
        left = [self.atom(1, 122, 4.0, 5.0, 6.0)]
        right = [self.atom(1, 122, 4.001, 5.0, 6.0)]
        self.assertFalse(self.canon.same_selection_content(left, right))

    def test_source_serialization_is_not_part_of_selected_content(self):
        left = [self.atom(1, 122, 4.0, 5.0, 6.0)]
        right = [self.atom(1, 122, 4.0, 5.0, 6.0)]
        self.assertEqual(
            self.canon.selection_content_packet(left)["rows"],
            self.canon.selection_content_packet(right)["rows"],
        )


if __name__ == "__main__":
    unittest.main()

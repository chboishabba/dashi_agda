import importlib.util
import pathlib
import sys
import unittest

SCRIPT = pathlib.Path(__file__).with_name("adk_pdb_cv_fixture.py")


class FixtureScriptTests(unittest.TestCase):
    def load(self):
        spec = importlib.util.spec_from_file_location("adk_pdb_cv_fixture", SCRIPT)
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module

    def test_parses_altloc_policy_and_com_geometry(self):
        m = self.load()
        pdb = """\
ATOM      1  N   ALA A   1       0.000   0.000   0.000  1.00 10.00           N  \nATOM      2  CA AALA A   1       2.000   0.000   0.000  0.60 10.00           C  \nATOM      3  CA BALA A   1      20.000   0.000   0.000  0.40 10.00           C  \nATOM      4  C   ALA A   1       4.000   0.000   0.000  1.00 10.00           C  \nATOM      5  O   ALA A   1       6.000   0.000   0.000  1.00 10.00           O  \n"""
        atoms = m.parse_pdb_text(pdb, chain="A", altloc_policy="blank-or-A")
        self.assertEqual([a.altloc for a in atoms], ["", "A", "", ""])
        com = m.center_of_mass(atoms)
        self.assertGreater(com[0], 2.0)
        self.assertLess(com[0], 4.0)

    def test_angle_is_rigid_translation_invariant(self):
        m = self.load()
        a, b, c = (1.0, 0.0, 0.0), (0.0, 0.0, 0.0), (0.0, 1.0, 0.0)
        self.assertAlmostEqual(m.angle_degrees(a, b, c), 90.0, places=12)
        t = (17.0, -3.0, 9.0)
        add = lambda p: tuple(p[i] + t[i] for i in range(3))
        self.assertAlmostEqual(m.angle_degrees(add(a), add(b), add(c)), 90.0, places=12)

    def test_adk_receipt_keeps_dln_conventions_separate(self):
        m = self.load()
        atoms = []
        serial = 1
        for residue, xyz in [
            (1, (0, 0, 0)),
            (50, (1, 0, 0)),
            (79, (0, 1, 0)),
            (104, (0, 2, 0)),
            (123, (1, 1, 0)),
            (161, (1, 2, 0)),
            (190, (0, 3, 0)),
        ]:
            atoms.append(
                m.Atom(serial, "CA", "", "ALA", "A", residue, *map(float, xyz), "C")
            )
            serial += 1
        receipt = m.evaluate_adk_cv(atoms)
        self.assertIn("domain_backbone", receipt["dln_angstrom"])
        self.assertIn("domain_heavy", receipt["dln_angstrom"])
        self.assertFalse(receipt["dln_source_atom_subset_resolved"])


if __name__ == "__main__":
    unittest.main()

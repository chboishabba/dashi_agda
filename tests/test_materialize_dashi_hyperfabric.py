import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "scripts" / "materialize_dashi_hyperfabric.py"
spec = importlib.util.spec_from_file_location("hf", SCRIPT)
hf = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = hf
spec.loader.exec_module(hf)

REFINE = '''module DASHI.Foundations.SSPPrimeLane369Refinement where
canonicalThreeSixNineDigits : Set
canonicalThreeSixNineDigits =
  addressDigits canonicalThreeSixNineAddress
  ≡ digit-3 ∷ digit-6 ∷ digit-9 ∷ []
'''
FIELD = '''module DASHI.Core.SuperSSP369Field where
rootP3Supervoxel : Set
rootP3Supervoxel =
  mkSuperSSP369Supervoxel
    p3
    sig
    refl
    refinement
    refl
    symmetry
    refl
    evenParity
    canonicalZeroFifteenSSPSurface
    canonicalExampleFifteenSSPSurface

depth3P7Supervoxel : Set
depth3P7Supervoxel =
  mkSuperSSP369Supervoxel
    p7
    sig
    refl
    refinement
    refl
    symmetry
    refl
    oddParity
    canonicalExampleFifteenSSPSurface
    canonicalNegativeFifteenSSPSurface

rootField : Set
rootField =
  mkSuperSSP369Field
    (constantForest zero canonicalZeroFifteenSSPSurface)
    (constantForest zero canonicalExampleFifteenSSPSurface)
    rootP3Supervoxel
    false
    refl

depth3Field : Set
depth3Field =
  mkSuperSSP369Field
    (constantForest depth canonicalExampleFifteenSSPSurface)
    (constantForest depth canonicalNegativeFifteenSSPSurface)
    depth3P7Supervoxel
    false
    refl
'''


class HyperfabricTests(unittest.TestCase):
    def fixture(self):
        temp_dir = tempfile.TemporaryDirectory()
        root = Path(temp_dir.name)
        (root / hf.REFINEMENT_PATH).parent.mkdir(parents=True)
        (root / hf.FIELD_PATH).parent.mkdir(parents=True)
        (root / hf.REFINEMENT_PATH).write_text(REFINE)
        (root / hf.FIELD_PATH).write_text(FIELD)
        return temp_dir, root

    def test_extracts_actual_canonical_address(self):
        temp_dir, root = self.fixture()
        with temp_dir:
            self.assertEqual(hf.build_ir(root)["canonical_address"], [3, 6, 9])

    def test_split_is_derived_from_supervoxel_fields(self):
        temp_dir, root = self.fixture()
        with temp_dir:
            ir = hf.build_ir(root)
            event = next(item for item in ir["events"] if item["id"] == "body-residue-split")
            self.assertEqual(event["kind"], "decomposition")
            self.assertEqual(event["targets"], ("depth3-body", "depth3-residue"))

    def test_every_carrier_and_event_has_source(self):
        temp_dir, root = self.fixture()
        with temp_dir:
            ir = hf.build_ir(root)
            self.assertTrue(all(carrier.get("source") for carrier in ir["carriers"]))
            self.assertTrue(all(event.get("source_ref") for event in ir["events"]))

    def test_svg_contains_derived_transport_not_mock_domains(self):
        temp_dir, root = self.fixture()
        with temp_dir:
            svg = hf.render_svg(hf.build_ir(root))
            self.assertIn("canonicalThreeSixNineDigits", svg)
            self.assertIn("body/residue decomposition", svg)
            self.assertIn("animateMotion", svg)
            for forbidden in ("collision event", "HEPData", "bone collagen", "photosynthesis"):
                self.assertNotIn(forbidden, svg)


if __name__ == "__main__":
    unittest.main()

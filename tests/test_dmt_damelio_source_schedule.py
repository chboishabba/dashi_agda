"""D'Amelio 2026 original source dose/filename provenance: synthetic names only."""
import copy
import unittest

from scripts.audit_dmt_damelio_source_schedule import (
    audit_source, load_source, parse_original_name, validate_source,
    ORIGINAL_HIGH_FIRST)


class OriginalSourceScheduleTests(unittest.TestCase):
    def setUp(self):
        self.source = load_source()
        self.roster = validate_source(self.source)

    def test_original_19_ids_and_counterbalance(self):
        self.assertEqual(len(self.roster), 19)
        self.assertNotIn("S14", self.roster)
        self.assertEqual({p for p, arms in self.roster.items() if arms[0] == "Alta"},
                         ORIGINAL_HIGH_FIRST)
        self.assertTrue(all(set(v) == {"Alta", "Baja"} for v in self.roster.values()))

    def test_source_protocol_not_actual_tet_n18(self):
        result = audit_source(self.source)
        self.assertEqual(result["original_code_protocol_stage_slots"], 76)
        self.assertEqual(result["inspected_filename_slots"], 0)
        self.assertFalse(result["TET_18_participant_claim_reproduced"])

    def test_filename_sample_sources_dose_from_config(self):
        first = parse_original_name("s01_DMT_Session1_DMT.mat", self.roster)
        second = parse_original_name("s01_DMT_Session2_DMT.mat", self.roster)
        self.assertEqual((first["dose"], second["dose"]), ("Alta", "Baja"))
        rest = parse_original_name("s02_RS_Session1_EC.mat", self.roster)
        self.assertEqual(rest["dose"], "Baja")

    def test_complete_constructed_filename_sets_are_only_constructed(self):
        names = []
        for pid in self.roster:
            for session in (1, 2):
                names += [f"{pid}_RS_Session{session}_EC.mat",
                          f"{pid}_DMT_Session{session}_DMT.mat"]
        report = audit_source(self.source, names)
        self.assertEqual(report["inspected_filename_slots"], 76)
        self.assertEqual(len(report["complete_filename_identity_participants"]), 19)
        self.assertFalse(report["source_mat_contents_loaded"])

    def test_source_schedule_single_swap_rejected(self):
        changed = copy.deepcopy(self.source)
        row = next(x for x in changed["scheduled_participant_sessions"] if x["id"] == "S01")
        row["session_1_dose_label"], row["session_2_dose_label"] = (
            row["session_2_dose_label"], row["session_1_dose_label"])
        with self.assertRaises(ValueError):
            validate_source(changed)

    def test_same_count_different_schedule_rejected(self):
        changed = copy.deepcopy(self.source)
        rows = changed["scheduled_participant_sessions"]
        a = next(x for x in rows if x["id"] == "S01")
        b = next(x for x in rows if x["id"] == "S02")
        for x in (a, b):
            x["session_1_dose_label"], x["session_2_dose_label"] = (
                x["session_2_dose_label"], x["session_1_dose_label"])
        with self.assertRaises(ValueError):
            validate_source(changed)

    def test_unknown_subject_rejected(self):
        with self.assertRaises(ValueError):
            parse_original_name("s14_DMT_Session1_DMT.mat", self.roster)

    def test_inconsistent_Rs_suffix_rejected(self):
        with self.assertRaises(ValueError):
            parse_original_name("s01_RS_Session1_DMT.mat", self.roster)

    def test_path_traversal_rejected(self):
        with self.assertRaises(ValueError):
            parse_original_name("../s01_DMT_Session1_DMT.mat", self.roster)

    def test_duplicate_case_insensitive_identity_rejected(self):
        with self.assertRaises(ValueError):
            audit_source(self.source, ["s01_DMT_Session1_DMT.mat",
                                       "S01_DMT_Session1_OTHER.mat"])

    def test_no_ontology_promotion(self):
        result = audit_source(self.source)
        self.assertFalse(result["ethics_and_licence_verified"])
        self.assertFalse(result["observed_data_or_ontology_established"])


if __name__ == "__main__":
    unittest.main()

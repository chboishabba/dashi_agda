"""Synthetic-only DMT TET admission and onset diagnostics; no human records."""
import copy
import unittest

from scripts.audit_dmt_tet_presence_synthetic import (
    CODE_COMMIT, CONFIG_BLOB, DIMENSIONS, SCHEMA, audit, validate)


def fixture():
    records = []
    for person in ("toy-person-A", "toy-person-B"):
        for dose in (20, 40):
            for stage in ("RS", "DMT"):
                for step in (0, 1):
                    values = {name: "0" for name in DIMENSIONS}
                    if stage == "DMT" and dose == 20:
                        if person == "toy-person-A":
                            values["complex_imagery"] = "7"
                            if step == 1:
                                values["entity"] = "6"
                        else:
                            values["entity"] = "7"
                            if step == 1:
                                values["complex_imagery"] = "6"
                    records.append({
                        "person": person, "dose_mg": dose, "stage": stage,
                        "time_index": step, "values": values})
    return {"schema": SCHEMA, "mode": "synthetic",
            "source_id": "synthetic:two-people",
            "code_commit": CODE_COMMIT, "config_blob": CONFIG_BLOB,
            "interval_seconds": 4, "dimensions": list(DIMENSIONS),
            "threshold": "5", "samples": records}


class SourceBoundTetTests(unittest.TestCase):
    def bad(self, doc):
        with self.assertRaises(ValueError):
            validate(doc)

    def test_bidirectional_lag_and_absence(self):
        out = audit(fixture())
        self.assertEqual(len(out["groups"]), 4)
        mapping = {(x["person"], x["dose_mg"]): x for x in out["groups"]}
        self.assertEqual(mapping["toy-person-A", 20]["entity_minus_complex_imagery_seconds"], 4)
        self.assertEqual(mapping["toy-person-B", 20]["entity_minus_complex_imagery_seconds"], -4)
        self.assertIsNone(mapping["toy-person-A", 40]["entity_minus_complex_imagery_seconds"])
        self.assertFalse(out["external_agent_ontology_inferred"])

    def test_report_order_permutation(self):
        a = fixture(); b = copy.deepcopy(a); b["samples"].reverse()
        self.assertEqual(audit(a)["groups"], audit(b)["groups"])

    def test_reject_authorized_research(self):
        d = fixture(); d["mode"] = "authorized_research"
        self.bad(d)

    def test_source_commit_mismatch(self):
        d = fixture(); d["code_commit"] = "unverified"
        self.bad(d)

    def test_removed_entity_dimension(self):
        d = fixture(); d["dimensions"].remove("entity")
        self.bad(d)

    def test_raw_narrative_field(self):
        d = fixture(); d["samples"][0]["narrative"] = "not permitted"
        self.bad(d)

    def test_outside_scale(self):
        d = fixture(); d["samples"][0]["values"]["entity"] = "11"
        self.bad(d)

    def test_false_synthetic_person(self):
        d = fixture(); d["samples"][0]["person"] = "real-study-id"
        self.bad(d)

    def test_missing_four_second_interval(self):
        d = fixture(); d["interval_seconds"] = 30
        self.bad(d)

    def test_missing_timebin(self):
        d = fixture(); d["samples"].pop(0)
        self.bad(d)

    def test_duplicate_timebin(self):
        d = fixture(); d["samples"].append(copy.deepcopy(d["samples"][0]))
        self.bad(d)

    def test_no_zero_threshold(self):
        d = fixture(); d["threshold"] = "0"
        self.bad(d)

    def test_no_unknown_arm(self):
        d = fixture(); d["samples"][0]["dose_mg"] = 60
        self.bad(d)

    def test_no_one_person_cohort(self):
        d = fixture()
        d["samples"] = [x for x in d["samples"] if x["person"] == "toy-person-A"]
        self.bad(d)

    def test_missing_channel_value(self):
        d = fixture(); d["samples"][0]["values"].pop("entity")
        self.bad(d)


if __name__ == "__main__":
    unittest.main()

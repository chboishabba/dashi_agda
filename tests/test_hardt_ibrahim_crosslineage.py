"""Case-specific Ibrahim source genealogy regression: synthetic mutations.
A green test means consistent attribution controls, not event corroboration.
"""
from __future__ import annotations
import copy
import importlib.util
import json
from pathlib import Path
import unittest

SCRIPT=Path(__file__).resolve().parents[1]/"scripts"/"check_hardt_ibrahim_crosslineage.py"
SPEC=importlib.util.spec_from_file_location("hardt_ibrahim_crosslineage",SCRIPT)
mod=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)
BASE=json.loads(mod.DEFAULT.read_text(encoding="utf-8"))

class TestIbrahimRootInvariants(unittest.TestCase):
    def test_original_source_ledger_and_zero_event_witnesses(self):
        result=mod.audit(BASE)
        self.assertEqual(result["source_carriers"],13)
        self.assertEqual(result["published_field_pair_matches"],3)
        self.assertEqual(result["independent_event_witness_records_present"],0)
        self.assertEqual(result["hardt_allegation_speaker_roots"],1)

    def test_new_same_speaker_carrier_not_independent(self):
        doc=copy.deepcopy(BASE)
        new=copy.deepcopy(next(x for x in doc["sources"] if x["id"]=="H26_REEL"))
        new["id"]="H_EXTRA_REPRINT"
        doc["sources"].append(new)
        result=mod.audit(doc)
        self.assertEqual(result["hardt_allegation_carriers"],3)
        self.assertEqual(result["hardt_allegation_speaker_roots"],1)

    def test_unread_original_manuscript_cannot_be_promoted(self):
        doc=copy.deepcopy(BASE)
        next(x for x in doc["sources"] if x["id"]=="H_MANUSCRIPT")["inspection"]="original_experiment_inspected"
        with self.assertRaisesRegex(ValueError,"manuscript"):
            mod.audit(doc)

    def test_different_eighty_percent_statistics_never_join(self):
        doc=copy.deepcopy(BASE)
        next(x for x in doc["sources"] if x["id"]=="H17_JOURNAL")["claims"].append("H_ASSASSINATION")
        with self.assertRaisesRegex(ValueError,"80 percent"):
            mod.audit(doc)

    def test_croft_archive_does_not_create_independent_gentry(self):
        doc=copy.deepcopy(BASE)
        next(x for x in doc["sources"] if x["id"]=="C_ARCHIVE")["author_root"]="Gentry Smith"
        with self.assertRaisesRegex(ValueError,"Gentry/Flanagan"):
            mod.audit(doc)

    def test_original_witness_not_imputed_to_2020_host(self):
        doc=copy.deepcopy(BASE)
        next(x for x in doc["sources"] if x["id"]=="H20_PODCAST")["independent_event_witness"]=True
        with self.assertRaisesRegex(ValueError,"independently authenticated"):
            mod.audit(doc)

    def test_three_published_magnetic_pairs_not_raw_data_identity(self):
        doc=copy.deepcopy(BASE)
        doc["concordance"][0]["raw_trace_same_proved"]=True
        with self.assertRaisesRegex(ValueError,"raw-data"):
            mod.audit(doc)

    def test_modified_table_fails_value_join(self):
        doc=copy.deepcopy(BASE)
        doc["concordance"][0]["b2024_mt"]="4.14"
        with self.assertRaisesRegex(ValueError,"numerical concordance"):
            mod.audit(doc)

    def test_missing_negative_join_fails(self):
        doc=copy.deepcopy(BASE)
        doc["explicit_nonjoins"].pop()
        with self.assertRaisesRegex(ValueError,"negative"):
            mod.audit(doc)

    def test_false_smith_identity_fails(self):
        doc=copy.deepcopy(BASE)
        next(x for x in doc["sources"] if x["id"]=="WBS99")["author_root"]="Gentry Smith"
        with self.assertRaisesRegex(ValueError,"Wilbert"):
            mod.audit(doc)

if __name__=="__main__":
    unittest.main()

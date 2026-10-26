"""Finite source-count and identity firewalls. Not biological data tests."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
import check_hardt_rai_2025_source_denominators as m

class TestRaiProvenance(unittest.TestCase):
    def test_publication_counts(self):
        z=m.audit_metadata()
        self.assertEqual((z['paper_recruited'],z['paper_reported_excluded'],z['paper_retained']),(69,10,59))
    def test_three_event_units(self):
        z=m.audit_metadata()
        self.assertEqual(z['published_event_counts'],[20,18,21])
        self.assertEqual(z['synthetic_max_all_event_pairs'],553)
    def test_catalog_gap_is_not_missing_participants_claim(self):
        z=m.audit_metadata()
        self.assertEqual(z['nominal_record_gap'],2)
        self.assertFalse(z['participant_membership_join_verified'])
    def test_original_code_links_not_assumed_equivalent(self):
        self.assertEqual(len(m.CODE_LOCATORS),2)
        self.assertFalse(m.audit_metadata()['osf_code_identical_or_different_verified'])
    def test_exclusion_arithmetic_detects_revision(self):
        x=copy.deepcopy(m.PAPER);x['lost_technical']=8
        with self.assertRaisesRegex(ValueError,'arithmetic'):m.audit_metadata(x)
    def test_event_count_detects_revision(self):
        x=copy.deepcopy(m.PAPER);x['performances']=(20,18,20)
        with self.assertRaisesRegex(ValueError,'event counts'):m.audit_metadata(x)
    def test_identity_is_not_inferred_from_counts(self):
        one=m.subject_join(('A','B','C'),('A','B'))
        two=m.subject_join(('A','B','C'),('X','Y'))
        self.assertEqual(one['paper_ids'],two['paper_ids'])
        self.assertEqual(one['archive_ids'],two['archive_ids'])
        self.assertNotEqual(one['matched_ids'],two['matched_ids'])
    def test_three_distinct_n57_source_roles(self):
        z=m.audit_cohort_roles()
        self.assertEqual(z['distinct_57_roles'],3)
        self.assertEqual(len(z['equal_number_nonidentity_pairs']),3)
        self.assertIsNone(z['deposited_subjects_match_questionnaire_respondents'])
        self.assertFalse(z['role_count_joins_are_authenticated'])

    def test_duplicate_source_role_rejected(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):
            m.audit_cohort_roles(m.COHORT_ROLES+(m.COHORT_ROLES[0],))

    def test_cinema_not_live_same_object(self):
        from copy import deepcopy
        x=deepcopy(list(m.COHORT_ROLES))
        x[2]['condition']='live-P1-P2-P3'
        with self.assertRaisesRegex(ValueError,'conflated'):
            m.audit_cohort_roles(x)

    def test_equal_57_deposit_not_questionnaire(self):
        from copy import deepcopy
        x=deepcopy(list(m.COHORT_ROLES))
        x[3]['measure']='questionnaire_responses'
        with self.assertRaisesRegex(ValueError,'conflated'):
            m.audit_cohort_roles(x)

    def test_deposit_version_locked_not_subsumed_by_paper(self):
        x=copy.deepcopy(m.DEPOSIT); x['declared_recordings']=59
        with self.assertRaisesRegex(ValueError,'deposit DOI/version/count'):
            m.audit_metadata(deposit=x)

    def test_deposit_foreign_version_rejected(self):
        x=copy.deepcopy(m.DEPOSIT); x['doi']='10.5522/04/28508744.v2'
        with self.assertRaisesRegex(ValueError,'deposit DOI/version/count'):
            m.audit_metadata(deposit=x)

    def test_duplicate_rejected(self):
        with self.assertRaisesRegex(ValueError,'duplicate'):m.subject_join(('A','A'),('A',))
    def test_unattributed_file_not_reanalysis(self):
        with tempfile.TemporaryDirectory() as d:
            f=Path(d)/'manifest.json'
            f.write_text(json.dumps(dict(paper_doi='wrong',deposit_doi=m.DEPOSIT['doi'],paper_retained=59,deposit_declared=57,paper_ids=[],archive_ids=[])))
            with self.assertRaisesRegex(ValueError,'identifiers'):m.audit_manifest_file(f)
    def test_arbitrary_59_57_ids_do_not_authenticate(self):
        with tempfile.TemporaryDirectory() as d:
            f=Path(d)/'manifest.json'
            f.write_text(json.dumps(dict(paper_doi='10.1016/j.isci.2025.112922',deposit_doi=m.DEPOSIT['doi'],paper_retained=59,deposit_declared=57,paper_ids=[f's{i}' for i in range(59)],archive_ids=[f's{i}' for i in range(57)])))
            out=m.audit_manifest_file(f)
            self.assertEqual(out['matched_ids'],57)
            self.assertFalse(out['ids_authenticated_by_original_data'])

if __name__=='__main__':unittest.main()

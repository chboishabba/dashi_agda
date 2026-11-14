"""Synthetic source-bound ITIR negative controls; not real Wikipedia evidence."""
from __future__ import annotations
import copy
import hashlib
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import ibrahim_itir_multilingual_candidate as api


def fixture(language,target,observation):
    txt=f'opening [[{target}]] trailing'
    start=txt.index('[[')
    return dict(qid='Q5891',language=language,title='Synthetic Philosophy',
                page_id=101 if language=='en' else 202,
                revision_id=11001 if language=='en' else 22002,
                wikitext=txt,wikitext_sha256=hashlib.sha256(txt.encode()).hexdigest(),
                selector_policy_ref='fixture:outer-wikilink-v1',
                consumer_ref='fixture:first-link-destination-v1',
                observation=observation, selected_span=[start,start+len(f'[[{target}]]')],
                selected_target=target)


class ConsumerCandidateTests(unittest.TestCase):
    def test_same_qid_different_query_exposes_collision(self):
        result=api.compare_candidate(fixture('en','Science','Science'),
                                     fixture('de','Philosophie','Philosophie'))
        self.assertEqual(result['consumer_status'],'collision_residual')
        self.assertEqual(result['repair_candidate']['retain_coordinate'],'observed_value')
        self.assertFalse(result['human_review_paid'])
        self.assertFalse(result['selected_consumer_licence_paid'])
        self.assertFalse(result['translation_equivalence_paid'])
        self.assertFalse(result['qid_identity_paid'])
        self.assertFalse(result['source_retrieval_paid'])
        self.assertFalse(result['wiki_edit_authority_paid'])
    def test_agreement_is_not_equivalence(self):
        r=api.compare_candidate(fixture('en','Science','same'),fixture('de','Wissenschaft','same'))
        self.assertEqual(r['consumer_status'],'value_agrees_unlicensed')
        self.assertIsNone(r['repair_candidate'])
        self.assertFalse(r['semantic_authority_paid'])
    def test_author_parser_port_rejects_skipping_an_earlier_valid_link(self):
        left=fixture('en','Science','Science')
        right=fixture('de','Philosophie','Philosophie')
        for page in (left,right):
            page['selector_policy_ref']=api.AUTHOR_PORT_POLICY
        compared=api.compare_candidate(left,right)
        self.assertTrue(compared['left']['reference_port_selection_matches'])
        self.assertTrue(compared['right']['reference_port_selection_matches'])
        self.assertFalse(compared['right']['first_qualifying_link_soundness_paid'])
        right['wikitext']='[[Earlier]] '+right['wikitext']
        right['wikitext_sha256']=hashlib.sha256(right['wikitext'].encode()).hexdigest()
        start=right['wikitext'].index('[[Philosophie]]')
        right['selected_span']=[start,start+len('[[Philosophie]]')]
        with self.assertRaisesRegex(ValueError,'author-parser behavioural port'):
            api.compare_candidate(left,right)

    def test_reject_tampered_bytes_links_policy_qid_and_revision(self):
        good=fixture('de','Philosophie','Philosophie')
        left=fixture('en','Science','Science')
        cases=[]
        r=copy.deepcopy(good);r['wikitext_sha256']='0'*64;cases.append(r)
        r=copy.deepcopy(good);r['selected_target']='unrelated';cases.append(r)
        r=copy.deepcopy(good);r['revision_id']=0;cases.append(r)
        r=copy.deepcopy(good);r['qid']='Q123';cases.append(r)
        r=copy.deepcopy(good);r['selector_policy_ref']='different';cases.append(r)
        r=copy.deepcopy(good);r['consumer_ref']='different';cases.append(r)
        r=copy.deepcopy(good);r['selected_span']=[0,5];cases.append(r)
        r=copy.deepcopy(good);r['language']='en';cases.append(r)
        for c in cases:
            with self.subTest(c=c),self.assertRaises(ValueError):
                api.compare_candidate(left,c)

if __name__=='__main__':unittest.main()

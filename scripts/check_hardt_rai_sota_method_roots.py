#!/usr/bin/env python3
"""Original-source Rai code-locator + Oct 2026 EEG-review estimand audit.

This is a source metadata and arithmetic audit, NOT an EEG replication.
Rai et al. (2025) own the empirical study; Jiang, Zou & Yu (2026)
own the meta-analysis; Novembre, Koul & Bigand (2026) own the forum.
"""
from __future__ import annotations
import argparse
import json
from math import tanh
import unittest

RAI_DOI = '10.1016/j.isci.2025.112922'
REVIEW_DOI = '10.1016/j.biopsycho.2026.109367'
FORUM_DOI = '10.1016/j.tins.2026.09.006'

# Four *citation locations* in a paper, not four fetched code repositories.
CODE_REFERENCES = (
    dict(id='paper_availability', url='https://osf.io/uz573/',
         scope='general_analysis_scripts', citing_root=RAI_DOI),
    dict(id='paper_key_resources', url='https://osf.io/ursmc/',
         scope='custom_analysis_scripts', citing_root=RAI_DOI),
    dict(id='cca_method', url='https://osf.io/69gfe/',
         scope='correlated_components_analysis_method_code', citing_root=RAI_DOI),
    dict(id='granger_method', url='https://osf.io/b62d7/',
         scope='performance_feature_granger_analysis_code', citing_root=RAI_DOI),
)

# Counts are within models of ONE meta-analysis, not disjoint studies.
# g and z are distinct effect-size types; r is derived from Fisher z.
MODELS = (
    dict(id='core_condition', question='interaction_condition', metric='hedges_g', k=14,
         estimate=0.887, ci=(0.533, 1.241)),
    dict(id='core_outcome', question='external_outcome_association', metric='fishers_z', k=6,
         estimate=0.456, derived_r=0.426),
    dict(id='expanded_condition', question='interaction_condition', metric='hedges_g',
         k=36, estimate=0.691),
    dict(id='expanded_outcome', question='external_outcome_association', metric='fishers_z',
         k=30, estimate=0.474, derived_r=0.441),
    dict(id='restricted_outcome', question='external_outcome_association', metric='fishers_z',
         k=26, estimate=0.418, derived_r=0.395),
)


def audit_code_roots(records=CODE_REFERENCES):
    records = tuple(records)
    role = {r['id']: r for r in records}
    if len(records) != 4 or len(role) != 4:
        raise ValueError('lost or duplicated original Rai paper code role')
    canonical = {r['id']: (r['url'], r['scope'], r['citing_root']) for r in CODE_REFERENCES}
    if set(role) != set(canonical) or any(
        (v['url'], v['scope'], v['citing_root']) != canonical[k] for k, v in role.items()
    ):
        raise ValueError('distinct original source code locator roles conflated')
    return dict(original_paper_doi=RAI_DOI, source_locators=len(role),
                source_citation_roles=sorted(role),
                original_OSF_files_or_versions_fetched=False,
                code_identical_across_locators_verified=False,
                correlated_components_not_canonical_correlation=True,
                original_2025_CCA_or_Granger_reproduced=False)


def audit_review_models(models=MODELS, unique_studies=54):
    models = tuple(models)
    identities = [m['id'] for m in models]
    if unique_studies != 54 or len(models) != 5 or len(set(identities)) != 5:
        raise ValueError('2026 review source study/model identities changed')
    canonical = {m['id']: m for m in MODELS}
    if set(identities) != set(canonical):
        raise ValueError('2026 review models missing')
    for m in models:
        source = canonical[m['id']]
        if m != source or type(m['k']) is not int or not 0 < m['k'] <= unique_studies:
            raise ValueError('2026 review original effect-unit, source-count or metric changed')
        if (m['metric'] == 'hedges_g') != (m['question'] == 'interaction_condition'):
            raise ValueError('heterogeneous effect-size types conflated')
        if 'derived_r' in m and abs(tanh(m['estimate']) - m['derived_r']) > 0.003:
            raise ValueError('Fisher z / derived r inconsistent')
    core = canonical['core_condition']
    if not (core['ci'][0] < core['estimate'] < core['ci'][1]):
        raise ValueError('invalid published Hedges g interval')
    return dict(review_doi=REVIEW_DOI, original_review_authors='Lan Jiang; Qingyu Zou; Shuilong Yu',
                source_unique_studies=unique_studies, source_model_specific_counts={m['id']: m['k'] for m in models},
                effects_by_model={m['id']: (m['metric'], m['estimate']) for m in models},
                sum_of_model_k_is_independent_studies=False,
                review_new_experimental_participants=0,
                review_prospectively_registered=False,
                original_study_inclusion_list_inspected=False,
                overlap_with_Rai_original_study_verified=False,
                remote_target_mechanism_established=False)


def audit_source_program():
    return dict(rai=audit_code_roots(), review=audit_review_models(),
                forum=dict(doi=FORUM_DOI, authors='Giacomo Novembre; Atesh Koul; Felix Bigand',
                           publication_kind='Forum/methodological taxonomy',
                           new_independent_empirical_trial=False),
                no_psi_or_hardt_event_verified=True)


class TestOriginalSourceRoots(unittest.TestCase):
    def test_four_method_code_roles(self):
        self.assertEqual(audit_code_roots()['source_locators'], 4)
    def test_granger_not_cca(self):
        r=list(CODE_REFERENCES); r[-1] = dict(r[-1], scope=r[-2]['scope'])
        with self.assertRaisesRegex(ValueError, 'conflated'): audit_code_roots(r)
    def test_two_general_code_pages_not_automatically_identical(self):
        self.assertFalse(audit_code_roots()['code_identical_across_locators_verified'])
    def test_no_original_code_download_claim(self):
        self.assertFalse(audit_code_roots()['original_OSF_files_or_versions_fetched'])
    def test_review_unique_study_count(self):
        self.assertEqual(audit_review_models()['source_unique_studies'], 54)
    def test_core_condition_Hedges_g_and_interval(self):
        self.assertEqual(MODELS[0]['ci'], (0.533, 1.241))
        self.assertEqual(MODELS[0]['estimate'], 0.887)
    def test_core_outcome_Fisher_z_and_r(self):
        self.assertAlmostEqual(tanh(MODELS[1]['estimate']), MODELS[1]['derived_r'], delta=0.003)
    def test_cannot_add_meta_model_ks_as_independent_studies(self):
        self.assertFalse(audit_review_models()['sum_of_model_k_is_independent_studies'])
    def test_changed_k_rejected(self):
        import copy
        ms=copy.deepcopy(MODELS); ms[0]['k']=55
        with self.assertRaisesRegex(ValueError,'metric changed'): audit_review_models(ms)
    def test_wrong_effect_scale_rejected(self):
        import copy
        ms=copy.deepcopy(MODELS); ms[0]['metric']='fishers_z'
        with self.assertRaisesRegex(ValueError,'metric changed'):audit_review_models(ms)
    def test_no_empirical_Hardt_claim_added(self):
        self.assertFalse(audit_review_models()['remote_target_mechanism_established'])
    def test_forum_is_not_second_trial(self):
        self.assertFalse(audit_source_program()['forum']['new_independent_empirical_trial'])


def main():
    p=argparse.ArgumentParser(); p.add_argument('--selftest', action='store_true'); args=p.parse_args()
    if args.selftest:
        t=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TestOriginalSourceRoots))
        raise SystemExit(0 if t.wasSuccessful() else 1)
    print(json.dumps(audit_source_program(), indent=2, sort_keys=True))


if __name__ == '__main__':main()

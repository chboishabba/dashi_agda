#!/usr/bin/env python3
"""Source-bound VMF biology contrast (not a biomedical replication).

Original papers: Saikia et al. (2019), Maldonado-Moreles et al. (2021),
Aparicio-Bautista et al. (2022), Ramirez-Galindo et al. (2024).
Original study credit stays with those authors. Johl Brown-directed source
audit with OpenAI ChatGPT assistance.
"""
from __future__ import annotations
import json
import unittest

SOURCE = {
 'a_beta_2021': dict(doi='10.1080/15368378.2020.1830288', year=2021,
  first_author='Alejandro Maldonado-Moreles', kind='original_experiment',
  measured='Aβ fibril formation and SH-SY5Y cell responses',
  exposure='vortex magnetic field, own coil',
  phenotype='fibril formation approx 86% lower than own untreated control after 24 h; authors report increased viability',
  context='Aβ-associated peptide and cell assays', direction='fibrils_down_and_viability_up'),
 'cell_2022': dict(doi='10.1002/bem.22400', year=2022,
  first_author='Diana I. Aparicio-Bautista', kind='original_experiment',
  measured='SH-SY5Y cell proteome and survival',
  exposure='own modified Rodin-coil extremely low-frequency vortex field',
  phenotype='decreased cell survival with apoptosis; 106 altered protein spots (40 down, 66 up)',
  context='cell-line exposure/proteomics under its own conditions', direction='cell_survival_down'),
 'ef_2019': dict(doi='10.1021/acschemneuro.8b00490', year=2019,
  first_author='Jahnu Saikia', kind='original_experiment',
  measured='Aβ peptide aggregation and cellular toxicity',
  exposure='electric- and magnetic-field investigation, geometry unverified here',
  phenotype='authors report 15–38% less toxicity for EF-treated samples in specified cells',
  context='different Aβ preparations and EF assays', direction='toxicity_down_in_ef'),
 'rodin_2024': dict(doi='10.31349/RevMexFis.70.030901', year=2024,
  first_author='Ángel David Ramírez-Galindo', kind='original_field_characterization',
  measured='Rodin coil magnetic field mapping, modelling, geometry',
  exposure='own Rodin setup',
  phenotype='discussion asserts up-to-60% biological comparison against Helmholtz, citing Saikia 2019 as [24]',
  context='field-characterization paper, not authenticated same-cell Rodin/Helmholtz comparison in this audit',
  direction='biological_comparison_not_reproduced_here'),
}
CITATION = dict(citing='rodin_2024', citing_reference='24', cited='ef_2019',
  exact_claim='up_to_60_percent_Rodin_vs_Helmholtz',
  original_2019_full_methods_and_SI_inspected=False,
  matching_rodin_helmholtz_arms_authenticated=False)
REQUIRED_FOR_SAME_EXPERIMENT = frozenset((
 'original_sample_lot','assay_endpoint_and_denominator','exact_coil_specimen',
 'field_spectrum_and_gradient','exposure_duration','sham_and_controls',
 'actual_raw_trials'))

def source_audit(records=SOURCE, citation=CITATION):
    if set(records) != set(SOURCE) or citation != CITATION:
        raise ValueError('original source roots or direct citation identity changed')
    for key, original in SOURCE.items():
        if records[key] != original or not original['doi'] or not original['first_author']:
            raise ValueError('source provenance or effect scope was rewritten')
    return dict(original_experiment_roots=3, separate_original_field_characterization=1,
      unique_original_biological_studies=3,
      shared_named_team_members_2021_2022=('Teodoro Córdova-Fraga','Gustavo Basurto-Islas'),
      independent_same_protocol_replication_verified=False,
      original_2021_benefit_general_safety_verified=False,
      original_2022_harm_all_exposures_verified=False,
      cited_2019_study_is_2021_vmf_experiment=False,
      original_2024_reference_24_validates_60_percent_comparison=False,
      unknown_exposure_parameters_must_not_be_filled_from_2024_model=True)

def same_experiment_join(left, right, evidence=None):
    if left not in SOURCE or right not in SOURCE:
        raise ValueError('unattributed study identity')
    evidence = evidence or {}
    if any(not isinstance(k,str) or not isinstance(v,str) or not v.strip()
           for k,v in evidence.items()):
        raise ValueError('blank or malformed supplied evidence')
    # Even full *claimed* field names do not authenticate publisher-source bytes.
    return dict(left=left,right=right,
       supplied_same_object_fields=sorted(REQUIRED_FOR_SAME_EXPERIMENT.intersection(evidence)),
       required_field_names=sorted(REQUIRED_FOR_SAME_EXPERIMENT),
       coverage_complete=REQUIRED_FOR_SAME_EXPERIMENT.issubset(evidence),
       authenticated_original_source_bytes=False, same_experiment_verified=False,
       effect_size_pooling_permitted=False)

def audit():
    return dict(source_scope=source_audit(),
      original_source_identifiers={k:r['doi'] for k,r in SOURCE.items()},
      claimed_2024_citation=dict(CITATION),
      compare_2021_2022=same_experiment_join('a_beta_2021','cell_2022'),
      compare_2019_2024=same_experiment_join('ef_2019','rodin_2024'),
      no_replay_of_original_trials=True,no_verified_biomedical_therapy=True,
      no_kernel_proof=True)

class TestVMFOriginalEndpointScope(unittest.TestCase):
    def test_four_original_paper_ids(self): self.assertEqual(len(SOURCE),4)
    def test_original_2021_claim_is_conditioned(self):
        self.assertIn('24 h',SOURCE['a_beta_2021']['phenotype'])
        self.assertIn('own untreated control',SOURCE['a_beta_2021']['phenotype'])
    def test_original_2022_survival_contrast(self):
        self.assertEqual(SOURCE['cell_2022']['direction'],'cell_survival_down')
    def test_original_2022_proteome_arithmetic(self): self.assertEqual(40+66,106)
    def test_2021_2022_not_same_experiment(self):
        self.assertFalse(same_experiment_join('a_beta_2021','cell_2022')['same_experiment_verified'])
    def test_2019_is_electric_field_root(self):
        self.assertIn('EF-treated',SOURCE['ef_2019']['phenotype'])
    def test_2024_cites_2019_not_2021(self):
        self.assertEqual(CITATION['cited'],'ef_2019')
        self.assertEqual(CITATION['citing_reference'],'24')
    def test_60_percent_is_not_authenticated(self):
        self.assertFalse(source_audit()['original_2024_reference_24_validates_60_percent_comparison'])
    def test_complete_fields_still_insufficient(self):
        evidence={k:'asserted' for k in REQUIRED_FOR_SAME_EXPERIMENT}
        result=same_experiment_join('a_beta_2021','cell_2022',evidence)
        self.assertTrue(result['coverage_complete'])
        self.assertFalse(result['same_experiment_verified'])
    def test_reject_source_mutation(self):
        records={k:dict(v) for k,v in SOURCE.items()}
        records['cell_2022']['direction']='cell_survival_up'
        with self.assertRaises(ValueError):source_audit(records)
    def test_reject_unknown_source(self):
        with self.assertRaises(ValueError):same_experiment_join('other','cell_2022')
    def test_not_clinical_research(self):
        self.assertTrue(audit()['no_verified_biomedical_therapy'])

if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--self-test',action='store_true')
    args=p.parse_args()
    if args.self_test:
        result=unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(TestVMFOriginalEndpointScope))
        raise SystemExit(0 if result.wasSuccessful() else 1)
    print(json.dumps(audit(),indent=2,sort_keys=True,ensure_ascii=False))

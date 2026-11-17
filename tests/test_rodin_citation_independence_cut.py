"""Documentary negative-promotion tests, not original field experiments."""
from __future__ import annotations
import csv
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
S = ROOT / 'scripts' / 'check_rodin_citation_independence_cut.py'
spec = importlib.util.spec_from_file_location('rodin_documentary_cut', S)
assert spec and spec.loader
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
FIELDS = ['current_a', 'perez_2013_frequency_hz', 'perez_2013_theory_mt',
          'perez_2013_experiment_mt', 'ramirez_galindo_2024_theory_mt',
          'ramirez_galindo_2024_simulation_mt', 'ramirez_galindo_2024_experiment_mt',
          'reused_raw_trace_proved']
ROWS = [
 {'current_a':'1.60','perez_2013_frequency_hz':'100','perez_2013_theory_mt':'3.80', 'perez_2013_experiment_mt':'4.13','ramirez_galindo_2024_theory_mt':'3.90','ramirez_galindo_2024_simulation_mt':'4.08','ramirez_galindo_2024_experiment_mt':'4.13','reused_raw_trace_proved':'false'},
 {'current_a':'1.25','perez_2013_frequency_hz':'800','perez_2013_theory_mt':'2.97', 'perez_2013_experiment_mt':'3.05','ramirez_galindo_2024_theory_mt':'3.01','ramirez_galindo_2024_simulation_mt':'3.00','ramirez_galindo_2024_experiment_mt':'3.05','reused_raw_trace_proved':'false'},
 {'current_a':'0.60','perez_2013_frequency_hz':'2450','perez_2013_theory_mt':'1.42', 'perez_2013_experiment_mt':'1.16','ramirez_galindo_2024_theory_mt':'1.30','ramirez_galindo_2024_simulation_mt':'1.10','ramirez_galindo_2024_experiment_mt':'1.16','reused_raw_trace_proved':'false'},
]

class TestRodinDocumentaryCut(unittest.TestCase):
    def fixture(self, fn=None):
        from copy import deepcopy
        data = deepcopy(ROWS)
        if fn:
            fn(data)
        t = tempfile.TemporaryDirectory()
        self.addCleanup(t.cleanup)
        file = Path(t.name)/'printed.csv'
        with file.open('w', newline='', encoding='utf-8') as h:
            writer=csv.DictWriter(h,fieldnames=FIELDS)
            writer.writeheader(); writer.writerows(data)
        return file

    def test_published_concordance_not_raw_identity(self):
        result=module.audit(self.fixture())
        self.assertEqual(result['same_reported_current_field_pairs'],3)
        self.assertEqual(result['2013_2024_raw_session_identity'],'UNRESOLVED')

    def test_transcription_change_rejected(self):
        with self.assertRaisesRegex(ValueError,'concordance'):
            module.audit(self.fixture(lambda rows: rows[0].update(ramirez_galindo_2024_experiment_mt='4.12')))

    def test_frequency_context_rejected(self):
        with self.assertRaisesRegex(ValueError,'concordance'):
            module.audit(self.fixture(lambda rows: rows[1].update(perez_2013_frequency_hz='0')))

    def test_raw_data_promotion_rejected(self):
        with self.assertRaisesRegex(ValueError,'raw traces'):
            module.audit(self.fixture(lambda rows: rows[2].update(reused_raw_trace_proved='true')))

    def test_2013_2024_theory_identity_rejected(self):
        with self.assertRaisesRegex(ValueError,'theoretical'):
            module.audit(self.fixture(lambda rows: rows[0].update(ramirez_galindo_2024_theory_mt='3.80')))

    def test_bibliography_explicit_source_distinctions(self):
        refs={i: f'unknown original bibliography item {i}' for i in range(1,25)}
        refs[13]='Maldonado-Moreles et al. 2021'
        refs[14]='Rodin & Volk 2010'
        refs[23]='Aparicio-Bautista et al. 2022'
        self.assertTrue(module.audit(self.fixture(),refs)['source_2024_reference_list_checked_from_input'])
        refs[8]='Perez et al 2013 DOI 10.1063/1.4819796'
        with self.assertRaisesRegex(ValueError,'noncitation'):
            module.audit(self.fixture(),refs)

    def test_partial_bibliography_cannot_prove_absence(self):
        with self.assertRaisesRegex(ValueError,'24 numbered'):
            module.audit(self.fixture(),{14:'Rodin & Volk 2010'})


    def test_two_latent_worlds_same_printed_table(self):
        w = module.rounded_measurement_worlds(self.fixture())
        self.assertTrue(w['hypothetical_counterexample_only'])
        self.assertEqual(w['raw_field_trace_identity_status'], 'UNRESOLVED')
        self.assertEqual(len(w['rows']), 3)
        self.assertTrue(w['2013_frequency_not_transferable_to_2024'])
        from decimal import Decimal, ROUND_HALF_UP
        for row in w['rows']:
            a = [Decimal(x) for x in row['shared_trace_hypothesis_unrounded_pair_mt']]
            b = [Decimal(x) for x in row['distinct_trace_hypothesis_unrounded_pair_mt']]
            printed = Decimal(row['printed_both_mt'])
            self.assertEqual(a[0], a[1])
            self.assertNotEqual(b[0], b[1])
            self.assertEqual(
                {x.quantize(Decimal('0.01'), rounding=ROUND_HALF_UP) for x in a+b},
                {printed})

    def test_rounded_witness_rejects_cross_current_join(self):
        with self.assertRaisesRegex(ValueError, 'misjoined'):
            module.rounded_measurement_worlds(self.fixture(
                lambda rows: rows[0].update(current_a='1.25')))

    def test_rounded_witness_rejects_tampered_reported_field(self):
        with self.assertRaisesRegex(ValueError, 'concordance'):
            module.rounded_measurement_worlds(self.fixture(
                lambda rows: rows[2].update(ramirez_galindo_2024_experiment_mt='1.17')))

    def test_rounded_witness_no_false_frequency_inference(self):
        w = module.rounded_measurement_worlds(self.fixture())
        self.assertEqual(w['original_2024_table_frequency'], 'NOT_REPORTED_IN_TABLE_II')
        self.assertTrue(w['original_2024_FEM_steady_state_not_measured_sensor_drive_frequency'])
        self.assertTrue(w['no_p_value_without_noise_calibration_and_protocol'])
        self.assertFalse(w['author_measurement_sessions_verified'])
        self.assertTrue(w['no_misconduct_inference'])


if __name__=='__main__':unittest.main()

#!/usr/bin/env python3
"""Source-neutral 2x2 physical-field interaction audit; NOT exposure advice.

Synthetic inputs only unless externally authenticated. Independent units and a
single pre-specified outcome are assumed; causal/human-health conclusions require
separate ethical, calibration, dose, thermal, blinding and randomisation review.
"""
import csv
import json
import math
import sys
import unittest
from collections import defaultdict
from dataclasses import dataclass

ARMS = ((0, 0), (1, 0), (0, 1), (1, 1))

@dataclass(frozen=True)
class Observation:
    unit_id: str
    sound_on: int
    rf_on: int
    outcome: float
    study_id: str
    protocol_ref: str
    calibration_ref: str


def estimate(records):
    """Descriptive interaction. One observation per independently sampled unit."""
    records = list(records)
    groups = defaultdict(list)
    seen = set()
    study_keys = set()
    for r in records:
        if r.sound_on not in (0, 1) or r.rf_on not in (0, 1):
            raise ValueError('invalid four-arm assignment')
        if not r.unit_id or r.unit_id in seen:
            raise ValueError('missing or duplicate independent unit identity')
        if not math.isfinite(r.outcome):
            raise ValueError('non-finite outcome')
        seen.add(r.unit_id)
        if not all((r.study_id, r.protocol_ref, r.calibration_ref)):
            raise ValueError('missing source/protocol/calibration *locator*')
        study_keys.add((r.study_id, r.protocol_ref, r.calibration_ref))
        groups[(r.sound_on, r.rf_on)].append(r.outcome)
    if len(study_keys) != 1:
        raise ValueError('cannot silently join separate studies or instrument protocols')
    if any(len(groups[k]) < 2 for k in ARMS):
        raise ValueError('at least two independent observations per factorial arm required')
    mean = {k: sum(groups[k])/len(groups[k]) for k in ARMS}
    variance = {k: sum((v-mean[k])**2 for v in groups[k])/(len(groups[k])-1)
                for k in ARMS}
    effect = mean[(1, 1)]-mean[(1, 0)]-mean[(0, 1)]+mean[(0, 0)]
    # Only a descriptive independent-group standard error; no causal p value.
    se = math.sqrt(sum(variance[k]/len(groups[k]) for k in ARMS))
    return {
        'n_per_arm': {f'{a}{b}': len(groups[(a, b)]) for a, b in ARMS},
        'mean_per_arm': {f'{a}{b}': mean[(a, b)] for a, b in ARMS},
        'sound_effect_when_rf_off': mean[(1, 0)]-mean[(0, 0)],
        'rf_effect_when_sound_off': mean[(0, 1)]-mean[(0, 0)],
        'factorial_interaction_contrast': effect,
        'interaction_independent_group_standard_error': se,
        'calibrated_physical_coupling_demonstrated': False,
        'causal_biological_effect_demonstrated': False,
        'intent_or_deployment_demonstrated': False,
        'required_external_receipts': [
            'genuine calibrated sound spectrum and level at receptor, incl. audible and vibration',
            'genuine RF waveform, field strength, exposure dosimetry, and thermal tracking',
            'original random assignment, complete outcome/attrition and sham/blinding records',
            'pre-registered endpoint, independence, sample-size justification and uncertainty analysis',
            'independent replication and intervention appropriateness/ethics if living subjects',
            'same-apparatus historical/operational records for any deliberate-influence allegation'
        ]
    }


def read_rows(path):
    fields = tuple(Observation.__dataclass_fields__)
    with open(path, newline='', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        if not set(fields).issubset(set(reader.fieldnames or [])):
            raise ValueError('CSV missing columns')
        return [Observation(**{**{s: row[s] for s in ('unit_id','study_id','protocol_ref','calibration_ref')},
                **{b: int(row[b]) for b in ('sound_on','rf_on')},
                'outcome': float(row['outcome'])}) for row in reader]


def synthetic(interaction=0):
    baseline = {(0,0):10,(1,0):12,(0,1):13,(1,1):15+interaction}
    return [Observation(f'unit-{a}{b}-{i}',a,b,baseline[(a,b)]+d,
                        'synthetic','fixture-only','not-calibrated')
            for a,b in ARMS for i,d in enumerate((-1,1))]


class TestFactorial(unittest.TestCase):
    def test_additive(self):
        z=estimate(synthetic())
        self.assertAlmostEqual(z['factorial_interaction_contrast'],0)
        self.assertFalse(z['causal_biological_effect_demonstrated'])
    def test_nonadditive(self):
        self.assertAlmostEqual(estimate(synthetic(4))['factorial_interaction_contrast'],4)
    def test_duplicate_rejected(self):
        x=synthetic(); x[1]=x[0]
        with self.assertRaises(ValueError):estimate(x)
    def test_partial_arm_rejected(self):
        with self.assertRaises(ValueError):estimate(synthetic()[:-1])
    def test_wrong_protocol_rejected(self):
        x=synthetic(); x[1]=Observation('u',0,0,9,'other','fixture-only','not-calibrated')
        with self.assertRaises(ValueError):estimate(x)
    def test_nan_rejected(self):
        x=synthetic(); x[0]=Observation('unit-00-0',0,0,float('nan'),'synthetic','fixture-only','not-calibrated')
        with self.assertRaises(ValueError):estimate(x)

if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        r=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TestFactorial))
        raise SystemExit(0 if r.wasSuccessful() else 1)
    if sys.argv[1:] == ['--synthetic']:
        print(json.dumps(estimate(synthetic(4)), indent=2))
    elif len(sys.argv)==3 and sys.argv[1]=='--csv':
        print(json.dumps(estimate(read_rows(sys.argv[2])), indent=2))
    else:
        raise SystemExit('Use --selftest, --synthetic or --csv FILE. No real exposure is performed.')

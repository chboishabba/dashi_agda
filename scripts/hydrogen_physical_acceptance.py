#!/usr/bin/env python3
"""Matched-output hydrogen retrofit analysis; no vendor-performance assumptions.

User-directed, ChatGPT-authored integration, 2026-11-09. Existing DASHI
SI/conservation authors and original chemistry/thermochemistry sources retain
attribution. This program cannot certify instrument provenance or causality.

Usage: python hydrogen_physical_acceptance.py measured.csv
       python hydrogen_physical_acceptance.py --self-test

All energy fields are kWh over the same block and HHV/declared convention.
The user must record source/calibration IDs; synthetic examples are rejected.
"""
from __future__ import annotations
import csv
import json
import sys
import unittest
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation

ARMS = ('powered_no_gas', 'h2_only', 'o2_only', 'h2_o2', 'baseline')
ENERGY = ('diesel', 'external_electric', 'imported_heat', 'aux_fuel',
          'external_h2', 'external_synth', 'stored_before', 'stored_after')
REQUIRED = ('block', 'arm', 'source_id', 'calibration_id', 'output_kwh',
            'shaft_work_kwh', 'h2_burned_kwh', 'synth_burned_kwh',
            'hhv_basis', 'duty_id', 'emissions_receipt')

def dec(x: str) -> Decimal:
    try:
        value = Decimal(str(x))
    except (InvalidOperation, ValueError) as exc:
        raise ValueError(f'invalid numeric value {x!r}') from exc
    if not value.is_finite() or value < 0:
        raise ValueError(f'nonfinite/negative measured quantity {x!r}')
    return value

@dataclass(frozen=True)
class Run:
    data: dict

    def q(self, name: str) -> Decimal:
        return dec(self.data[name + '_kwh'])

    def u(self, name: str) -> Decimal:
        return dec(self.data[name + '_unc_kwh'])

    def input_bounds(self):
        inputs = ENERGY[:6] + ('stored_before',)
        mid = sum((self.q(n) for n in inputs), Decimal(0)) - self.q('stored_after')
        unc = sum((self.u(n) for n in ENERGY), Decimal(0))
        return mid - unc, mid + unc

    def engine_eta(self):
        combustible = self.q('diesel') + self.q('h2_burned') + self.q('synth_burned')
        if combustible <= 0:
            raise ValueError('engine chemical input must be positive')
        return self.q('shaft_work') / combustible

    def validate(self):
        for key in REQUIRED:
            if not self.data.get(key):
                raise ValueError(f'missing required field {key}')
        for key in ENERGY + ('h2_burned', 'synth_burned', 'shaft_work', 'output'):
            self.q(key)
        for key in ENERGY:
            self.u(key)
        if self.data['arm'] not in ARMS:
            raise ValueError('unknown arm')
        if self.q('external_h2') > self.q('h2_burned'):
            raise ValueError('external H2 exceeds H2 burned')
        if self.q('external_synth') > self.q('synth_burned'):
            raise ValueError('external synthetic fuel exceeds synthetic fuel burned')
        if self.data['hhv_basis'] != 'HHV':
            raise ValueError('mixed/unsupported heat basis; convert explicitly')
        if any('SYNTHETIC' in self.data[k].upper() for k in ('source_id','calibration_id')):
            raise ValueError('synthetic provenance cannot be admitted as measured')
        if self.q('shaft_work') < self.q('output'):
            raise ValueError('net output exceeds source-reported shaft work')

def analyze(records: list[dict], output_tolerance=Decimal('0.005')):
    runs = [Run(record) for record in records]
    for run in runs:
        run.validate()
    blocks = {}
    for run in runs:
        key = run.data['block']
        if run.data['arm'] in blocks.setdefault(key, {}):
            raise ValueError(f'duplicate arm in block {key}')
        blocks[key][run.data['arm']] = run
    results = []
    for block, arm in blocks.items():
        if set(arm) != set(ARMS):
            raise ValueError(f'block {block} lacks complete five-arm controls')
        if len({r.data['duty_id'] for r in arm.values()}) != 1:
            raise ValueError('different duty cycles cannot be pooled')
        if len({r.data['hhv_basis'] for r in arm.values()}) != 1:
            raise ValueError('mixed calorimetric conventions')
        baseline = arm['baseline']
        baseline_out = baseline.q('output')
        if baseline_out <= 0:
            raise ValueError('zero baseline useful output')
        if any(abs(r.q('output') - baseline_out) > output_tolerance
               for r in arm.values()):
            raise ValueError('outputs not actually matched')
        without = arm['powered_no_gas']
        h, o, both = arm['h2_only'], arm['o2_only'], arm['h2_o2']
        interaction = h.q('diesel') + o.q('diesel') - without.q('diesel') - both.q('diesel')
        base_lower, base_upper = baseline.input_bounds()
        assisted_lower, assisted_upper = both.input_bounds()
        robust_saving = assisted_upper < base_lower
        mechanism = {
            key: str(r.engine_eta()) for key, r in arm.items()
        }
        results.append({
            'block': block,
            'diesel_displacement_kwh': str(baseline.q('diesel') - both.q('diesel')),
            'hydrogen_oxygen_interaction_kwh': str(interaction),
            'engine_shaft_efficiency_by_arm': mechanism,
            'net_energy_saving_interval_kwh':
                [str(base_lower - assisted_upper), str(base_upper - assisted_lower)],
            'robust_positive_net_input_saving': robust_saving,
            'causal_combustion_mechanism_proven': False,
            'independent_replication_proven': False,
            'note': 'Meter/source fields are identifiers; documentary verification and replication are external.',
        })
    return results

class Tests(unittest.TestCase):
    def row(self, arm, diesel, h2=0, output=35, extra=0):
        data = dict(block='A', arm=arm, source_id='lab-raw-asset',
                    calibration_id='cal-001', hhv_basis='HHV', duty_id='fixed-load',
                    emissions_receipt='emissions-asset', output_kwh=str(output),
                    shaft_work_kwh='35')
        values = {name: 0 for name in ENERGY}
        values.update(diesel=diesel, external_electric=extra)
        for name, value in values.items():
            data[name+'_kwh'] = str(value)
            data[name+'_unc_kwh'] = '0.1'
        data['h2_burned_kwh'] = str(h2)
        data['synth_burned_kwh'] = '0'
        return data
    def full(self):
        return [self.row('baseline',100), self.row('powered_no_gas',100),
                self.row('h2_only',92,h2=5,extra=7),
                self.row('o2_only',94,extra=2),
                self.row('h2_o2',80,h2=8,extra=12)]
    def test_full_block_interaction(self):
        r=analyze(self.full())[0]
        self.assertEqual(r['hydrogen_oxygen_interaction_kwh'],'6')
        self.assertTrue(r['robust_positive_net_input_saving'])
        self.assertFalse(r['causal_combustion_mechanism_proven'])
    def test_unmatched_output_rejected(self):
        rows=self.full(); rows[2]['output_kwh']='34'
        with self.assertRaisesRegex(ValueError,'outputs not actually matched'):
            analyze(rows)
    def test_missing_control_rejected(self):
        with self.assertRaisesRegex(ValueError,'complete five-arm'):
            analyze(self.full()[:-1])
    def test_synthetic_provenance_rejected(self):
        rows=self.full(); rows[1]['source_id']='SYNTHETIC'
        with self.assertRaisesRegex(ValueError,'synthetic provenance'):
            analyze(rows)
    def test_diluted_savings_not_robust(self):
        rows=self.full(); rows[-1]['external_electric_kwh']='25'
        self.assertFalse(analyze(rows)[0]['robust_positive_net_input_saving'])
    def test_external_h2_not_double_counted(self):
        rows=self.full(); rows[-1]['external_h2_kwh']='8'
        self.assertFalse(analyze(rows)[0]['robust_positive_net_input_saving'])
    def test_bad_external_hydrogen_rejected(self):
        rows=self.full(); rows[-1]['external_h2_kwh']='15'
        with self.assertRaisesRegex(ValueError,'external H2 exceeds'):
            analyze(rows)
    def test_negative_uncertainty_rejected(self):
        rows=self.full(); rows[-1]['diesel_unc_kwh']='-1'
        with self.assertRaisesRegex(ValueError,'negative'):
            analyze(rows)

if __name__=='__main__':
    if '--self-test' in sys.argv:
        unittest.main(argv=[sys.argv[0]],verbosity=2)
    elif len(sys.argv)==2:
        with open(sys.argv[1],newline='') as stream:
            print(json.dumps(analyze(list(csv.DictReader(stream))),indent=2))
    else:
        raise SystemExit('usage: python hydrogen_physical_acceptance.py measured.csv | --self-test')

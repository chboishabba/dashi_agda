#!/usr/bin/env python3
"""Exact interval first-law audit, without declaring a natural source.

Consumes a signed V/I receipt plus *independently* supplied loss and storage
change intervals. A compatible budget is necessary, never proof of origin,
replenishment, or repeatability. No simulated observations are built in.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path


def rat(x):
    if not isinstance(x, str) or not x.strip():
        raise ValueError('energy endpoints must be exact rational strings')
    return Fraction(x)


def interval(data):
    if not isinstance(data, dict) or set(data) != {'lower_J', 'upper_J'}:
        raise ValueError('interval must have lower_J and upper_J')
    a, b = rat(data['lower_J']), rat(data['upper_J'])
    if a > b:
        raise ValueError('reversed interval')
    return a, b


def out(pair):
    return {'lower_J': str(pair[0]), 'upper_J': str(pair[1])}


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def analyze(work, independent):
    if not isinstance(work, dict) or not isinstance(independent, dict):
        raise ValueError('both receipts must be objects')
    if work.get('original_id') != independent.get('original_id') or not isinstance(work.get('original_id'), str):
        raise ValueError('original apparatus IDs differ')
    if work.get('clock_id') != independent.get('clock_id') or not isinstance(work.get('clock_id'), str):
        raise ValueError('clock IDs differ')
    if work.get('integration_remainder_certificate_required') is not True:
        raise ValueError('work receipt lacks explicit integration remainder admission')
    natural = interval(work['net_environmental_work'])
    controller = interval(work['net_controller_work'])
    load = interval(work['useful_load_work'])
    loss = interval(independent['all_dissipative_and_outgoing_loss_J'])
    storage = interval(independent['total_stored_energy_final_minus_initial_J'])
    if loss[0] < 0:
        raise ValueError('loss interval may not certify negative dissipative loss')
    residual = sub(sub(add(natural, controller), load), add(loss, storage))
    # Both bounds are exact and conservatively allow correlations; they are
    # not calibrated until the independently generated input intervals are.
    restorable = storage == (Fraction(0), Fraction(0))
    return {
        'original_id': work['original_id'], 'clock_id': work['clock_id'],
        'natural_net_J': out(natural), 'controller_net_J': out(controller),
        'load_J': out(load), 'all_loss_J': out(loss),
        'storage_change_J': out(storage), 'first_law_residual_J': out(residual),
        'zero_in_first_law_residual': residual[0] <= 0 <= residual[1],
        'first_law_excluded_by_claimed_intervals': residual[0] > 0 or residual[1] < 0,
        'exact_restoration_admitted_by_interval': restorable,
        'conditionally_positive_natural_work': natural[0] > 0,
        'environmental_sink_proved_conditional_on_inputs': natural[1] < 0,
        'f15_closed': False, 'physical_claim_closed': False,
        'notes': [
            'A labelled natural port is not an independent natural-source certificate.',
            'Zero residual compatibility is necessary, not evidence for F15.',
            'Storage change includes electrical, mechanical, thermal, chemical and material states only if independently measured.',
            'Exact restoration requires a true [0,0] interval, not an unobserved endpoint.',
            'A zero-compatible interval without controlled repeated cycles does not establish sustained replenishment.',
        ]
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('work_receipt', type=Path)
    p.add_argument('independent_loss_storage_receipt', type=Path)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    try:
        result = analyze(json.loads(args.work_receipt.read_text()),
                         json.loads(args.independent_loss_storage_receipt.read_text()))
    except (OSError, ValueError, KeyError, TypeError, ZeroDivisionError) as e:
        print(json.dumps({'error': str(e), 'f15_closed': False}))
        return 2
    render = json.dumps(result, sort_keys=True, indent=2)
    if args.out:
        args.out.write_text(render + '\n')
    print(render)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

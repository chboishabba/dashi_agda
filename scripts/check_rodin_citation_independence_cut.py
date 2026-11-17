#!/usr/bin/env python3
"""Case-specific 2013/2024 published Rodin table/citation audit.

This is bibliographic and arithmetic validation, NOT a magnetometer replay,
proof of data reuse or accusation of author misconduct. Original authors
retain their original measurements and interpretations.
"""
from __future__ import annotations
import argparse
import csv
import json
from decimal import Decimal, InvalidOperation
from pathlib import Path

DEFAULT = Path(__file__).resolve().parents[1] / 'docs' / 'research' / 'psychotronics-phase1-rodin-field-table-concordance-20261025.csv'
EXPECTED = (('1.60', '100', '4.13'), ('1.25', '800', '3.05'), ('0.60', '2450', '1.16'))
CITED_ORIGINALS = {
    14: ('Rodin & Volk', '2010'),
    13: ('Maldonado-Moreles et al.', '2021'),
    23: ('Aparicio-Bautista et al.', '2022'),
}
TARGET_2013_DOI = '10.1063/1.4819796'


def audit(path: Path = DEFAULT, original_2024_bibliography: dict | None = None) -> dict:
    """Verify only source-recorded printed values and bounded reference claims."""
    with path.open(newline='', encoding='utf-8') as handle:
        rows = list(csv.DictReader(handle))
    if len(rows) != len(EXPECTED):
        raise ValueError('expected exactly three original printed value rows')
    for row, (current, freq, observed) in zip(rows, EXPECTED):
        if not {'current_a', 'perez_2013_frequency_hz', 'perez_2013_experiment_mt',
                'ramirez_galindo_2024_experiment_mt', 'perez_2013_theory_mt',
                'ramirez_galindo_2024_theory_mt', 'ramirez_galindo_2024_simulation_mt',
                'reused_raw_trace_proved'}.issubset(row):
            raise ValueError('missing original bibliographic measurement field')
        try:
            actual = tuple(Decimal(row[k]) for k in
                ('current_a','perez_2013_frequency_hz','perez_2013_experiment_mt','ramirez_galindo_2024_experiment_mt'))
        except (InvalidOperation, ValueError) as exc:
            raise ValueError('invalid printed physical units/value') from exc
        if actual != (Decimal(current), Decimal(freq), Decimal(observed), Decimal(observed)):
            raise ValueError('2013/2024 printed field-value concordance differs')
        if row['reused_raw_trace_proved'].lower() != 'false':
            raise ValueError('rounded values do not identify raw traces')
        if Decimal(row['perez_2013_theory_mt']) == Decimal(row['ramirez_galindo_2024_theory_mt']):
            raise ValueError('distinct original theoretical columns were collapsed')
    # Original bibliography checked visually at the publisher's printed pp6-7.
    # It is optional as an INPUT to let callers provide an independently typed
    # canonical reference index, rather than falsely deriving bibliography from
    # the 3-row measurement CSV.
    refs = original_2024_bibliography
    if refs is not None:
        if set(refs) != set(range(1,25)):
            raise ValueError('2024 bibliography must include original 24 numbered items')
        if TARGET_2013_DOI in ' '.join(str(s).lower() for s in refs.values()):
            raise ValueError('contradicts inspected original 2024 bibliography noncitation')
        for number, (source, year) in CITED_ORIGINALS.items():
            if source.lower() not in str(refs[number]).lower() or year not in str(refs[number]):
                raise ValueError('lost original #13/#14/#23 bibliography distinction')
    return {
        'status': 'PUBLISHED_RECORDS_CONCORDANT_INDEPENDENCE_UNRESOLVED',
        'original_2024_reference_count_visually_inspected': 24,
        'explicit_2013_RSI_DOI_in_2024_references': False,
        '2013_RSI_DOI_original': TARGET_2013_DOI,
        'source_2024_reference_list_checked_from_input': refs is not None,
        'same_reported_current_field_pairs': len(rows),
        '2013_printed_frequencies_hz': [int(x[1]) for x in EXPECTED],
        '2024_theory_model_steady_state_as_printed': True,
        '2024_physical_sensor_acquisition_frequency_derived_from_steady_state_model': False,
        '2013_2024_raw_session_identity': 'UNRESOLVED',
        'misconduct_or_plagiarism_established': False,
        'novel_non_Maxwell_physics_observed': False,
    }



def rounded_measurement_worlds(path: Path = DEFAULT) -> dict:
    """Construct a finite exact counterexample to raw-session identifiability.

    Original paper values are printed to 0.01 mT. Nearest-decimal rounding is
    an explicit ILLUSTRATIVE model; the papers' underlying rounding/calibration
    procedures, uncertainty and raw records are not independently verified.

    World A shares the same latent trace. World B gives each paper separate
    hypothetical unrounded values from the same printed interval. Both map
    to exactly the original three printed pairs. Thus the TABLE cannot alone
    distinguish shared source from separate measurement sessions. World B
    does not assert authors actually remeasured, or statistical independence.
    """
    from decimal import ROUND_HALF_UP
    quantum = Decimal('0.01')
    shift = Decimal('0.001')
    with path.open(newline='', encoding='utf-8') as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != len(EXPECTED):
        raise ValueError('expected three published original-current rows')
    witnesses = []
    seen_current = set()
    for row, (current, freq, expected) in zip(rows, EXPECTED):
        if row.get('current_a') != current or row.get('perez_2013_frequency_hz') != freq:
            raise ValueError('misjoined current/frequency; cannot construct same-object comparison')
        if current in seen_current:
            raise ValueError('duplicate current labels')
        seen_current.add(current)
        printed = Decimal(expected)
        if Decimal(row['perez_2013_experiment_mt']) != printed or Decimal(
                row['ramirez_galindo_2024_experiment_mt']) != printed:
            raise ValueError('printed experimental fields are not the checked concordance')
        common = printed + shift
        distinct = printed - shift
        if common == distinct or any(
            v.quantize(quantum, rounding=ROUND_HALF_UP) != printed
            for v in (common, distinct)
        ):
            raise AssertionError('rounding collision failed')
        witnesses.append({
            'current_a': current,
            'printed_both_mt': str(printed),
            'shared_trace_hypothesis_unrounded_pair_mt': [str(common), str(common)],
            'distinct_trace_hypothesis_unrounded_pair_mt': [str(distinct), str(common)],
            'nearest_0_01_mt_rounding_yields_same_printed_pairs': True,
        })
    return {
        'hypothetical_counterexample_only': True,
        'author_measurement_sessions_verified': False,
        'raw_field_trace_identity_status': 'UNRESOLVED',
        'different_original_publications': True,
        'original_2024_table_frequency': 'NOT_REPORTED_IN_TABLE_II',
        '2013_frequency_not_transferable_to_2024': True,
        'original_2024_FEM_steady_state_not_measured_sensor_drive_frequency': True,
        'no_p_value_without_noise_calibration_and_protocol': True,
        'no_misconduct_inference': True,
        'rows': witnesses,
    }


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument('--csv', type=Path, default=DEFAULT)
    p.add_argument('--rounding-witness', action='store_true', help='include synthetic exact-coarsening nonidentifiability')
    args = p.parse_args()
    result = audit(args.csv)
    if args.rounding_witness:
        result['rounded_measurement_worlds'] = rounded_measurement_worlds(args.csv)
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""RVML/Gentry source-specific documentary admission, using existing Phase-1 graph.

This audits original-source *claims and graph classification*, not what the
speaker said in the video or the reality of any medical/gravity mechanism.
Uses (does not replace) the existing NOAA/Phase-1 generic ledger validator.
"""
from __future__ import annotations

import argparse
import csv
import json
from copy import deepcopy
from pathlib import Path
from check_psychotronics_ellsworth_1953_sources import audit_ledgers, SOURCES, EDGES


def _rows(path: Path, key: str) -> dict[str, dict[str, str]]:
    with path.open(newline='', encoding='utf-8') as f:
        result = list(csv.DictReader(f))
    if not result or any(key not in row or None in row for row in result):
        raise ValueError('malformed source-graph CSV')
    keys = [row[key] for row in result]
    if len(set(keys)) != len(keys):
        raise ValueError('duplicate documentary identity')
    return {row[key]: row for row in result}


def assert_gentry_bounds(sources: dict, edges: dict) -> dict:
    """Invariant on source ownership and the limit of the 1999 handoff."""
    if not {'P1-22', 'P1-23', 'P1-24', 'P1-69', 'P1-70'} <= set(sources):
        raise ValueError('missing original Croft/RVML/Flanagan evidence roles')
    if not {'E104', 'E105', 'E106', 'E107'} <= set(edges):
        raise ValueError('missing bounded organiser/video relation class')
    a, b = sources['P1-69'], sources['P1-70']
    if a['locator'] != 'https://rvml.org/calendar/wc112003s.htm':
        raise ValueError('event must resolve to original organiser, not a Croft reprint')
    if b['locator'] != 'https://vimeo.com/92437258':
        raise ValueError('later recording metadata must be separately located')
    if not ('Gentry Smith' in a['original_work'] and
            'Rogue Valley Metaphysical Library' in a['authorial_root'] and
            '2003' in a['date_or_period'] and '2003' in a['original_work']):
        raise ValueError('missing the original dated RVML Gentry programme')
    if not ('RVML' in b['authorial_root'] and 'Flanagan' in
            (b['claim_scope'] + b['explicit_join']) and
            'not' in b['not_established'].lower()):
        raise ValueError('recording metadata wrongly treated as witnessed speech')
    expected = {'E104': ('P1-69', 'P1-23'),
                'E105': ('P1-70', 'P1-69'),
                'E106': ('P1-70', 'P1-24'),
                'E107': ('P1-70', 'P1-22')}
    for edge, (src, dest) in expected.items():
        e = edges[edge]
        if e['source_id'] != src or e['target_id'] != dest:
            raise ValueError('misjoined original source dependence ' + edge)
        if not e['assertion_limit'].strip() or not e['root_witness'].strip():
            raise ValueError('unbounded original-source edge ' + edge)
    if 'same-original-organiser' not in edges['E105']['evidence_class']:
        raise ValueError('event and recording may not count as two witness roots')
    if 'not-handoff' not in edges['E104']['evidence_class']:
        raise ValueError('Gentry event cannot establish Croft 1999 transmission')
    if not ('no-personal-transmission-proof' in edges['E107']['evidence_class']):
        raise ValueError('RVML advertised topic cannot prove assistant relationship')
    return {
        'original_source_roles_checked': ['P1-69', 'P1-70'],
        'original_source_edges_checked': sorted(expected),
        'rvml_carriers': 2,
        'rvml_organiser_roots': 1,
        'croft_independent_from_rvml_as_publisher': True,
        'recording_playback_or_transcript_examined': False,
        'gentry_speaker_identity_authenticated_across_1999_and_2003': False,
        'flanagan_employment_independently_proved': False,
        'gentry_to_croft_1999_instruction_independently_proved': False,
        'medical_or_new_physics_outcome_verified': False,
        'status': 'DOCUMENTARY_TOPIC_CONVERGENCE_HANDOFF_UNRESOLVED',
    }


def self_test(sources: dict, edges: dict) -> dict:
    assert_gentry_bounds(sources, edges)
    n = 0
    for which, key, field, changed in (
        ('sources','P1-69','locator','https://www.croftzappers.com/the-don-croft-archives'),
        ('sources','P1-70','locator','https://vimeo.com/999999'),
        ('edges','E105','source_id','P1-23'),
        ('edges','E104','evidence_class','verified-handoff'),
        ('edges','E107','evidence_class','confirmed-personal-flanagan-assistant'),
    ):
        a, b = deepcopy(sources), deepcopy(edges)
        (a if which == 'sources' else b)[key][field] = changed
        try:
            assert_gentry_bounds(a,b)
        except ValueError:
            n += 1
        else:
            raise AssertionError('negative documentary admission fixture accepted')
    return {'positive_original_source_fixture': 'PASS',
            'negative_join_or_overclaim_fixtures_rejected': n,
            'real_1999_personal_handoff_proved': False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources', type=Path, default=SOURCES)
    parser.add_argument('--edges', type=Path, default=EDGES)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    # Reuse the existing generic historical-source ledger guard.
    generic = audit_ledgers(args.sources, args.edges)
    s, e = _rows(args.sources, 'id'), _rows(args.edges, 'edge')
    report = {'generic_phase1_checks': generic,
              'gentry_specific': assert_gentry_bounds(s,e)}
    if args.self_test:
        report['self_test'] = self_test(s,e)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

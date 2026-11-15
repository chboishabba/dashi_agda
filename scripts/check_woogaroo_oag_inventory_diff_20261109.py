#!/usr/bin/env python3
"""Deterministic cell/formula comparison of two unverified OAG XLSM inventories.

Inputs are output JSON from check_woogaroo_oag_xlsm_provenance_20261109.py.
The comparison is not workbook recalculation, approval authentication or
an assertion that either source was used for EPBC 2019/8575.
"""
import argparse
import json
from pathlib import Path
from tempfile import TemporaryDirectory


def index_inventory(data):
    if data.get('case') != 'EPBC 2019/8575' or data.get('status') != 'UNVERIFIED_WORKBOOK_CANDIDATE':
        raise ValueError('Wrong case or not a candidate inventory')
    if not data.get('declared_sheet_links_resolved'):
        raise ValueError('Unresolved workbook worksheet mapping')
    named = {}
    for sheet in data.get('sheets_declared', []):
        name, part = sheet.get('name'), sheet.get('worksheet_part')
        if not name or not part or name in named or part in named.values():
            raise ValueError('Ambiguous sheet name or worksheet part')
        named[name] = part
    if not named:
        raise ValueError('No named sheets')
    part_cells = {}
    for sheet in data.get('sheet_cells', []):
        part = sheet.get('part')
        if not part or part in part_cells:
            raise ValueError('Duplicate sheet part')
        part_cells[part] = sheet.get('cells', [])
    if set(named.values()) != set(part_cells):
        raise ValueError('Declared vs extracted worksheet mismatch')
    cells = {}
    groups = {}
    for name, part in named.items():
        groups[name] = {}
        for cell in part_cells[part]:
            address = cell.get('cell')
            key = (name, address)
            if not isinstance(address, str) or not address or key in cells:
                raise ValueError('Missing or duplicate cell address')
            fattr = cell.get('formula_attributes')
            if fattr is not None and not isinstance(fattr, dict):
                raise ValueError('Invalid formula attributes')
            cells[key] = {'type': cell.get('type'), 'formula': cell.get('formula'),
                          'formula_attributes': fattr, 'cached_value': cell.get('cached_value')}
            if fattr and fattr.get('t') == 'shared':
                si = fattr.get('si')
                if si is None:
                    raise ValueError('Shared formula without group index')
                group = groups[name].setdefault(si, {'masters': [], 'followers': []})
                (group['masters'] if cell.get('formula') else group['followers']).append(address)
    unresolved = [{'sheet': sheet, 'si': si, **g} for sheet, by_si in groups.items()
                  for si, g in by_si.items() if len(g['masters']) != 1]
    return cells, unresolved


def compare(before, after):
    a, a_unresolved = index_inventory(before)
    b, b_unresolved = index_inventory(after)
    keys = sorted(set(a) | set(b))
    changes = []
    for sheet, cell in keys:
        old, new = a.get((sheet, cell)), b.get((sheet, cell))
        if old == new:
            continue
        kind = 'added' if old is None else 'removed' if new is None else 'modified'
        changed_fields = [field for field in ('type', 'formula', 'formula_attributes', 'cached_value')
                          if (old or {}).get(field) != (new or {}).get(field)]
        changes.append({'sheet': sheet, 'cell': cell, 'kind': kind,
                        'fields': changed_fields, 'before': old, 'after': new})
    return {'case': 'EPBC 2019/8575', 'status': 'UNVERIFIED_INVENTORY_COMPARISON',
            'before_sha256': before.get('sha256'), 'after_sha256': after.get('sha256'),
            'changed_cell_count': len(changes), 'changes': changes,
            'before_unresolved_shared_formula_groups': a_unresolved,
            'after_unresolved_shared_formula_groups': b_unresolved,
            'shared_formula_semantics_recalculated': False,
            'approval_authenticity_established': False,
            'accepted_oag_cell_join_proved': False}


def selftest():
    base = {'case': 'EPBC 2019/8575', 'status': 'UNVERIFIED_WORKBOOK_CANDIDATE',
            'sha256': 'a'*64, 'declared_sheet_links_resolved': True,
            'sheets_declared': [{'name': 'Inputs', 'worksheet_part': 'xl/worksheets/sheet7.xml'}],
            'sheet_cells': [{'part': 'xl/worksheets/sheet7.xml', 'cells': [
                {'cell': 'B2', 'formula': 'A2*4', 'formula_attributes': {}, 'cached_value': '300', 'type': None},
                {'cell': 'B3', 'formula': None, 'formula_attributes': {'t':'shared','si':'1'}, 'cached_value': '300', 'type': None}]}]}
    import copy
    newer = copy.deepcopy(base)
    newer['sha256'] = 'b'*64
    newer['sheet_cells'][0]['cells'][0]['formula'] = 'A2*5'
    result = compare(base, newer)
    assert result['changed_cell_count'] == 1 and result['changes'][0]['fields'] == ['formula']
    assert result['before_unresolved_shared_formula_groups'][0]['si'] == '1'
    bad = copy.deepcopy(base)
    bad['declared_sheet_links_resolved'] = False
    try: compare(bad, base); raise AssertionError('Unresolved sheet accepted')
    except ValueError as e: assert 'Unresolved' in str(e)
    bad = copy.deepcopy(base)
    bad['sheet_cells'][0]['cells'].append(copy.deepcopy(bad['sheet_cells'][0]['cells'][0]))
    try: compare(bad, base); raise AssertionError('Duplicate cell accepted')
    except ValueError as e: assert 'duplicate' in str(e)
    master = copy.deepcopy(base)
    master['sheet_cells'][0]['cells'][0]['formula_attributes'] = {'t':'shared','si':'1'}
    assert not compare(master, master)['before_unresolved_shared_formula_groups']
    return {'tests': 4, 'passed': 4, 'synthetic_only': True,
            'original_accepted_workbook_compared': False}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--before', type=Path)
    p.add_argument('--after', type=Path)
    p.add_argument('--out', type=Path)
    p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    result = selftest() if args.self_test else compare(json.loads(args.before.read_text()),
                                                       json.loads(args.after.read_text())) if args.before and args.after else p.error('Supply --self-test or --before and --after')
    out = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.out: args.out.write_text(out)
    print(out, end='')


if __name__ == '__main__':
    main()

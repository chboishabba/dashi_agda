#!/usr/bin/env python3
"""Resumable exact signed-node regression using the original arithmetic owners.
Checkpoint receipts are execution records, never native proof witnesses.
Run e.g. timeout 90s python3 -u scripts/check_paper9_signed_integer_matrix_checkpointed.py --checkpoint /tmp/paper9-signed.json --pairs-per-run 3
"""
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from time import monotonic

import check_paper9_full_hecke_symmetry as original
import check_paper9_signed_integer_matrix_weld as signed

ROOT = Path(__file__).resolve().parent
P, D, M = signed.P, signed.D, signed.M
PER_NODE = M + 1 + 2 * (D + 1)
PAIRS = set(range(1, 22))


def fingerprints():
    names = ('check_paper9_full_hecke_symmetry.py',
             'check_paper9_signed_integer_matrix_weld.py',
             'paper9_hecke_packed_mul.cpp', Path(__file__).name)
    out = {}
    for name in names:
        raw = (ROOT / name).read_bytes()
        out[name] = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    return out


def save(path, state):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as f:
        tmp = Path(f.name)
        json.dump(state, f, sort_keys=True, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def read(path, fp):
    if not path.exists():
        return {'schema': 1, 'source_blobs': fp, 'pairs': {}}
    state = json.loads(path.read_text())
    if state.get('schema') != 1 or state.get('source_blobs') != fp:
        raise ValueError('checkpoint source mismatch: use a new checkpoint path')
    for k, v in state['pairs'].items():
        if int(k) not in PAIRS or str(int(k)) != k or v['nodes'] != [int(k), -int(k)] or v['equations'] != 2 * PER_NODE:
            raise ValueError('malformed pair receipt')
    return state


def main():
    if not __debug__:
        raise RuntimeError('assertions must remain enabled')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checkpoint', type=Path, required=True)
    ap.add_argument('--pairs-per-run', type=int, default=3)
    ap.add_argument('--budget-seconds', type=float, default=80)
    ap.add_argument('--recheck', action='store_true', help='discard old pair receipts and replay')
    args = ap.parse_args()
    if not 1 <= args.pairs_per_run <= 21 or not 0 < args.budget_seconds <= 85:
        ap.error('use 1..21 pairs and a soft budget <=85 seconds, with external 90s timeout')
    start = monotonic()
    fp = fingerprints()
    state = {'schema': 1, 'source_blobs': fp, 'pairs': {}} if args.recheck else read(args.checkpoint, fp)
    if args.recheck:
        save(args.checkpoint, state)
    pending = sorted(PAIRS - {int(k) for k in state['pairs']})
    if pending:
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp)/'mul.so'
            subprocess.run(['g++','-O3','-shared','-fPIC',str(ROOT/'paper9_hecke_packed_mul.cpp'),'-lgmp','-o',str(lib)],check=True)
            dll = ctypes.CDLL(str(lib))
            original._mul = dll.multiply
            original._mul.argtypes = [ctypes.c_char_p,ctypes.c_size_t,ctypes.c_char_p,ctypes.c_size_t,ctypes.c_void_p,ctypes.c_size_t]
            original._mul.restype = None
            phi, diag, fixed, divisions = original.matrix()
            j = original.junit(M)
            powers = [[1]+[0]*D]
            for k in range(D):
                powers.append(original.conv(powers[-1], j[:D+1], D))
            assert all(phi[D-k][D] == int(k==D) for k in range(D+1))
            for a in pending[:args.pairs_per_run]:
                if monotonic()-start >= args.budget_seconds:
                    break
                t = monotonic()
                count = sum(signed.check_node(y,j,phi,powers) for y in (a,-a))
                assert count == 2*PER_NODE
                state['pairs'][str(a)] = {'nodes':[a,-a], 'equations':count, 'seconds':round(monotonic()-t,6)}
                save(args.checkpoint, state)
                print('PASS pair',a,'equations',count,'seconds',round(monotonic()-t,3),flush=True)
    total = sum(v['equations'] for v in state['pairs'].values())
    complete = {int(k) for k in state['pairs']} == PAIRS
    assert total == len(state['pairs'])*2*PER_NODE
    print('COMPLETE' if complete else 'CHECKPOINT',len(state['pairs']),'/ 21 pairs;',total,'/',42*PER_NODE,'equations; invocation seconds',round(monotonic()-start,3),flush=True)
    if complete:
        assert total == 75978


if __name__ == '__main__':
    main()

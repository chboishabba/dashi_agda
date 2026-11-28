#!/usr/bin/env python3
"""Resumable exact-source GMP acceptance, one precision/backend per job.
Use timeout 90s python3 -u scripts/check_pi_p0_checkpointed.py --checkpoint /tmp/pi-p0.json
Repeat until COMPLETE. Each invocation preserves completed jobs atomically.
"""
import argparse, json, os, re, subprocess, tempfile
from pathlib import Path
from time import monotonic
import check_pi_p0_consolidated_acceptance as base

def save(path, state):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w',dir=path.parent,delete=False) as f:
        tmp=Path(f.name)
        json.dump(state,f,indent=2,sort_keys=True); f.write('\n')
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp,path)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checkpoint',type=Path,required=True)
    ap.add_argument('--jobs-per-run',type=int,default=1)
    ap.add_argument('--reps',type=int,default=1)
    ap.add_argument('--budget',type=float,default=82)
    args=ap.parse_args()
    if not (1<=args.jobs_per_run<=12 and args.reps in (1,3,5) and 0<args.budget<=85):
        ap.error('invalid job/repetition/budget settings')
    start=monotonic()
    fingerprints={name:subprocess.check_output(['git','hash-object',path],cwd=base.ROOT,text=True).strip() for name,path in base.SOURCES.items()}
    if fingerprints!=base.SOURCE_GIT_BLOBS: raise RuntimeError('original source blob mismatch')
    jobs=[(d,name) for d in base.EXPECTED for name in (('reuse',) if d>=5000000 else ('quotient','reuse'))]
    keys={f'{d}:{name}' for d,name in jobs}
    header={'schema':1,'source_blobs':fingerprints,'reps':args.reps,'expected':{str(k):v for k,v in base.EXPECTED.items()}}
    state=json.loads(args.checkpoint.read_text()) if args.checkpoint.exists() else {**header,'jobs':{}}
    if any(state.get(k)!=v for k,v in header.items()): raise RuntimeError('checkpoint configuration mismatch')
    def validate(key,rows):
        d,name=key.split(':'); d=int(d)
        if key not in keys or len(rows)!=(4 if name=='quotient' else 1): raise RuntimeError('invalid checkpoint rows')
        for row in rows:
            m=re.search(r'(?:sha=|hash=)([0-9a-f]{64})',row)
            if not m or m.group(1)!=base.EXPECTED[d]: raise RuntimeError('digest mismatch '+key)
        if name=='quotient':
            if {re.search(r'mode=(\w+)',row).group(1) for row in rows}!={'plain_two_floors','plain_one_floor','cross_two_floors','cross_one_floor'}: raise RuntimeError('missing mode')
        elif 'mode=inplace' not in rows[0]: raise RuntimeError('wrong reuse mode')
    for key,v in state['jobs'].items(): validate(key,v['rows'])
    def run(argv):
        remaining=args.budget-(monotonic()-start)
        if remaining<=0: raise subprocess.TimeoutExpired(argv,0)
        return subprocess.run(argv,cwd=base.ROOT,capture_output=True,text=True,check=True,timeout=remaining).stdout
    pending=[(d,name) for d,name in jobs if f'{d}:{name}' not in state['jobs']]
    with tempfile.TemporaryDirectory(prefix='pi-p0-checkpoint-') as tmp:
        binaries={}
        for d,name in pending[:args.jobs_per_run]:
            key=f'{d}:{name}'
            try:
                if name not in binaries:
                    binary=str(Path(tmp)/name)
                    run(['g++','-std=c++17','-O3',base.SOURCES[name],'-lgmpxx','-lgmp','-lcrypto','-o',binary])
                    binaries[name]=binary
                t=monotonic()
                argv=[binaries[name],str(d),str(args.reps)] if name=='quotient' else [binaries[name],str(d),'inplace',str(args.reps)]
                rows=[line for line in run(argv).splitlines() if line.startswith(('BENCH ','SUMMARY '))]
                validate(key,rows)
                state['jobs'][key]={'rows':rows,'seconds':monotonic()-t}
                save(args.checkpoint,state)
                print('PASS',key,*rows,sep='\n',flush=True)
            except subprocess.TimeoutExpired:
                print('TIMEOUT',key,'not accepted; earlier checkpoints preserved',flush=True)
                break
    print('COMPLETE' if set(state['jobs'])==keys else 'CHECKPOINT',len(state['jobs']),'/',len(keys),'jobs',flush=True)

if __name__=='__main__': main()

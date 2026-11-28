"""Bounded local continuation of all 90 exact source seed/normalizer columns.

Every child invocation has its own <=90s hard deadline. Parent output
is immutable; resume only with verified hash. A no-progress child stops
the batch instead of repeatedly paying an oversized source action.
No source data fabricated; completed manifests feed rank/factor assembly.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_actual_weyl_frame_bidi import require

ROOT=Path(__file__).resolve().parents[1]


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def write(path,r):
    with path.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')


def inputs(a):
    names=('local','frame') if a.mode=='seed' else ('local','source_rank','target_rank','modular_factor','seed_manifest')
    out={}
    for n in names:
        p=getattr(a,n);h=getattr(a,n+'_sha256')
        require(p is not None and h is not None and sha(p)==h,'pinned input '+n)
        out[n]=dict(path=str(p.resolve()),sha256=h)
    if a.mode=='seed':require(a.zeta in (2,4),'actual phase')
    return out


def chain(d,mode,j,inp,zeta):
    files=sorted(d.glob('chunk-*.json'));last=None;parent=None;previous=-1
    expected='actual_cyclotomic_seed_lift' if mode=='seed' else 'actual_cyclotomic_normalizer_column'
    for k,p in enumerate(files,1):
        require(p.name==f'chunk-{k:06d}.json','noncontiguous source chain')
        r=json.loads(p.read_text());c=r['contract']
        require(c['seed']==j and r['parent_receipt_sha256']==parent and
                c['local_sha256']==inp['local']['sha256'] and
                r['status'] in ('bounded_incomplete',expected),'source receipt chain scope')
        if mode=='seed':
            require(c['frame_sha256']==inp['frame']['sha256'] and c['zeta']==zeta,'phase changed')
            cursor=r['completed_projectors'];end=7
        else:
            require(all(c[n+'_sha256']==inp[n]['sha256'] for n in ('source_rank','target_rank','modular_factor')),
                    'normalizer source scope changed')
            cursor=r['cursor'];end=r['stages']
        require(0<=cursor<=end and cursor>=previous and (last is None or last['status']=='bounded_incomplete'),
                'source cursor or completion mismatch')
        require(r['status']!=expected or cursor==end,'false terminal marker')
        previous=cursor;parent=sha(p);last=r
    return dict(files=files,last=last,parent=parent,cursor=previous,complete=bool(last and last['status']==expected))


def run(a):
    require(1<=a.chunks<=1000 and 0<a.seconds<a.hard_timeout<=90,'bounded local source batch')
    inp=inputs(a);root=a.directory.resolve();root.mkdir(parents=True,exist_ok=True)
    registration=dict(mode=a.mode,inputs=inp,zeta=a.zeta if a.mode=='seed' else None,
        source_driver_sha256=sha(Path(__file__)))
    reg=root/'registration.json'
    if reg.exists():require(json.loads(reg.read_text())==registration,'source registration changed')
    else:write(reg,registration)
    seeds=None
    if a.mode=='factor':
        seeds=read_pinned(a.seed_manifest,a.seed_manifest_sha256)
        require(type(seeds) is list and len(seeds)==90,'actual source seed manifest')
    for i in range(a.chunks+1):
        states=[]
        for j in range(90):
            d=root/f'{j:03d}';d.mkdir(exist_ok=True)
            states.append(chain(d,a.mode,j,inp,a.zeta))
        done=sum(s['complete'] for s in states)
        if done==90:
            rows=[dict(path=str(s['files'][-1].relative_to(root)),sha256=s['parent']) for s in states]
            m=root/'complete-manifest.json'
            if m.exists():require(json.loads(m.read_text())==rows,'terminal manifest changed')
            else:write(m,rows)
            print('COMPLETE',m,sha(m),flush=True);return
        if i==a.chunks:
            print('IN_PROGRESS',done,90,flush=True);return
        j=next(j for j,s in enumerate(states) if not s['complete']);s=states[j]
        path=root/f'{j:03d}'/f'chunk-{len(s["files"])+1:06d}.json'
        module='scripts.x369_3b_cyclotomic_projector' if a.mode=='seed' else 'scripts.x369_3b_cyclotomic_normalizer'
        cmd=[sys.executable,'-m',module,'--seconds',str(a.seconds),'--output',str(path)]
        for n,r in inp.items():
            if n=='seed_manifest':continue
            k=n.replace('_','-');cmd+=['--'+k,r['path'],'--'+k+'-sha256',r['sha256']]
        if a.mode=='seed':cmd+=['--zeta',str(a.zeta),'--seed',str(j)]
        else:
            row=seeds[j];p=(a.seed_manifest.parent/row['path']).resolve()
            require(sha(p)==row['sha256'],'source seed changed')
            cmd+=['--seed',str(p),'--seed-sha256',row['sha256']]
        if s['last']:cmd+=['--resume',str(s['files'][-1]),'--resume-sha256',s['parent']]
        r=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True,timeout=a.hard_timeout)
        require(r.returncode in (0,2) and path.is_file(),'actual source child failed '+r.stderr[-2000:])
        n=chain(path.parent,a.mode,j,inp,a.zeta)
        require(n['complete']==(r.returncode==0),'child completion mismatch')
        print('SOURCE_CHUNK',j,n['cursor'],n['complete'],n['parent'],flush=True)
        if not n['complete'] and n['cursor']<=s['cursor']:
            raise RuntimeError('no complete projector/action stage; split this primitive source word further')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--mode',choices=('seed','factor'),required=True);p.add_argument('--directory',type=Path,required=True)
    for n in ('local','frame','source-rank','target-rank','modular-factor','seed-manifest'):
        p.add_argument('--'+n,type=Path);p.add_argument('--'+n+'-sha256')
    p.add_argument('--zeta',type=int,choices=(2,4))
    p.add_argument('--chunks',type=int,default=18);p.add_argument('--seconds',type=float,default=75);p.add_argument('--hard-timeout',type=float,default=90)
    run(p.parse_args())

if __name__=='__main__':main()

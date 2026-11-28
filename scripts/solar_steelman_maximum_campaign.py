"""Local staged maximum-cut campaign. Run each stage under timeout 90s.
Only load checkpoints generated and controlled by the caller; pickle is unsafe
for untrusted files. Source/content identity is checked before combining blocks.
"""
import argparse,hashlib,json,pickle,os
from pathlib import Path
import numpy as np

HERE=Path(__file__).resolve().parent

def sha(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def sources():
    paths=sorted(set(HERE.glob('solar_*.py')) | set(HERE.glob('check_smith_filsinger_solar_*.py')))
    return {p.name:sha(p) for p in paths}

def json_atomic(path,obj):
    tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(obj,sort_keys=True,indent=2));os.replace(tmp,path)

def save(path,obj,upstream,src):
    tmp=path.with_suffix('.tmp')
    with open(tmp,'wb') as f:pickle.dump(obj,f,pickle.HIGHEST_PROTOCOL)
    os.replace(tmp,path)
    json_atomic(path.with_suffix('.json'),dict(sha=sha(path),upstream=upstream,sources=src))

def load(path,upstream,src):
    meta=json.loads(path.with_suffix('.json').read_text())
    if meta!=dict(sha=sha(path),upstream=upstream,sources=src):raise ValueError("checkpoint identity mismatch: "+str(path))
    with open(path,'rb') as f:return pickle.load(f)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('stage',choices=['seven','metric','mediator','static','inverse','preflight','nonlinear','tangent','block','assemble','delay','delay-run','span','span-full','delay-tangent','delay-action','reciprocal','history-block','history-assemble','history-leaf','static-leaf','history-bounds','history-certify','history-cert-assemble'])
    p.add_argument('--work',required=True);p.add_argument('--tol',type=float,default=1e-7)
    p.add_argument('--perturb',type=float,default=0.);p.add_argument('--periods',type=int,default=1)
    p.add_argument('--start',type=int);p.add_argument('--stop',type=int);p.add_argument('--delay',type=float,default=.01)
    p.add_argument('--degree',type=int,default=8)
    p.add_argument('--export-trace',action='store_true')
    p.add_argument('--knots',type=int,default=4)
    p.add_argument('--exact-null',action='store_true');x=p.parse_args()
    work=Path(x.work);work.mkdir(parents=True,exist_ok=True);src=sources()
    seven=work/'seven.pkl';metric=work/'metric.pkl';med=work/'mediator.pkl'
    if x.stage=='seven':
        from solar_steelman_seven_edge import run
        save(seven,run(),{},src);return
    d=load(seven,{},src);up={'seven':sha(seven)}
    if x.stage=='metric':
        from solar_steelman_material_metric import run
        save(metric,run(d),up,src);return
    m=load(metric,up,src);up['metric']=sha(metric)
    if x.stage=='mediator':
        from solar_steelman_autonomous_mediator import run
        save(med,run(m),up,src);return
    a=load(med,up,src);up['mediator']=sha(med)
    if x.stage=='static':
        from solar_steelman_combined_static_fibre import run
        run(m,a,x.exact_null)
    elif x.stage=='inverse':
        from solar_steelman_physical_inverse import run
        run(a)
    elif x.stage in ('span','span-full'):
        from solar_steelman_constitutive_span import local_inverse
        local_inverse(a,x.stage=='span-full')
    elif x.stage=='reciprocal':
        from solar_steelman_reciprocal_port_inverse import construct
        construct(a)
    elif x.stage=='static-leaf':
        from solar_steelman_history_exact_bounds import static_leaf
        z=static_leaf(m,a)
        save(work/'static_leaf.pkl',z,up,src)
        print(z['status'],z['rank'],z['nullity'],flush=True)
    elif x.stage=='history-bounds':
        from solar_steelman_history_exact_bounds import ambient_bounds
        z=ambient_bounds(m,a)
        save(work/'history_bounds.pkl',z,up,src)
        print('conditional ambient coefficient bounds', {k:float(v) for k,v in z.items()},flush=True)
    elif x.stage=='history-leaf':
        from solar_steelman_history_leaf import construct
        construct(m,a,x.delay)
    elif x.stage in ('history-certify','history-cert-assemble'):
        from solar_steelman_history_trace_certificate import certify
        from solar_steelman_history_clock import aggregate
        prefix=f'H_{x.delay:.12g}_{x.knots}_{x.tol:.12g}'
        def verify_block(path):
            meta=dict(upstream=up,sources=src,tol=x.tol,delay=x.delay,knots=x.knots)
            if json.loads(path.with_suffix('.json').read_text())!=dict(meta,sha=sha(path)):
                raise ValueError('block provenance mismatch')
            trace=path.with_name(path.stem+'_trace.npz')
            if json.loads(trace.with_suffix('.json').read_text())!=dict(meta,sha=sha(trace),block=sha(path)):
                raise ValueError('trace provenance mismatch')
            return trace,dict(meta,block=sha(path),trace=sha(trace),degree=x.degree)
        if x.stage=='history-certify':
            if x.start is None or x.stop is None:raise ValueError('column bounds required')
            path=work/f'{prefix}_{x.start:04d}_{x.stop:04d}.npz'
            trace,provenance=verify_block(path)
            z=certify(m,a,trace,x.degree,block_path=path)
            out=path.with_name(path.stem+f'_cert{x.degree}.pkl')
            save(out,z,provenance,src)
            print('conditional rational-time block certificate written',out,flush=True)
        else:
            paths=sorted(p for p in work.glob(prefix+'_*.npz') if not p.name.endswith(('_leaf.npz','_trace.npz')))
            if not paths:raise ValueError('missing blocks')
            records=[];clocks=set();spacings=set();matrices=[]
            for path in paths:
                trace,provenance=verify_block(path)
                z=load(path.with_name(path.stem+f'_cert{x.degree}.pkl'),provenance,src)
                with np.load(path,allow_pickle=False) as f:
                    assert int(f['start'])==z['start'] and int(f['stop'])==z['stop']
                    matrices.append((z['start'],f['M']))
                records.append((z['start'],z['stop'],z['state_matrix_error'],z['history_matrix_error']))
                clocks.add((z['T'],z['delay']));spacings.add(z['spacing'])
            assert len(clocks)==len(spacings)==1
            M=np.column_stack([v for _,v in sorted(matrices,key=lambda z:z[0])])
            assert M.shape[0]==M.shape[1]
            cap=aggregate(records,M.shape[0])
            save(work/f'{prefix}_cert{x.degree}_aggregate.pkl',dict(matrix=M,errors=cap,clock=next(iter(clocks)),spacing=next(iter(spacings)),records=records),up,src)
            print('conditional rational-time complete block error ledger; exact-period/leaf projection/contraction not yet certified',flush=True)
    elif x.stage in ('history-block','history-assemble'):
        from solar_steelman_history_section import block,assemble
        prefix=f'H_{x.delay:.12g}_{x.knots}_{x.tol:.12g}'
        if x.stage=='history-block':
            if x.start is None or x.stop is None:raise ValueError("column bounds required")
            path=work/f'{prefix}_{x.start:04d}_{x.stop:04d}.npz'
            tmp=path.with_name(path.stem+'.tmp.npz')
            block(m,a,x.delay,x.knots,x.start,x.stop,x.tol,tmp,export=x.export_trace);os.replace(tmp,path)
            if x.export_trace:
                trace=path.with_name(path.stem+'_trace.npz')
                os.replace(tmp.with_name(tmp.stem+'_trace.npz'),trace)
                json_atomic(trace.with_suffix('.json'),dict(sha=sha(trace),upstream=up,sources=src,tol=x.tol,delay=x.delay,knots=x.knots,block=sha(path)))
            json_atomic(path.with_suffix('.json'),dict(sha=sha(path),upstream=up,sources=src,tol=x.tol,delay=x.delay,knots=x.knots))
        else:
            paths=sorted(p for p in work.glob(prefix+'_*.npz') if not p.name.endswith(('_leaf.npz','_trace.npz')))
            if not paths:raise ValueError("no history blocks")
            for path in paths:
                meta=json.loads(path.with_suffix('.json').read_text())
                if meta!=dict(sha=sha(path),upstream=up,sources=src,tol=x.tol,delay=x.delay,knots=x.knots):raise ValueError("history provenance mismatch")
            M=assemble(paths)
            from solar_steelman_history_leaf import construct,section
            _,_,Q=construct(m,a,x.delay)
            A,defect=section(M,Q,len(a['models']),x.knots)
            out=work/f'{prefix}_leaf.npz'
            np.savez(out,M=A,Q=Q,defect=defect)
            json_atomic(out.with_suffix('.json'),dict(sha=sha(out),upstream=up,sources=src,tol=x.tol,delay=x.delay,knots=x.knots))
    elif x.stage=='preflight':
        from solar_steelman_reservoir_return import preflight
        preflight(m,a)
    elif x.stage=='nonlinear':
        from solar_steelman_reservoir_return import integrate
        integrate(m,a,x.tol,x.perturb,x.periods)
    elif x.stage=='tangent':
        from solar_steelman_anchored_monodromy import check
        check(m,a)
    elif x.stage=='block':
        from solar_steelman_anchored_monodromy import block
        if x.start is None or x.stop is None:raise ValueError("column bounds required")
        path=work/f'M_{x.tol:.12g}_{x.start:03d}_{x.stop:03d}.npz'
        tmp=path.with_name(path.stem+'.tmp.npz')
        block(m,a,x.start,x.stop,x.tol,tmp);os.replace(tmp,path)
        json_atomic(path.with_suffix('.json'),dict(sha=sha(path),upstream=up,sources=src,tol=x.tol))
    elif x.stage=='assemble':
        from solar_steelman_anchored_monodromy import assemble
        paths=sorted(work.glob(f'M_{x.tol:.12g}_*.npz'))
        if not paths:raise ValueError("no monodromy blocks")
        for path in paths:
            meta=json.loads(path.with_suffix('.json').read_text())
            if meta!=dict(sha=sha(path),upstream=up,sources=src,tol=x.tol):raise ValueError("monodromy provenance mismatch")
        assemble(paths)
        from solar_steelman_return_compatibility import run
        matrices=[]
        for path in paths:
            with np.load(path,allow_pickle=False) as f:matrices.append((int(f['start']),f['M']))
        M=np.column_stack([v for _,v in sorted(matrices,key=lambda x:x[0])])
        out=work/f'full_{x.tol:.12g}.npz'
        np.savez(out,M=M)
        json_atomic(out.with_suffix('.json'),dict(sha=sha(out),upstream=up,sources=src,tol=x.tol))
        run(M,m,a)
    elif x.stage in ('delay-tangent','delay-action'):
        from solar_steelman_delayed_tangent import check,history_action
        if x.stage=='delay-tangent':check(m,a,x.delay)
        else:history_action(m,a,x.delay,x.tol,x.periods)
    elif x.stage in ('delay','delay-run'):
        from solar_steelman_retarded_face_return import run
        run(m,a,x.delay,x.tol,x.periods,x.perturb,x.stage=='delay-run')
    print('STAGE COMPLETE',x.stage,flush=True)

if __name__=='__main__':main()

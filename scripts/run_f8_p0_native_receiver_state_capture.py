"""Original F8 P0 mode3 receiver-time capture WITHOUT editing the native solver.

Import and execute the exact source-owned run_f8_lxix_native_source_matrix.main,
interposing a transparent wrapper on the original stage dispatcher only to
COPY U/P/M and U_T at the *pre-lookahead t=12 stage* (it==nt, original U).
The callback delegates the actual original Numba stage exactly once and
never modifies any operand. All original NativeCheckpoint fingerprints
remain unchanged. An extra .receiver-state.npz is an INSTRUMENTED receipt,
not an original uninstrumented checkpoint or an independent PDE solver.

Use a fresh native workdir with F8_CAPTURE_RECEIVER_STATE=1 through the
integrated cooperative runner to produce the sidecar; a completed previous
original NPZ cannot retroactively produce same-time P/M. No CI.
"""
import hashlib,json,os,sys,tempfile
from pathlib import Path
import numpy as np
import ksw668_f8_tt_multipole as original
import run_f8_lxix_native_source_matrix as original_driver

def atomic_npz(path,**arrays):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent,delete=False,suffix='.npz') as f:
        tmp=f.name
        try:
            np.savez(f,**arrays)
            f.flush();os.fsync(f.fileno());os.replace(tmp,path)
        finally:
            if os.path.exists(tmp):os.unlink(tmp)

def main():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('label',choices=('A0','A1','C0','C1'))
    parser.add_argument('--work',type=Path,default=Path('.local-f8-lxix-instrumented'))
    parser.add_argument('--budget',type=float,default=12.)
    args=parser.parse_args()
    args.work.mkdir(parents=True,exist_ok=True)
    sidecar=args.work/(args.label+'.receiver-state.npz')
    captured={}
    unmodified_stage=original.stage
    solver_blob_sha=hashlib.sha256(Path(original.__file__).read_bytes()).hexdigest()

    def observe_and_delegate(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order):
        # Trace only the original propagate Python stack, not the JIT interior.
        frame=sys._getframe(1)
        local=frame.f_locals
        target=(frame.f_code.co_name=='propagate'
                and local.get('it',-1)==local.get('nt',-2)
                and local.get('U') is U and local.get('P') is P
                and local.get('M') is M)
        if target:
            if captured:raise AssertionError('duplicate original t12 same-state capture')
            if normal_order!=3 or abs(b-1/12)>1e-10 or abs(amp)>1e-14:
                raise AssertionError('original mode3 at receiver clock/source ended')
            captured.update(U=U.copy(),P=P.copy(),M=M.copy(),
                dr=float(dr),dy=float(dy),b=float(b),v=float(v),
                amp=float(amp),source=src.copy())
        unmodified_stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order)
        if target:captured['Ut']=outU.copy()

    original.stage=observe_and_delegate
    original_driver.propagate=original.propagate
    saved_argv=sys.argv[:]
    try:
        sys.argv=[saved_argv[0],args.label,'--work',str(args.work),'--budget',str(args.budget)]
        status=original_driver.main()
    finally:
        sys.argv=saved_argv
        original.stage=unmodified_stage

    if status==75:
        if captured:raise AssertionError('caught last-stage state but producer checkpoint interrupted')
        return 75
    if status!=0:return status
    if not captured:
        # The original checkpoint may have already completed without the
        # instrumentation; nothing supports manufacturing its t12 P/M.
        if sidecar.exists():return 0
        raise RuntimeError('original run completed without t12 capture; use fresh checkpoint workdir')
    with np.load(args.work/(args.label+'.npz'),allow_pickle=False) as z:
        assert int(z['cursor'].item())==int(json.loads(z['identity'].item())['config']['nt'])+1
        assert np.array_equal(z['w1'],captured['U'][:,0,:])
        assert np.array_equal(z['w3'],captured['Ut'][:,0,:])
        original_identity=z['identity'].item()
        checkpoint_wall_sha=hashlib.sha256(z['w1'].tobytes()).hexdigest()
    receipt=args.work/(args.label+'.json')
    assert receipt.is_file()
    label=args.label
    metadata=json.dumps(dict(label=label,capture_plane='t=12 pre-lookahead, original it==nt after enforce',
        original_checkpoint_identity_sha256=hashlib.sha256(original_identity.encode()).hexdigest(),
        original_checkpoint_wall_sha256=checkpoint_wall_sha,
        original_solver_sha256=solver_blob_sha,
        original_driver='run_f8_lxix_native_source_matrix.main',
        classification='instrumented same-time original U,P,M,Ut copy, no numerical state modification'),sort_keys=True)
    atomic_npz(sidecar,metadata=metadata,
        U=captured['U'],P=captured['P'],M=captured['M'],Ut=captured['Ut'],
        source=captured['source'],dr=captured['dr'],dy=captured['dy'],
        b=captured['b'],v=captured['v'],amp=captured['amp'])
    print(sidecar,flush=True)
    return 0

if __name__=='__main__':
    raise SystemExit(main())

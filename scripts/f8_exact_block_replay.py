"""Exact reverse-order leaf replay with logarithmic state storage per block.

Advance must be deterministic and return new arrays. All indices and both
carriers are retained. No interpolation, compression or quotient is used.
Commit accumulated reverse outputs only after exhausting the generator.
"""
import numpy as np


def reverse_leaves(lo, hi, c, f, ce, fe, C, G):
    if not 0 <= lo < hi:
        raise ValueError('invalid replay interval')
    if hi-lo == 1:
        cn, fn = C(c, lo), G(f, lo)
        if not np.array_equal(cn, ce) or not np.array_equal(fn, fe):
            raise ValueError('block replay mismatch at %d' % hi)
        yield lo, c, f, cn, fn
        return
    mid = (lo+hi)//2
    cm, fm = c, f
    for n in range(lo, mid):
        cm, fm = C(cm, n), G(fm, n)
    yield from reverse_leaves(mid, hi, cm, fm, ce, fe, C, G)
    yield from reverse_leaves(lo, mid, c, f, cm, fm, C, G)


def check():
    rng = np.random.default_rng(1547)
    cases = leaves = resumes = corrupt = 0
    for nstep in (1, 2, 3, 7, 16, 31, 64, 127):
        for dim in (3, 9, 17):
            A = rng.normal(size=(nstep, dim, dim))*.05 + np.eye(dim)
            B = rng.normal(size=(nstep, dim, dim))*.04 + np.eye(dim)
            a, b = rng.normal(size=(2, nstep, dim))
            C = lambda x,n: A[n]@x+a[n]
            G = lambda x,n: B[n]@x+b[n]
            c, f = [rng.normal(size=dim)], [rng.normal(size=dim)]
            for n in range(nstep):
                c.append(C(c[-1],n)); f.append(G(f[-1],n))
            obs = rng.normal(size=(nstep+1,dim))
            def consume(cuts):
                lam = obs[-1].copy(); signed = np.zeros(dim); absolute = signed.copy()
                for lo,hi in reversed(list(zip(cuts,cuts[1:]))):
                    for n,xc,xf,cn,fn in reverse_leaves(lo,hi,c[lo],f[lo],c[hi],f[hi],C,G):
                        assert all(np.array_equal(x,y) for x,y in zip((xc,xf,cn,fn),(c[n],f[n],c[n+1],f[n+1])))
                        d = G(xc,n)-cn; v = lam*d
                        signed += v; absolute += abs(v)
                        lam = obs[n]+B[n].T@lam
                    # Model a serialized boundary without altering floating values.
                    lam=lam.copy(); signed=signed.copy(); absolute=absolute.copy()
                return lam,signed,absolute
            x=consume(list(range(nstep+1))); y=consume([0,nstep]);
            assert all(np.array_equal(u,v) for u,v in zip(x,y))
            direct=sum(o@(v-u) for o,u,v in zip(obs,c,f))
            assert np.isclose(direct,x[0]@(f[0]-c[0])+x[1].sum(),rtol=1e-10,atol=1e-10)
            for split in sorted({1,nstep//2,nstep-1}-{0,nstep}):
                assert all(np.array_equal(u,v) for u,v in zip(x,consume([0,split,nstep])))
                resumes+=1
            bad=f[-1].copy();bad[0]+=1
            try: list(reverse_leaves(0,nstep,c[0],f[0],c[-1],bad,C,G))
            except ValueError: corrupt+=1
            else: raise AssertionError('corrupt checkpoint accepted')
            cases+=1;leaves+=nstep
    return dict(cases=cases,reverse_leaves=leaves,resume_splits=resumes,corrupt_rejections=corrupt)


if __name__=='__main__': print(check())

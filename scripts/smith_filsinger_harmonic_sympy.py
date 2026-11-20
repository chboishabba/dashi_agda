"""Finite sampled harmonic response, not a physical scattering matrix."""
import sympy as S
from smith_filsinger_floquet_sympy import floquet
from smith_filsinger_switched_ade_sympy import step


def clean(x):
    return x.applyfunc(lambda a: S.simplify(S.expand_complex(a)))


def harmonic_transfer(maps, lam, root):
    N=len(maps); lam=S.sympify(lam); root=S.sympify(root)
    if not N or lam==0 or S.simplify(root**N-1)!=0 or any(S.simplify(root**k-1)==0 for k in range(1,N)):
        raise ValueError('nonzero multiplier and primitive Nth root required')
    d,p=maps[0][1].shape
    out=S.zeros(N*d,N*p)
    for n in range(N):
        for k in range(p):
            _,z=floquet(maps,S.simplify(lam*root**n),S.eye(p)[:,k])
            for m in range(N):
                out[m*d:(m+1)*d,n*p+k]=clean(sum((z[j]/lam**j*root**(-m*j) for j in range(N)),S.zeros(d,1))/N)
    return out


def quadrature_step(z, jn, jc, material, eps1, dt, curl=None, load=0):
    """Sum real and imaginary trajectory work; not a single real-field cycle."""
    r=step(z.applyfunc(S.re),jn.applyfunc(S.re),jc.applyfunc(S.re),material,eps1,dt,curl,load)
    i=step(z.applyfunc(S.im),jn.applyfunc(S.im),jc.applyfunc(S.im),material,eps1,dt,curl,load)
    keys=('storage_delta','natural_work','controller_work','modulation_work','ohmic','relaxation','useful_load','residual')
    return dict(z=clean(r['z']+S.I*i['z']),**{k:S.simplify(r[k]+i[k]) for k in keys})

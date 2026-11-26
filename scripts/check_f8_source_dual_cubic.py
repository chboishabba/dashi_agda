"""Linear cubic r^2 dual reconstruction, original source primitive moments.
An explicit source-load intervention on the unchanged native finite propagator.
No claim this is the original emitter or a certified continuum approximation.
"""
import argparse,json,math,hashlib
from pathlib import Path
import numpy as np
import sympy as S
from scipy.integrate import quad
from check_f8_source_dual_primitive import EPS,volume,pair
from ksw668_f8_fv_source_flux import primitives,compact_bump


def moment(i,j):
    # Original common-prepotential adjoint on monomial u^(2j).
    if i==0:
        if j<2:return 0.
        factor=S.Rational(2,5)*(2*j)*(2*j+1)*(2*j-2)*(2*j-1);power=2*j-2
    elif i==1:
        if j==0:return 0.
        factor=S.Rational(4,7)*(2*j+5)*(2*j+3)*(2*j)*(2*j+1);power=2*j
    else:
        factor=S.Rational(1,35)*math.prod(2*j+k for k in (9,7,5,3));power=2*j+2
    return float(factor)*quad(lambda u:u**power*compact_bump(u),0,1,epsabs=1e-13)[0]


def load(dr,i):
    h=S.Rational(str(dr))/S.Rational(str(EPS));n=int(S.ceiling(1/h))+1
    x=S.symbols('x');nodes=[(j*h)**2 for j in range(n)];p=primitives()[i];d=3+4*i;out=np.zeros(n);checks=0
    for j in range(n-1):
        a=float(j*h);b=min(1.,float((j+1)*h));start=max(0,min(j-1,n-4));ids=range(start,start+4)
        basis=[S.prod((x-nodes[k])/(nodes[l]-nodes[k]) for k in ids if k!=l) for l in ids]
        for m in range(4):
            assert S.expand(sum(nodes[l]**m*f for l,f in zip(ids,basis))-x**m)==0;checks+=1
        for l,f in zip(ids,basis):
            fun=S.lambdify(x,f,'numpy');df=S.lambdify(x,S.diff(f,x),'numpy')
            val=-quad(lambda u:float(p(u))*2*u*df(u*u),a,b,epsabs=1e-12,epsrel=1e-12)[0]
            if i==2:val+=quad(lambda u:27*u*u*compact_bump(u)*fun(u*u),a,b,epsabs=1e-12,epsrel=1e-12)[0]
            out[l]+=val
    errors=[]
    for m in range(4):
        coeff=np.array([float(z)**m for z in nodes]);observed=float(out@coeff);expected=moment(i,m)
        err=abs(observed-expected)/max(abs(out)@abs(coeff),abs(expected),1e-300);assert err<2e-10,(dr,i,m,observed,expected,err)
        errors.append(dict(j=m,observed=observed,expected=expected,scaled_error=float(err)))
    return out*EPS**d,checks,errors


def run(work):
    results={};checks=0
    for kind,dr in [('coarse',.008),('fine',.006)]:
        with np.load(work/(kind+'.source-kernel.npz'),allow_pickle=False) as z:
            assert z['n'].item()==-1;k=z['kappa'].sum(axis=0)
        rows=[]
        for i,d in enumerate((3,7,11)):
            q=k[i,:-1]/volume(dr,k.shape[-1]-1,d);l,n,e=load(dr,i);checks+=n
            source=l/volume(dr,len(l),d);signed=float(k[i,:len(l)]@source);terms=l*q[:len(l)]
            assert abs(signed-terms.sum())<1e-12*max(abs(terms).sum(),1e-300)
            rows.append(dict(d=d,source_load=source.tolist(),moments=e,cubic=float(terms.sum()),absolute=float(abs(terms).sum()),terms=terms.tolist(),cell=pair(q,dr,i,'cell')['signed'],hat=pair(q,dr,i,'hat')['signed'],pchip=pair(q,dr,i,'pchip')['signed']))
        results[kind]=dict(dr=dr,rows=rows,sums={s:sum(x[s] for x in rows) for s in ('cell','hat','pchip','cubic')})
    out=dict(scope='finite source-load intervention, exact polynomial reproduction and numerical primitive quadrature; no propagation/continuum certification',exact_reproduction_checks=checks,results=results)
    (work/'source_cubic.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(exact=checks,summary={k:v['sums'] for k,v in results.items()},max_moment_error=max(x['scaled_error'] for v in results.values() for r in v['rows'] for x in r['moments'])),indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path,default=Path('.local-f8-source-dual'));a=p.parse_args();run(a.work)

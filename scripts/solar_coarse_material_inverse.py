"""Reverse material bounds for target in-phase quarter-clock receiver field.
Exact scalar transverse triangle sector, not all geometries or target phases.
"""
import sympy as S
from itertools import product
from solar_coarse_source_cycle import fixture
from solar_gauss_ade_weld import augmented_step


def inverse_in_phase(d,c,amplitude,lo=1,hi=2):
    q,lo,hi=map(S.Rational,(amplitude,lo,hi));assert q>0 and 0<lo<=hi and d[1].rows==1
    h,a,o,g,s,l,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'))
    w=d[1].T;k=(w.T*w)[0];assert k>0
    t,D0,B0=S.symbols('t D0 B0',real=True);inc=[1,0,-1,0];em=[q*i for i in inc]
    E=[t];B=[B0]
    for e in em:E.append(2*e-E[-1]);B.append(B[-1]-h*k*e)
    assert E[-1]==t and B[-1]==B0
    # Mean Ampere on a closed periodic displacement forces mean B=0.
    b0=S.solve(sum(B[:4]),B0)[0];B=[x.subs(B0,b0) for x in B]
    P=S.symbols('P0:4',real=True);V=S.symbols('V0:4',real=True);eq=[]
    for i,e in enumerate(em):
        j=(i+1)%4;pm=(P[i]+P[j])/2;vm=(V[i]+V[j])/2
        eq += [P[j]-P[i]-h*vm,V[j]-V[i]-h*(a*e-g*vm-o*pm)]
    sol=S.solve(eq,(*P,*V),dict=True)[0];P=[sol[x] for x in P];V=[sol[x] for x in V]
    D=[D0]
    for i,e in enumerate(em):
        j=(i+1)%4;D.append(D[-1]+h*((B[i]+B[i+1])/2-(s+l+p*p)*e +2*p*inc[i]))
    assert S.expand(D[-1]-D0)==0
    # Eliminate D0 by pairing all lower/upper affine bounds. The remaining
    # exact one-dimensional halfspaces determine a closed interval for t.
    feasible=[];excluded=0
    for signs in product((-1,1),repeat=4):
        lower=[];upper=[];ineq=[]
        for i,sign in enumerate(signs):
            e=E[i];v=D[i]-D0-P[i];ineq.append(sign*e)
            lower.append((lo if sign==1 else hi)*e-v)
            upper.append((hi if sign==1 else lo)*e-v)
        ineq += [u-l for u in upper for l in lower]
        tl,th=-S.oo,S.oo;bad=False
        for z in ineq:
            z=S.expand(z);slope=z.coeff(t);intercept=z.subs(t,0)
            if slope>0:tl=max(tl,-intercept/slope)
            elif slope<0:th=min(th,-intercept/slope)
            elif intercept<0:bad=True;break
        if bad or tl>th:excluded+=1;continue
        tv=tl if tl!=-S.oo else th if th!=S.oo else S.Integer(0)
        dv=max(z.subs(t,tv) for z in lower)
        assert dv<=min(z.subs(t,tv) for z in upper)
        sub={t:tv,D0:dv}
        ev=[z.subs(sub) for z in E];dval=[z.subs(sub) for z in D]
        eps=[S.simplify((dval[i]-P[i])/ev[i]) if ev[i]!=0 else lo for i in range(4)];eps.append(eps[0]);assert all(lo<=x<=hi for x in eps)
        # Same inverse witness is reopened on full triangle incidence ADE.
        initial=S.Matrix.vstack(ev[0]*w,S.Matrix([B[0]]),P[0]*w,V[0]*w);x=initial;W=[]
        for i in range(4):
            r=augmented_step(d,[eps[i]]*len(w),[eps[i+1]]*len(w),[S.Integer(1)],a,o,g,s+p*p,l,x,2*p*inc[i]*w,S.zeros(len(w),1),h)
            assert (x[:len(w),:]+r['state'][:len(w),:])/2==em[i]*w
            W.append(r);x=r['state']
        assert x==initial
        feasible.append(dict(eps=eps,initial=initial,work=W))
    return dict(status='INHABITED_IN_PHASE_FIBRE' if feasible else 'EMPTY_IN_PHASE_FIBRE',sign_sectors=16,excluded_sectors=excluded,witnesses=feasible,physical_admission=False)


def run():
    d,c=fixture()
    for q in [S.Rational(1,10),S.Rational(4,5)]:
        r=inverse_in_phase(d,c,q);print(q,r['status'],r['excluded_sectors'])
    # Unconstrained resonant static material gives a positive control.
    from solar_coarse_source_cycle import static_optimum
    opt=static_optimum(d,c,S.Rational(1,100),2,S.Integer(1));e=opt['eps'];amp=S.sqrt(opt['efficiency']/c['load'])
    assert amp.is_Rational
    r=inverse_in_phase(d,c,amp,S.Rational(1,100),2);assert r['status']=='INHABITED_IN_PHASE_FIBRE'
    print('COARSE_MATERIAL_INVERSE_PASS',e,amp,len(r['witnesses']))
if __name__=='__main__':run()

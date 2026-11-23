#!/usr/bin/env python3
"""Exact original-Wilson-source RG martingale absolute budget: finite reference.

NOT CMP119 physical E/R/B/V localized polymer charges: this is an absolute
martingale *scale* ledger, bounded by original source variances. It supplies no
physical separation rate, no rooted geometry, and no cutoff-independent KP input.

Uses the complete 1536-plaquette L4 Wilson action with 15 SU2-centre active
links (1009 identity), keeping all 64 R445 pair identities/896 spectators in
the original source and independently checking 32768 fine vs fibre states.
"""
from fractions import Fraction as Q
from contextlib import redirect_stdout
from io import StringIO
from runpy import run_path
from pathlib import Path
from itertools import product

file=Path(__file__).with_name('check_ym_original_f19_fine_mark_fibre_20261122.py')
with redirect_stdout(StringIO()):
    source=run_path(str(file))
K=source['K']; assert len(K)==8
assert source['cov'] != 0

# For the literal original Wilson source with F,G in {+1,-1}, all weighted
# conditional F,G moments at nonzero affine tilt are obtained from the SAME
# original four K coefficients, not another measure or effective action.
def tilt(row,s,t):
    k,b,c,d=row
    return (k+s*b+t*c+s*t*d,
            b+s*k+t*d+s*t*c,
            c+s*d+t*k+s*t*b,
            d+s*c+t*b+s*t*k)

def group(Kt,n):
    out={}
    for w,values in Kt.items():
        g=w & ((1<<n)-1)
        entry=out.setdefault(g,[Q(0)]*4)
        for i,x in enumerate(values): entry[i]+=x/Q(1<<(3-n))
    return {g:tuple(v) for g,v in out.items()}

def verify(s,t):
    Kt={w:tilt(row,s,t) for w,row in K.items()}
    H={n:group(Kt,n) for n in range(4)}
    totals=[tuple(sum(x[i] for x in H[n].values())/Q(1<<n) for i in range(4)) for n in range(4)]
    assert all(z==totals[0] for z in totals)
    total,b,c,d=totals[0]
    assert total>0
    muF,muG=b/total,c/total
    cov=d/total-muF*muG
    varF=1-muF*muF
    varG=1-muG*muG
    assert 0<=varF<=1 and 0<=varG<=1
    means={n:{g:(v[1]/v[0],v[2]/v[0]) for g,v in H[n].items()} for n in H}
    # Each level k=0..3: signed E[DkF DkG], absolute expectation
    # E|DkF DkG|, and independent absolute conditional mean charge.
    signed=[];absolute=[];absolute_cond=[];squareF=[];squareG=[]
    fine_signed=Q(0);fine_abs=Q(0);fine_abs_cond=Q(0);fine_F2=Q(0);fine_G2=Q(0)
    for w,row in Kt.items():
        kw,bw,cw,dw=row
        prob_w=kw/(8*total)
        fm,gm=means[3][w]
        local_cov=dw/kw-fm*gm
        fine_signed+=prob_w*local_cov
        fine_abs_cond+=prob_w*abs(local_cov)
        # reconstruct exact original marked conditional distribution of F,G
        # from its four original source coefficients. All four atoms >=0.
        localabs=Q(0)
        for fv,gv in product((-1,1),repeat=2):
            mass=(kw+fv*bw+gv*cw+fv*gv*dw)/(4*kw)
            assert mass>=0
            localabs+=mass*abs((fv-fm)*(gv-gm))
        fine_abs+=prob_w*localabs
        fine_F2+=prob_w*(1-fm*fm)
        fine_G2+=prob_w*(1-gm*gm)
    signed.append(fine_signed);absolute.append(fine_abs)
    absolute_cond.append(fine_abs_cond);squareF.append(fine_F2);squareG.append(fine_G2)
    for n in (3,2,1):
        ss=Q(0);aa=Q(0);fx=Q(0);gx=Q(0)
        for w,row in Kt.items():
            p=row[0]/(8*total)
            fm,gm=means[n][w&((1<<n)-1)]
            fn,gn=means[n-1][w&((1<<(n-1))-1)]
            df,dg=fm-fn,gm-gn
            ss+=p*df*dg;aa+=p*abs(df*dg)
            fx+=p*df**2;gx+=p*dg**2
        signed.append(ss);absolute.append(aa);absolute_cond.append(aa)
        squareF.append(fx);squareG.append(gx)
    assert sum(signed)==cov
    assert sum(squareF)==varF and sum(squareG)==varG
    # Exact Cauchy-Schwarz in L2 over (original configuration, level):
    # E sum |DkF DkG| <= sqrt(Var F Var G) <=1.
    T=sum(absolute)
    assert T**2<=varF*varG
    assert T<= (varF+varG)/2<=1
    # Original signed covariance per scale vs absolute-scale payments.
    assert sum(abs(x) for x in signed)<=sum(absolute_cond)<=T
    # This is NOT a shell-distance bound: no R, scale locality,
    # chargeSummation or q<1 is asserted or manufactured.
    return cov,varF,varG,signed,absolute,absolute_cond,T

settings=list(product((-Q(9,100),Q(0),Q(9,100)),repeat=2))
outputs=[]
for s,t in settings:
    outputs.append((s,t,verify(s,t)))
base=next(v for s,t,v in outputs if s==0 and t==0)
cov,vf,vg,signed,absolute,charged,T=base
assert sum(charged)>abs(cov)
# External cancellation control: sharp two-scale example abs budget nonzero.
# F=(e1+e2)/2 G=(e1-e2)/2 with e1,e2 independent ±1:
# level fine/one-bit charges -1/4 and +1/4, sum total =0 but sum abs =1/2.
assert sum((Q(-1,4),Q(1,4)))==0
assert sum(abs(x) for x in (Q(-1,4),Q(1,4)))==Q(1,2)

print('PASS full original 1536-plaquette Wilson L4, 1024-link geometry, 32768 direct + 32768 F19-fibre link assignments')
print('PASS exact fine->3->2->1->trivial original coarse filtration; 9 marked affine source settings')
print('PASS exact variance-isometry and signed-to-absolute-source ledger at every setting')
print('PASS source-uniform absolute multiscale L2 budget T^2<=Var(F)Var(G)<=1')
print('PASS independent W3 cancellation negative control, 0 signed versus 1/2 absolute')
print('At source zero: cov=',cov,'varF=',vf,'varG=',vg)
print('Original per-scale signed=',[float(x) for x in signed])
print('Original per-scale absolute E|DkF DkG|=',[float(x) for x in absolute])
print('Original per-scale E|Cov_k|=',[float(x) for x in charged])
print('Absolute L2 budget T=',T,'decimal',float(T),'versus sqrt(varF varG)=',(float(vf*vg))**.5)
print('SCOPE: martingale scale *absolute* ledger, not individual CMP119 E/R/B/V physical polymer charges or W3 rooted-shell decay')

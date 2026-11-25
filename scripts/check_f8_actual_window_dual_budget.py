"""Conditional actual-window dual residual majorants; no normal/time error bound.
All majorant arithmetic rational except interval quadrature of derivative L1.
Uses original source energy bound and contour envelope, no receiver fitting.
"""
from fractions import Fraction as Q
from math import factorial, comb
import json
import sympy as s
import mpmath as mp

# Normalized T jets, with L1 norm in T for the single window factor.
# Analytic coefficient sup jets use the complex T disk radius 1/4.
D=20
RATE=4; BETA=Q(17,16); V=Q(1,3); VB=Q(1,2); BI=16; W=42; SB=3
zero=[Q(0)]*(D+1)
def add(a,b):return [x+y for x,y in zip(a,b)]
def mul(a,b):return [sum(a[i]*b[j-i] for i in range(j+1)) for j in range(D+1)]
def scale(a,c):return [x*c for x in a]
def deriv(a):return [(j+1)*a[j+1] for j in range(D)]+[Q(0)]
def jet(M):return [Q(M)*RATE**j for j in range(D+1)]
def padd(a,b):return [add(a[i] if i<len(a) else zero,b[i] if i<len(b) else zero) for i in range(max(len(a),len(b)))]
def pmul(a,b):return [mul(x,b) for x in a]
def pdz(a):return padd([scale(a[i],i) for i in range(1,len(a))],pmul(a,jet(BETA)))
def pdt(a):return padd([deriv(x) for x in a],[zero]+pmul(a,deriv(jet(BETA))))
def A(a):return padd(pmul(pdt(pdz(a)),jet(2*V)),pmul(pdz(a),add(deriv(jet(V)),jet(3*BI))))
def B(a):return pdt(pdt(a))
def warp(a,l):return [zero]*l+pmul(pdz(a),jet(3*BI**(l+1)))
def solve(rhs,flux):
    # Absolute descending-coefficient bound for s(p''-2 beta p')=rhs.
    p=[zero for _ in range(len(rhs)+2)]
    for i in reversed(range(len(rhs))):
        p[i+1]=add(scale(mul(p[i+2],jet(BETA)),Q(i+2,2)),scale(mul(rhs[i],jet(BETA)),Q(1,2*(i+1))))
    p[0]=mul(add(p[1],flux),jet(BETA))
    return p[:-1]
def norm(a):return W*sum(x[0]*factorial(i) for i,x in enumerate(a))

def window_jets():
    # Total variation: integrate |f^(j)| by evaluating f^(j-1) at exact
    # polynomial turning-point intervals. No interval-Horner cancellation
    # across broad cells; repeated roots are harmless extra split points.
    z=s.symbols('z');P=s.Integer(1);odd=0;mp.iv.dps=50;iv=mp.iv;mp.mp.dps=75
    out=[Q(1)];counts=[]
    def rational(v):return iv.mpf(int(v.p))/int(v.q)
    for j in range(1,D+1):
        prev,parity=P,odd
        P=s.expand(P+2*(z*z-z)*(s.diff(P,z)-P) if odd else 2*z*z*(s.diff(P,z)-P));odd=1-odd
        roots=s.Poly(P,z).intervals(eps=s.Rational(1,10**32),inf=1)
        vals=[iv.mpf(0) if parity else iv.mpf(int(prev.subs(z,1)))];count=0
        for (a,b),mult in roots:
            if b<=1:continue
            a=max(a,s.S.One);l=rational(a);h=rational(b);v=iv.mpf([l.a,h.b]);poly=iv.mpf(0)
            for c in s.Poly(prev,z).all_coeffs():poly=poly*v+int(c)
            vals.append(poly*iv.exp(1-v)*(iv.sqrt(1-1/v) if parity else 1));count+=1
        vals.append(iv.mpf(0));total=sum(abs(b-a) for a,b in zip(vals,vals[1:]));counts.append(count)
        # Round upward with an extra unit after extracting interval endpoint.
        # ||chi^(j)||_1 <=3*10^j * integral positive half.
        out.append(Q((int(mp.ceil(mp.mpf(total.b._mpi_[1])))+1)*3*10**j,factorial(j)))
    return out,counts

def residual(q,m,K):
    # p0=-beta q; flux recurrence -v dt p_j(0).
    p=[[mul(q,jet(BETA))]]
    for j in range(m):
        rhs=A(p[j]);rhs=padd(rhs,B(p[j-1])) if j else rhs
        for l in range(1,j+1):rhs=padd(rhs,warp(p[j-l],l))
        p.append(solve(rhs,mul(deriv(p[j][0]),jet(V))))
    # Residual after exact cancellation through k^-(m-1), factored k^-m.
    r=norm(A(p[m]))+norm(B(p[m]))/K
    if m:r+=norm(B(p[m-1]))
    for j in range(m+1):
        l=max(1,m-j);r+=norm(warp(p[j],l))/K**(j+l-m)
    # Final correction p_c = -v/s * dt p_m(0) Z. D(p_c)=-2s beta p_c'.
    c=[zero,mul(deriv(p[m][0]),jet(VB))];r+=norm(pmul([c[1]],jet(SB)))
    r+=norm(A(c))/K+norm(B(c))/K**2+norm(warp(c,1))/K**2
    return r

def tail(N,m,C):
    # N=j²; k>=n, k<=4n/3, use contour |c_n|<=4 eps^6 exp(-sqrt(n)/5).
    j=int(N**.5);assert j*j==N and j>=60
    p=5-m;factor=Q(4,3)**max(p,0);v=Q(j,5);term=Q(1);den=term
    for l in range(1,2*int(v)+2):term*=v/l;den+=term
    if p>=0:
        d=2*p+1;integ=2*sum(Q(factorial(d),factorial(i))*Q(j)**i*5**(d+1-i) for i in range(d+1))/den
    else:integ=2*Q(N)**p*(5*j+25)/den
    return C*4*Q(1,25)**6*factor*integ

def check():
    global RATE,BETA,V,VB,BI,W,SB
    RATE=4; BETA=Q(17,16); V=Q(1,3); VB=Q(1,2); BI=16; W=42; SB=3
    # Exact disk proof constants: b0 in [1/12,1/8]; Picard ball |b|<=1/4.
    # |b'|<=1/sqrt(15)*1/1? <=1/3, derivative <= (16/15)^(3/2)< 2.
    assert Q(1,8)+Q(1,4)*Q(1,3)<Q(1,4)
    assert Q(16,15)**3<4 and Q(1,4)*2<1
    # Relative bound |b/b0|>=exp(- (17/16)/4)>3/4 (use e^x <=1/(1-x)).
    # weaker lower bound 1-17/64=47/64 gives |b|>1/17, not 1/16.
    # Sharper e^(17/64)<4/3 via series plus geometric remainder.
    x=Q(17,64);a=sum(x**j/factorial(j) for j in range(8));assert a+x**8/factorial(8)/(1-x/9)<Q(4,3)
    assert Q(16,15)<Q(17,16)**2
    # beta <=17/16 and inverse beta <=17/16; |v|<=1/3, |v/s|<=1/2.
    assert Q(1,4)*Q(17,16)<Q(1,3)
    # a2,a1,a0 multipliers (complex disk) <= 1/16, 1/8, 1/32.
    assert Q(1,2)*Q(1,16)*Q(17,16)**2<Q(1,16)
    assert Q(1,2)*Q(1,16)*(Q(1,16)*Q(17,16)+2*Q(17,16))<Q(1,8)
    # Window starts after t=8: F(12)-F(8)>=log(12/8)>1/4.
    assert Q(1,3)>Q(1,4) # log(3/2)>= (1/2)/(3/2).
    ch,counts=window_jets();a2=mul(ch,jet(Q(1,16)));a1=mul(ch,jet(Q(1,8)));a0=mul(ch,jet(Q(1,32)))
    qP=mul(add(deriv(deriv(a2)),deriv(a1)),jet(Q(1,64)));q0=mul(a0,jet(Q(1,64)))
    rows=[];receiver=[]
    for m in range(9):
        # Highest required derivative m+2+2 <= 20, each operation loses one jet.
        K=1000;CP=residual(qP,m,K);C0=residual(q0,m,K)
        # Original energy bound: ||U||_w <= 491400 |c|/sqrt(k).
        receiver.append((CP,C0));C=Q(491400)*(C0+CP/K**2)
        lo,hi=60,60
        while tail(hi*hi,m,C)>=Q(1,10**9):hi*=2
        while hi-lo>1:
            mid=(lo+hi)//2
            if tail(mid*mid,m,C)<Q(1,10**9):hi=mid
            else:lo=mid
        rows.append(dict(order=m,dual_p=float(CP),dual_a0=float(C0),C=float(C),N=hi*hi,upper=float(tail(hi*hi,m,C)),bound4096=float(tail(4096,m,C))))
    # Source-side lift on whole half-line, original source supported t in [1,2].
    # Picard ball |b-b_real|<=1/4, time disk 1/8, Re(1+b²)>=1.
    assert Q(1,8)*Q(5,4)<Q(1,4) and Q(1,8)<1
    assert 1+Q(5,4)**2<4
    RATE=8; BETA=Q(2); V=Q(5,4); VB=Q(5,2); BI=4; W=3; SB=2
    # Unnormalized source bump, physical pulse width .065. chi bounds
    # converted from original normalized observation width .1.
    src=[Q(13,200)]+[x*Q(13,600)*Q(40,13)**j for j,x in enumerate(ch) if j]
    amp=mul(src,jet(24))
    source=[residual(amp,m,1000) for m in range(9)]
    # L1-in-time residual controls terminal energy since source lift is flat
    # at both pulse ends; the half-line lift decays and needs no upper SAT.
    # ||U||_w <= 1200*Cs |c_n| k^(-ms-3/2) after pulse.
    # receiver residual C_r k^(-mr-1/2), Bessel/curvature k^6 -> k^(4-ms-mr).
    combined=[]
    for ms,Cs in enumerate(source):
        for mr,(CP,C0) in enumerate(receiver):
            C=1200*Cs*(C0+CP/1000**2);order=ms+mr+1
            lo,hi=60,60
            while tail(hi*hi,order,C)>=Q(1,10**9):hi*=2
            while hi-lo>1:
                mid=(lo+hi)//2
                if tail(mid*mid,order,C)<Q(1,10**9):hi=mid
                else:lo=mid
            combined.append(dict(source_order=ms,receiver_order=mr,N=hi*hi,upper=float(tail(hi*hi,order,C)),C=float(C)))
    combined.sort(key=lambda r:r['N'])
    return dict(source_dual_constants=[float(x) for x in source],combined=combined,scope='conditional original continuous E4/SMS fixed-window tails, not normal/time numerical error',turning_point_counts=counts,window_derivative_L1=[float(x*factorial(i)) for i,x in enumerate(ch)],rows=rows)
if __name__=='__main__':print(json.dumps(check(),indent=2))

#!/usr/bin/env python3
"""Original physical R231/R236: transverse Leray output, active deep-FL,
complete zero-work spectators and exact cutoff non-invariance.
Mathematical finite-source certificate, NOT NSE regularity/Agda kernel.
"""
from collections import Counter,defaultdict
from sympy import Matrix,I,Rational as Q,sqrt,symbols,solve,simplify,re,im,expand,sign
T,B=symbols('t beta',real=True)
K=(16,0,0)
PAIRS=[((0,12,0),(16,-12,0)),((16,12,0),(0,-12,0)),
       ((8,6,0),(8,-6,0)),((8,15,0),(8,-15,0)),
       ((1,1,0),(15,-1,0))]
def helical(p):
    x,y,_=p;d=sqrt(x*x+y*y);e=Matrix([x/d,y/d,0]);v=Matrix([-y/d,x/d,0]);z=Matrix([0,0,1]);hp=v+I*z;hm=v-I*z
    assert simplify(I*e.cross(hp)-hp)==Matrix([0,0,0])
    assert simplify(I*e.cross(hm)+hm)==Matrix([0,0,0])
    assert simplify(e.dot(hp))==simplify(e.dot(hm))==0
    return hp,hm
def normrate(p,q):return sum(v*v for v in p)+sum(v*v for v in q)
def shell(p):
    m=max(map(abs,p));return 0 if m<=1 else (m-1).bit_length()
def tag(p,q):
    a,b,k=map(shell,(p,q,K))
    if a+3<b:return 'FL' if 3*a<=2*b else 'CC'
    if b+3<a:return 'FL' if 3*b<=2*a else 'CC'
    if k+3<a and k+3<b:return 'HH' if 5*k<=4*max(a,b) else 'CC'
    return 'CC'
def fibre(C):
    for x in range(16-C,C+1):
        for y in range(-C,C+1):
            for z in range(-C,C+1):
                p=(x,y,z);q=(16-x,-y,-z)
                yield (p,q,normrate(p,q),tag(p,q))
def stats(C):
    n=(2*C-15)*(2*C+1)**2
    mu=Q(128)+Q(2,3)*(C-8)*(C-7)+Q(4,3)*C*(C+1)
    return n,mu
def run():
    a,b,c=symbols('a b c',real=True)
    A=[simplify(helical(p)[0].cross(helical(q)[1])) for p,q in PAIRS]
    rates=[normrate(p,q) for p,q in PAIRS]
    assert rates==[544,544,200,578,228]
    coeff=[a,b,T,c,B]
    M=sum((v*w for v,w in zip(A,coeff)),Matrix([0,0,0]))
    sol=solve([im(M[0]),im(M[1]),re(M[2])-1],[a,b,c])
    w=[simplify(2*re(Ai[2])*bi.subs(sol)) for Ai,bi in zip(A,coeff)]
    M=simplify(M.subs(sol))
    assert M==Matrix([0,0,1]) # P_k M=M, nonzero transverse field!
    assert simplify(sum(w)-2)==0
    assert simplify(w[4]+16*sqrt(113)*B/113)==0 # deep-FL active
    plus={p for p,q in PAIRS};minus={q for p,q in PAIRS}
    plus|={tuple(-x for x in p) for p in tuple(plus)}
    minus|={tuple(-x for x in q) for q in tuple(minus)}
    assert {(p,q) for p in plus for q in minus if tuple(p[i]+q[i] for i in range(3))==K}==set(PAIRS)
    assert [tag(p,q) for p,q in PAIRS]==['CC']*4+['FL']
    V=simplify(expand(sum(ri*wi for ri,wi in zip(rates,w))))
    N,mu=stats(16);N2,mu2=stats(24)
    S=simplify(expand(N*(2*mu-V)))
    S2=simplify(expand(N2*(2*mu2-V)))
    expect=Q(9244158)-Q(456752736,25)*T-B*(Q(70812225,113)*sqrt(226)+4720815*sqrt(2)+Q(18068688,113)*sqrt(113))
    assert simplify(S-expect)==0
    assert simplify(S2/N2-S/N-2*(mu2-mu))==0
    assert sign(S.subs({T:0,B:1}))==-1
    assert sign(S2.subs({T:0,B:1}))==1
    assert sign(S.subs({T:-10,B:1}))==1
    assert sign(S.subs({T:10,B:1}))==-1
    for C in (16,24):
        actual=Counter();R=0
        for p,q,r,region in fibre(C):actual[region]+=1;R+=r
        nn,avg=stats(C)
        assert sum(actual.values())==nn and R==nn*avg
        print('cutoff',C,'all incidences',nn,'R',R,'regions',dict(actual))
    # Six original R236 pair blocks: independent full spectator-pair fold.
    rows=list(fibre(16));live={ (p,q):i for i,(p,q) in enumerate(PAIRS)}
    groups=['FL','HH','CC'];count=Counter();R=Counter();W=defaultdict(lambda:0);Vg=defaultdict(lambda:0)
    for p,q,r,g in rows:count[g]+=1;R[g]+=r
    for (p,q),ri,wi in zip(PAIRS,rates,w):g=tag(p,q);W[g]+=wi;Vg[g]+=ri*wi
    blocks={}
    for i,g in enumerate(groups):
        for h in groups[i:]:
            blocks[g,h]=(R[g]*W[g]-count[g]*Vg[g] if g==h else
                R[g]*W[h]+R[h]*W[g]-count[h]*Vg[g]-count[g]*Vg[h])
    sums=Counter()
    for p,q,r,g in rows:
        if (p,q) in live:continue
        for i,((pa,qa),ra) in enumerate(zip(PAIRS,rates)):
            h=tag(pa,qa);key=tuple(sorted((g,h),key=groups.index));sums[key,i]+=ra-r
    direct=defaultdict(lambda:0)
    for (key,i),amount in sums.items():direct[key]-=amount*w[i]
    for i in range(5):
        for j in range(i+1,5):
            k=tuple(sorted((tag(*PAIRS[i]),tag(*PAIRS[j])),key=groups.index))
            direct[k]-=(rates[i]-rates[j])*(w[i]-w[j])
    assert all(simplify(blocks[k]-direct[k])==0 for k in blocks)
    assert simplify(sum(blocks.values())-S)==0
    C=symbols('C',integer=True,positive=True);nn,avg=stats(C)
    assert expand(nn*(2*avg-V)).coeff(C,5)==32
    assert simplify(V-(mu*2-S/N))==0
    print('same field t=0,beta=1: S16=',S.subs({T:0,B:1}), 'S24=',S2.subs({T:0,B:1}))
    print('PASS exact source helical/Leray/reality, deep-FL live, six blocks, spectator-cutoff sign flip, BIDI work recovery, 32*C^5 growth')
    print('OPEN: actual NSE time estimate, uniformly compensated physical quantity, Agda kernel')
if __name__=='__main__':run()

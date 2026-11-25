from itertools import product
from collections import Counter
from fractions import Fraction
from random import Random
from math import prod
from sympy import Poly, symbols, cyclotomic_poly
import numpy as np

# Green character of GL4(F3): original rectified residue character exponent 16+40=56.
q=3; n=4; X=symbols('X'); I=(1,0,0,0); Z=(0,0,0,0)
F=list(product(range(3),repeat=4))
def fm(a,b):
    c=[0]*7
    for i,j in product(range(4),repeat=2):c[i+j]+=a[i]*b[j]
    for i in range(6,3,-1):c[i-3]-=c[i];c[i-4]-=2*c[i]
    return tuple(v%3 for v in c[:4])
def fp(a,k):
    z=I
    while k:
        if k&1:z=fm(z,a)
        a=fm(a,a);k//=2
    return z
g=next(a for a in F if a!=Z and fp(a,40)!=I and fp(a,16)!=I)
powers=[fp(g,i) for i in range(80)];assert len(set(powers))==80
# use Q(zeta_10) for rectified char, and Q(zeta_30) for Bessel.
P=Poly(cyclotomic_poly(30,X),X)
def ev(c):return Poly(sum(v*X**(k%30) for k,v in c.items()),X)%P
def cpadd(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def fpoly(orbit):
    p=[I]
    for a in orbit:
        z=[Z]*(len(p)+1)
        for j,b in enumerate(p):
            z[j]=cpadd(z[j],tuple(-t%3 for t in fm(a,b)));z[j+1]=cpadd(z[j+1],b)
        p=z
    assert all(t[1:]==(0,0,0) for t in p)
    return tuple(t[0] for t in p)
def parts(n,m=None):
    if n==0:yield ();return
    for a in range(min(n,m or n),1-1,-1):
        for p in parts(n-a,a):yield (a,)+p
orbits=[];seen=set()
for j in range(80):
    if j in seen:continue
    o=tuple(sorted({j*3**i%80 for i in range(4)}));seen.update(o);orbits.append(o)
assert Counter(map(len,orbits))=={1:2,2:3,4:18}
classes=[];primary={}
for o in orbits:
    d=len(o); f=fpoly([powers[j] for j in o]); pp=Poly(sum(v*X**i for i,v in enumerate(f)),X,modulus=3)**(4//d)
    key=tuple(int(pp.nth(i))%3 for i in range(5));primary[key]=(o,f)
    for l in parts(4//d):
        cen=Fraction(3**(d*sum(sum(a>=i for a in l)**2 for i in range(1,max(l)+1))))
        for m in Counter(l).values():
            for i in range(1,m+1):cen*=1-Fraction(1,3**(d*i))
        assert cen.denominator==1
        classes.append((o,l,int(cen)))
def green(o,r,e=56):
    assert e%8==0 # chosen exponent has order 10; all test chars below multiples of 8
    z=-prod(1-3**(len(o)*i) for i in range(1,r))
    c=Counter()
    for j in o:c[(e*j//8*3)%30]+=z
    return c
# e=56 -> zeta10^7, NOT order 10? 56/8=7, yes. But 16+40=56, gcd(56,80)=8.
# character orbit (56,8,24,72); comparison exponent 8 is same orbit;
# use exponent 16 (unrectified), distinct orbit.
checks=Counter()
for e in (56,16):
    for f in (56,16):
        c=Poly(0,X)
        for o,l,cen in classes:
            a=ev(green(o,len(l),e));b=ev(Counter({-k:v for k,v in green(o,len(l),f).items()}))
            c+=Poly(a.as_expr()*b.as_expr()/cen,X)
        assert (c%P).as_expr()==int(e==f);checks['green_inner_products']+=1
assert ev(green((0,),4))==Poly(416,X)
# Actual finite matrix evaluation by characteristic polynomial, primary kernel rank.
def rank(a):
    a=np.array(a,dtype=np.int64).copy()%3;r=0
    for j in range(a.shape[1]):
        k=next((i for i in range(r,len(a)) if a[i,j]),None)
        if k is None:continue
        a[[r,k]]=a[[k,r]];a[r]=a[r]*int(a[r,j])%3
        for i in range(len(a)):
            if i!=r:a[i]=(a[i]-a[i,j]*a[r])%3
        r+=1
        if r==len(a):break
    return r
def det(a):
    if len(a)==1:return int(a[0,0])%3
    return sum((-1)**i*int(a[0,i])*det(np.delete(np.delete(a,0,axis=0),i,axis=1)) for i in range(len(a)))%3
from itertools import combinations
minors=[list(combinations(range(4),i)) for i in range(1,5)]
I4=np.eye(4,dtype=np.int64)
def char(a):
    co=[0]*5;co[4]=1
    for i,ms in enumerate(minors,1):co[4-i]=(-1)**i*sum(det(a[np.ix_(s,s)]) for s in ms)%3
    if tuple(co) not in primary:return Counter()
    o,f=primary[tuple(co)];v=np.zeros((4,4),dtype=np.int64)
    for c in reversed(f):v=(v@a+c*I4)%3
    r=(4-rank(v))//len(o)
    return green(o,r)
U=[]
for a in product(range(3),repeat=6):
    u=I4.copy()
    for (i,j),v in zip(combinations(range(4),2),a):u[i,j]=v
    U.append((u,int(u[0,1]+u[1,2]+u[2,3])%3))
# Evaluate identity and all degeneracies of the Whittaker character using unipotent rank.
for signs in product(range(3),repeat=3):
    c=Counter()
    for u,_ in U:
        r=4-rank(u-I4);phase=sum(s*int(u[i,i+1]) for i,s in enumerate(signs))%3
        for k,v in green((0,),r).items():c[k-10*phase]+=v
    assert ev(c)==Poly(729*int(all(signs)),X);checks['whittaker_multiplicities']+=1
# Exact finite Bessel samples (normalization by 729).
def bessel(a):
    c=Counter()
    for u,p in U:
        for k,v in char(a@u%3).items():c[k-10*p]+=v
    return Poly(ev(c).as_expr()/729,X,domain='QQ')
swap=I4[::-1].copy()
D=I4.copy();D[0,0]=2
B=bessel(swap);assert not B.is_zero;assert bessel(I4).as_expr()==1;assert bessel(D).as_expr()==0
assert bessel(2*I4).as_expr()==1
# B(ugv)=psi(u)psi(v)B(g) on actual nonmirabolic sample (may vanish).
u=I4.copy();u[2,3]=1
assert (bessel(u@swap%3)-Poly(X**10*B.as_expr(),X)%P).is_zero
assert (bessel(swap@u%3)-Poly(X**10*B.as_expr(),X)%P).is_zero
checks['bessel_samples']=6
print('green classes',len(classes),'B(swap)',B.as_expr(),dict(checks),flush=True)

# Cut-target source contraction. Bundle original pair coordinates; keep old/new
# mask, tag and two length bits apart from affine compatibility syndrome.
def add(a,b):return tuple((x+y)%3 for x,y in zip(a,b))
def sub(a,b):return tuple((x-y)%3 for x,y in zip(a,b))
def basis(cols):
    B={}
    for a in cols:
        z=list(a)
        for i,b in sorted(B.items()):z=[(x-z[i]*y)%3 for x,y in zip(z,b)]
        if any(z):
            i=next(i for i,x in enumerate(z) if x);B[i]=tuple(x*z[i]%3 for x in z)
    return B
def contains(B,a):
    z=list(a)
    for i,b in sorted(B.items()):z=[(x-z[i]*y)%3 for x,y in zip(z,b)]
    return not any(z)
def tree(order):
    if len(order)==1:return order[0]
    h=len(order)//2;return tree(order[:h]),tree(order[h:])
def solve(n,A,B,target,clauses,w,v,order,diagonal=False,mod=None):
    ds=[(a,a) for a in (0,1)] if diagonal else list(product(range(2),repeat=2));allv=set(range(n));zero=(0,)*len(target);stats=Counter()
    def cv(i,d):return add(tuple(d[0]*x%3 for x in A[i]),tuple(d[1]*x%3 for x in B[i]))
    cols=[[cv(i,d) for d in ds] for i in range(n)]
    def node(t):
        if isinstance(t,int):U={t};kids=None
        else:
            l=node(t[0]);r=node(t[1]);U=l[0]|r[0];kids=(l,r)
        O=allv-U;bd=tuple(sorted({i for sc,bits,side in clauses if set(sc)&O for i in sc if i in U}));J=U-set(bd)
        P=basis(c for i in J for c in cols[i]);Q=basis(c for i in O for c in cols[i]);lam=len(P)+len(Q)-len(basis([*P.values(),*Q.values()]));stats['max_overlap']=max(stats['max_overlap'],lam)
        T={}
        def save(a,s,tag,k,l,mask,count,wit):
            if not contains(Q,sub(target,s)):return
            key=(tuple(a[i] for i in bd),s,tag,k,l,mask);old,ww=T.get(key,(0,wit));T[key]=((old+count) if mod is None else (old+count)%mod,ww)
        def filt(a,mask,fs):
            for sc,bits,side in fs:
                if not any(a[i][side//2]==b for i,b in zip(sc,bits)):mask&=~(1<<side)
            return mask
        if kids is None:
            i=t;fs=[c for c in clauses if set(c[0])<=U]
            for d in ds:
                a={i:d};m=filt(a,15,fs);save(a,cv(i,d),(w[i]*d[0]-v[i]*d[1])%3,d[0] if i==0 else 0,d[1] if i==0 else 0,m,1,a)
        else:
            (UL,BL,TL),(UR,BR,TR)=kids;fs=[c for c in clauses if set(c[0])<=U and not set(c[0])<=UL and not set(c[0])<=UR]
            for (al,sl,tl,kl,ll,ml),(cl,wl) in TL.items():
                for (ar,sr,tr,kr,lr,mr),(cr,wr) in TR.items():
                    stats['joins']+=1;a=dict(zip(BL,al));a.update(zip(BR,ar));m=filt(a,ml&mr,fs)
                    save(a,add(sl,sr),(tl+tr)%3,kl+kr,ll+lr,m,cl*cr,wl|wr)
        assert len(T)<=len(ds)**len(bd)*3**lam*3*4*16;stats['bounds']+=1;stats['entries']+=len(T);stats['peak']=max(stats['peak'],len(T))
        return U,bd,T
    _,_,T=node(tree(order));out=Counter();back={}
    for (_,s,t,k,l,m),(c,wit) in T.items():
        assert s==target
        st=int(m&5==5)+2*int(m&10==10)
        if not st:continue
        key=(t,k+1,l+1,st);out[key]+=c
        if mod is not None:out[key]%=mod
        back[key]=wit
    return out,back,stats
rng=Random(291);tot=Counter();peak=0
for n in range(1,6):
    for trial in range(10):
        d=trial%5;A=[tuple(rng.randrange(3) for _ in range(d)) for i in range(n)];B=[tuple(rng.randrange(3) for _ in range(d)) for i in range(n)]
        target=tuple(rng.randrange(3) for _ in range(d));w=[rng.randrange(3) for _ in range(n)];v=[rng.randrange(3) for _ in range(n)];order=list(range(n));rng.shuffle(order)
        C=[]
        for side in range(4):
            for _ in range(rng.randrange(4)):
                sc=tuple(sorted(rng.sample(range(n),rng.randrange(1,min(n,3)+1))));C.append((sc,tuple(rng.randrange(2) for i in sc),side))
        def label(a):
            s=(0,)*d
            for i,(x,y) in enumerate(a):s=add(s,add(tuple(x*z%3 for z in A[i]),tuple(y*z%3 for z in B[i])))
            if s!=target:return None
            m=15
            for sc,bs,side in C:
                if not any(a[i][side//2]==b for i,b in zip(sc,bs)):m&=~(1<<side)
            st=int(m&5==5)+2*int(m&10==10)
            if not st:return None
            return (sum(w[i]*x-v[i]*y for i,(x,y) in enumerate(a))%3,a[0][0]+1,a[0][1]+1,st)
        for diag in (False,True):
            ref=Counter(k for a in product(*([[(0,0),(1,1)] if diag else list(product(range(2),repeat=2))]*n)) if (k:=label(a)) is not None)
            out,back,st=solve(n,A,B,target,C,w,v,order,diag);assert out==ref;tot['packet_checks']+=1
            for k,a in back.items():assert label([a[i] for i in range(n)])==k;tot['witnesses']+=1
            for mod in (1,3,9):
                low,lb,ss=solve(n,A,B,target,C,w,v,order,diag,mod);assert set(low)==set(ref)==set(lb) and all(low[k]==ref[k]%mod for k in ref);tot['precision_checks']+=1;tot['bounds']+=ss['bounds']
            tot['bounds']+=st['bounds'];tot['joins']+=st['joins'];peak=max(peak,st['peak'])
for n in (16,32,64):
    A=[tuple(int(i==j) for j in range(n)) for i in range(n)];B=[tuple(-z%3 for z in a) for a in A]
    out,back,st=solve(n,A,B,(0,)*n,[],[0]*n,[0]*n,list(range(n)));assert sum(out.values())==2**n and st['max_overlap']==0
    print('large',n,sum(out.values()),dict(st),flush=True)
print('cut',dict(tot),'peak',peak,flush=True)

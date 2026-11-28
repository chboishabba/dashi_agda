"""R341: original rank-eight congruence image, scalar gate, exact lift witnesses."""
from itertools import product, permutations
from random import Random
from collections import Counter
import sympy as s
import numpy as np
from fractions import Fraction
from math import prod

N=8; pairs=list(product(range(N),repeat=2)); I=np.eye(8,dtype=object)
def v3(x):
    x=s.Rational(x)
    if not x:return 10**6
    a,b=abs(int(x.p)),int(x.q); n=0
    while a%3==0:a//=3;n+=1
    while b%3==0:b//=3;n-=1
    return n

def val(x):
    if not x:return 10**6
    n=0
    while x%3==0:x//=3;n+=1
    return n

def residue(x,m):
    x=s.Rational(x);return int(x.p)*pow(int(x.q),-1,m)%m

def mat(a):return s.Matrix(np.asarray(a).reshape(8,8).tolist())
B=s.Matrix([[6,21],[-7,-15]])/9; beta=s.diag(B,B,B,B)
P=s.Matrix([[0,-3],[1,3]]); X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0]); q=s.diag(*[B**i*X*s.diag(s.Integer(3)**(7-2*i),s.Integer(3)**(6-2*i)) for i in range(4)])
# Interleaved original (1,pi) pairs. O_B+3A block lattice, index 27.
blocks=[s.eye(2),P,s.Matrix([[3,0],[0,0]]),s.Matrix([[0,9],[0,0]])]
assert abs(s.Matrix.hstack(*[s.Matrix(list(z)) for z in blocks]).det())==27
basis=[]
for i,j in product(range(4),repeat=2):
    for z in blocks:
        a=s.zeros(8);a[2*i:2*i+2,2*j:2*j+2]=z;basis.append(a)
A=np.array(s.Matrix.hstack(*[s.Matrix(list(z)) for z in basis])).astype(object)
A=np.vectorize(int,otypes=[object])(A)
# Keep exact integral coefficient lifts mod 3^M; 3^M basis columns implicit.
# Each row l(c)=0 mod 3^h; transform all later forms concurrently.
def cut(C,forms,levels,M,indices=None):
    mod=3**M; C=C.copy()%mod
    R=np.asarray(forms,dtype=object)@C%mod
    for i,h in enumerate(levels):
        if h<=0:continue
        row=R[i]; p=min(range(C.shape[1]),key=lambda j:val(row[j]));v=val(row[p])
        if v>=h:continue
        # After dividing by common valuation, invert the unit modulo the remaining precision.
        if indices is not None:indices.append(h-v)
        m=3**(M-v); inv=pow(int(row[p]//3**v),-1,m)
        coeff=np.array([int(x//3**v)*inv%m for x in row],dtype=object);coeff[p]=0
        R[i:]=(R[i:]-np.outer(R[i:,p].copy(),coeff))%mod
        C=(C-np.outer(C[:,p].copy(),coeff))%mod
        C[:,p]=C[:,p]*3**(h-v)%mod;R[i:,p]=R[i:,p]*3**(h-v)%mod
        assert all(int(x)%3**h==0 for x in R[i])
    assert all(all(int(x)%3**h==0 for x in row) for row,h in zip(np.asarray(forms,dtype=object)@C,levels) if h>0)
    return C

def forms_for(b):
    bi=b.inv(); rows=[]; hs=[]
    for i,j in pairs:
        r=[bi[i,k]*b[l,j] for k,l in pairs]
        h=20 if i==7 else 0
        shift=max(0,-min(map(v3,r)))
        rows.append((r,shift));hs.append(h+shift)
    M=max(3,*hs);mod=3**M
    R=np.array([[residue(x*3**shift,mod) for x in r] for r,shift in rows],dtype=object)
    return R,hs,M

def subcut(C,threshold,M):
    return cut(C,np.eye(64,dtype=object),threshold,M)

def rankbasis(C):
    # Reduced basis of image with *original integral lifts* attached.
    rows={}
    for x in C.T:
        v=np.array([int(x[8*(2*i)+2*j])%3 for i,j in product(range(4),repeat=2)],dtype=object); lift=x.copy()
        for i,(r,w) in sorted(rows.items()):
            a=int(v[i]);v=(v-a*r)%3;lift=lift-a*w
        if any(v):
            i=next(i for i,a in enumerate(v) if a);a=int(v[i]);rows[i]=(v*a%3,lift*a)
    return list(rows.values())

def kmul(a,b):return ((a[0]*b[0]-3*a[1]*b[1])%9,(a[0]*b[1]+a[1]*b[0]+3*a[1]*b[1])%9)
H={(1,0)}
for g in [(8,0),(4,7),(7,0)]:
    p=(1,0);powers=[]
    for _ in range(18):powers.append(p);p=kmul(p,g)
    H={kmul(h,p) for h in H for p in powers}
chi={kmul(h,v):i for i,v in enumerate([(1,0),(1,6),(1,3)]) for h in H}
assert len(H)==18 and len(chi)==54
perms=[(p,(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))) for p in permutations(range(4))]
def kdet(C,D):
    a=b=0
    for p,sgn in perms:
        t=(sgn,0)
        for i,j in enumerate(p):t=kmul(t,(int(C[i,j]),int(D[i,j])))
        a+=t[0];b+=t[1]
    return (a%9,b%9)
def kappa(g):
    g=np.asarray(g,dtype=object)%27
    C=g[::2,::2]%3;D=g[1::2,::2]%3
    k=np.zeros((8,8),dtype=object);k[::2,::2]=C;k[::2,1::2]=-3*D;k[1::2,::2]=D;k[1::2,1::2]=C+3*D
    # Modular inverse via exact adjugate or SymPy inverse, denominator a unit.
    ki=np.array([[residue(x,27) for x in row] for row in s.Matrix(k.tolist()).inv().tolist()],dtype=object)
    Y=(ki@g-I)%27
    assert not any(int(x)%3 for x in Y.flat) and not any(int(x)%9 for x in Y[::2,1::2].flat)
    phase=sum(6*int(Y[2*i,2*i])+21*int(Y[2*i+1,2*i])-7*int(Y[2*i,2*i+1])-15*int(Y[2*i+1,2*i+1]) for i in range(4))
    assert phase%9==0
    return (chi[kdet(C,D)]+phase//9)%3

def actual(b,C):
    R,hs,M=forms_for(b);G=cut(C,R,hs,M)
    return G,M,R,hs

def evaluate(b,full=True):
    C,M,R,hs=actual(b,A);im=rankbasis(C)
    # U_A^2 thresholds, computed directly on exact original increment coordinates.
    rad2=[1+int(i%2==0 and j%2==1) for i,j in pairs]
    S2=subcut(C,rad2,M)
    bad=[]
    for x in S2.T:
        p=s.trace(beta*mat(x))/3
        if v3(p)<0:bad.append((x,p))
    if bad:
        x,p=bad[0]; y=mat(x);z=b.inv()*y*b
        assert all(v3(z[i,j])>=20 if i==7 else v3(z[i,j])>=0 for i,j in pairs)
        assert all(v3(y[i,j])>=rad2[k] for k,(i,j) in enumerate(pairs)) and v3((s.eye(8)+y).det())==0
    # All supplied candidates still compute full J1, even if U_A^2 already rejects.
    S=C.copy(); ledger=[]; phases=[]
    for r in range(1,6):
        m=r//2
        depth=[m+(int(i%2==0 and j%2==1) if r%2==0 else int(not(i%2==1 and j%2==0))) for i,j in pairs]
        S=subcut(S,depth,M)
        # J1 additionally requires C mod3 zero; depth1 implies it already.
        # Skip expensive character evaluation on generators trivial mod27.
        for x in S.T:
            if not any(x%27):continue
            phase=kappa(I+np.asarray(x).reshape(8,8));phases.append(phase)
        ledger.append(sum(1 for x in S.T if any(x%27)))
    # Exact finite image of additive increment lattice, with lifts. Enumerate only small image.
    units=None; ranks=None
    if len(im)<=7:
        units=0; ranks=Counter()
        for coeff in product(range(3),repeat=len(im)):
            vec=sum((a*r for a,(r,w) in zip(coeff,im)),np.zeros(16,dtype=object))%3
            d=(np.eye(4,dtype=object)+vec.reshape(4,4))%3
            if int(s.Matrix(d.tolist()).det())%3:
                units+=1
                lift=sum((a*w for a,(r,w) in zip(coeff,im)),np.zeros(64,dtype=object))
                assert all(int(x)%3**h==0 for x,h in zip(R@lift,hs))
                assert np.array_equal(np.asarray(lift).reshape(8,8)[::2,::2]%3,vec.reshape(4,4))
                # Only compute finite phases when all scalar-kernel generators vanish.
                if not any(phases):ranks[kappa(I+lift.reshape(8,8))]+=1
    return len(im),bool(bad),bool(any(phases)),units,tuple(ledger),ranks

if __name__=='__main__':
    # Independent exhaustive small lift test: arbitrary moduli and every residue.
    rng=Random(341)
    for _ in range(30):
        F=np.array([[rng.randrange(9) for _ in range(3)] for j in range(3)],dtype=object);h=[rng.randrange(1,3) for j in range(3)]
        C=cut(np.eye(3,dtype=object),F,h,2)
        ref={tuple(a%3 for a in x) for x in product(range(9),repeat=3) if all(int(v)%3**k==0 for v,k in zip(F@np.array(x,dtype=object),h))}
        out={tuple(int(a)%3 for a in C@np.array(x,dtype=object)) for x in product(range(3),repeat=3)}
        assert ref==out
    print('30 exhaustive small projection comparisons',flush=True)
    # Reproduce the exact 48 mixed R335 addresses, including its 12 non-excluded controls.
    rng=Random(332);power=lambda e:s.Integer(3)**e
    shears=[s.Integer(0)]+[power(e)*c for e in range(-20,11) for c in (1,2,-1,4)]
    E=s.zeros(8);E[1,0]=1
    result=Counter()
    for n in range(48):
        a=rng.choice(shears);u=s.eye(8);u[0,1]=a
        for i,j in [(0,2),(1,3),(0,5),(1,7)]:u[i,j]=rng.choice([0,1,-1])*power(rng.randrange(-12,13))
        b=q*u;ell=4 if v3(a)>=-2 else -2*v3(a)-1
        Y=power(ell)*b*E*b.inv();old=all(v3(Y[i,j])>=1+int(i%2==0 and j%2==1) for i,j in pairs)
        if old:continue
        out=evaluate(b);print('R335 unresolved',n,'=>',out,flush=True);result[(out[0],out[1],out[2],out[3])]+=1
    print('ledger',result,flush=True)

    # Reverse-solve the original covector via a cyclic perturbation of beta/3.
    def rank3(a):
        a=np.asarray(a,dtype=int).copy()%3;r=0
        for j in range(a.shape[1]):
            p=next((i for i in range(r,len(a)) if a[i,j]),None)
            if p is None:continue
            a[[r,p]]=a[[p,r]];a[r]=a[r]*a[r,j]%3
            for i in range(len(a)):
                if i!=r:a[i]=(a[i]-a[i,j]*a[r])%3
            r+=1
            if r==len(a):break
        return r
    for t in [s.Integer(1),s.Rational(1,3),s.Integer(3),s.Integer(9)]:
        T=beta/3
        for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=t*s.eye(2)
        v=s.eye(8)[:,0];b=s.Matrix.hstack(*[T**i*v for i in range(8)])
        assert b.det()!=0
        comp=b.inv()*T*b
        assert comp[:,:7]==s.eye(8)[:,1:] and min(map(v3,comp[:,7]))==-20
        assert all(v3((T-beta/3)[i,j])>=-1-int(i%2==1 and j%2==0) for i,j in pairs)
        out=evaluate(b);assert out[:4]==(6,False,False,729)
        R,hs,M=forms_for(b);idx=[];C=cut(A,R,hs,M,idx);im=rankbasis(C)
        sums=[0,0,0];seen=set();expected=int(t==s.Rational(1,3))
        for r,w in im:
            z=b.inv()*mat(w)*b
            assert all(v3(z[i,j])>=(20 if i==7 else 0) for i,j in pairs)
        for coeff in product(range(3),repeat=6):
            vec=sum((a*r for a,(r,w) in zip(coeff,im)),np.zeros(16,dtype=object))%3
            d=vec.reshape(4,4);assert not any(d[i,j] for i in range(4) for j in range(i+1))
            key=tuple(int(x) for x in d.flat);seen.add(key)
            lift=sum((a*w for a,(r,w) in zip(coeff,im)),np.zeros(64,dtype=object))
            phase=kappa(I+lift.reshape(8,8));assert phase==expected*sum(int(d[i,i+1]) for i in range(3))%3
            # Green's actual cuspidal trace on unipotents, R291.
            k=4-rank3(d);ch=-prod(1-3**i for i in range(1,k));sums[phase]+=ch
        assert len(seen)==729 and sums[1]==sums[2] and sums[0]-sums[1]==729*expected
        print('cyclic',t,'image U4=729','Green sums',sums,'projector rank',expected,flush=True)
        if not expected:continue
        assert 48+sum(idx)==382
        # Independent intersection in conjugate K1 additive coordinates.
        bi=b.inv();Cs=[]
        for i,j in pairs:
            E=s.zeros(8);E[i,j]=3**20 if i==7 else 1;Cs.append(b*E*bi)
        forms=[];levels=[]
        for i,j in pairs:forms.append([x[i,j] for x in Cs]);levels.append(0)
        for i,j in product(range(4),repeat=2):
            forms.append([x[2*i,2*j]-x[2*i+1,2*j+1] for x in Cs]);levels.append(1)
            forms.append([x[2*i,2*j+1]+3*x[2*i+1,2*j] for x in Cs]);levels.append(2)
        sh=[max(0,-min(map(v3,r))) for r in forms];hs=[a+h for a,h in zip(sh,levels)];M=max(3,*hs);mod=3**M
        R=np.array([[residue(x*3**a,mod) for x in r] for a,r in zip(sh,forms)],dtype=object)
        ri=[];cut(np.eye(64,dtype=object),R,hs,M,ri);assert sum(ri)==222
        prob=s.prod(1-s.Rational(1,3**i) for i in range(1,8));index=3**222*prob
        assert index.is_Integer and index*3**s.Integer(-126)/prob==3**96
        print('support address det',b.det(),'lattice valuation 382=160+222','W(1) absolute value 3^48 conditional on R327 pairing',flush=True)

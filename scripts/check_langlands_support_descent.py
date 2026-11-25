"""R332-R334: exact wild obstruction and cyclic spectral descent."""
import sympy as s
from itertools import combinations

def val(x):
    x=s.Rational(x)
    if not x: return 10**6
    a,b=abs(int(x.p)),int(x.q); n=0
    while a%3==0: a//=3; n+=1
    while b%3==0: b//=3; n-=1
    return n

B=s.Matrix([[6,21],[-7,-15]])/9
P=s.Matrix([[0,-3],[1,3]])
Q=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])*s.diag(3**7,3**6)
M=Q.inv()*(s.eye(2)+3*P)*Q
t=M[0,1]/M[1,1]
h=s.Matrix([[1,-t],[0,1]])*M
H=Q*h*Q.inv(); X=H-s.eye(2)
phase=s.trace(B*X)/3
assert t==s.Rational(19,156) and phase==-s.Rational(26,21)
assert all(val(x)>=0 for x in h) and val(h.det())==0
assert all(val(X[i,j])>=1+(i==0 and j==1) for i in range(2) for j in range(2))
assert val(phase)==-1 and int(3*phase*21/3)==-26
print('identity coset excluded: phase',phase,'h',h.tolist())

# Intersection of the actual 3A lattice with conjugated integral matrices.
# A single linear congruence is paid by valuation pivot, not residue enumeration.
def restrict(cols, linear, level):
    y=[linear(c) for c in cols]; p=min(range(len(y)),key=lambda i:val(y[i]))
    if val(y[p])>=level:return cols
    c=cols[p]; a=y[p]; out=[z-c*(b/a) if i!=p else c*3**(level-val(a)) for i,(z,b) in enumerate(zip(cols,y))]
    assert all(val(linear(z))>=level for z in out)
    return out

base=[s.Matrix([[3,0],[0,0]]),s.Matrix([[0,9],[0,0]]),s.Matrix([[0,0],[3,0]]),s.Matrix([[0,0],[0,3]])]
results=[]
for den in range(5):
    for a in [-2,-1,0,1,2]:
        u=s.Matrix([[1,s.Rational(a,3**den)],[0,1]])
        g=Q*u; gi=g.inv(); cols=base[:]
        for i in range(2):
            for j in range(2):
                cols=restrict(cols,lambda c,i=i,j=j:(gi*c*g)[i,j],0)
        ph=[s.trace(B*c)/3 for c in cols]
        for c in cols:
            assert all(val(x)>=0 for x in gi*c*g)
            assert val((s.eye(2)+c).det())==0
        results.append((den,a,min(map(val,ph))))
assert results[2][2]<0
print('25 supplied shear scalar gates (negative valuation excludes):',results)

# Original primitive Fourier labels; four sectors of the tame order-five weight.
J=[1,2,4,7,8,11,13,14]; orbit=[1,3,4,2]
idx={j:orbit.index(j%5) for j in J}; z=s.symbols('z',nonzero=True)
Phi=s.zeros(8); A=s.zeros(8)
for i,j in enumerate(J):
    Phi[J.index(13*j%15),i]=1
    A[J.index(11*j%15),i]=1
D=s.diag(*[s.I**idx[j] for j in J])
G=s.diag(*[z**(-idx[j]) for j in J])
assert D**4==s.eye(8) and D*A==A*D and D*Phi*D.inv()==s.I*Phi
F=s.simplify(G*(z*Phi)*G.inv())
assert F**4==z**4*s.eye(8) and F.subs(z,s.I*z)==F
assert s.factor(F.det())==z**8
n=0
for k in range(9):
    for S in combinations(J,k):
        T=[13*j%15 for j in S]
        # gauge descends each exterior monomial including wrap and wedge sign
        wrap=sum(idx[j]==3 for j in S)
        assert k+sum(idx[j] for j in S)-sum(idx[j] for j in T)==4*wrap
        assert s.I**(sum(idx[j] for j in T)-sum(idx[j] for j in S))==s.I**k
        n+=1
assert n==256
print('256 exterior monomial descent identities; determinant alpha^2')
# Universal first-block shear exclusion: shallow shears lie in J1;
# deep shears conjugate an integral diagonal to a nontrivial wild phase.
for den in range(2,13):
    for a in (-2,-1,1,2):
        t=s.Rational(a,3**den); delta=1/(3*t)
        u=s.Matrix([[1,t],[0,1]])
        X=Q*u*s.diag(0,delta)*u.inv()*Q.inv()
        assert all(val(X[i,j])>=1+(i==0 and j==1) for i in range(2) for j in range(2))
        assert val(s.trace(B*X)/3)==-1
        assert val(delta)>=1 and val(1+delta)==0
print('44 deep-shear explicit witnesses')

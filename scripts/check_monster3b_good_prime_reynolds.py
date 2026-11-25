"""Exact cyclotomic control of the good-prime Reynolds lift, not Monster data."""
from sympy import QQ
from sympy.polys.matrices import DomainMatrix as DM
K=QQ.cyclotomic_field(3); Z=K.unit

def M(rows):return DM([[K.convert(x) for x in r] for r in rows],(len(rows),len(rows[0])),K).to_dense()
def require(b,m):
    if not b:raise ValueError(m)
def red(x,p=31,z=5):
    a=x.to_list();out=0
    for c in a:
        out=(out*z+int(c.numerator)*pow(int(c.denominator),-1,p))%p
    return out
def residues(A):return [[red(x) for x in row] for row in A.to_list()]
I=M([[1,0],[0,1]]);C=M([[0,1],[1,0]]);D=M([[Z,0],[0,Z**2]])
G=[((D**i)*(C**j)).to_dense() for j in range(2) for i in range(3)]
require(len({str(x.to_list()) for x in G})==6,'group order')
require(all(any(a*b==g for g in G) for a in G for b in G),'group closure')
count=0
for X in (M([[1,Z],[0,1]]), M([[1,0],[1-Z,2]]), M([[Z,1],[1,1]])):
    Xi=X.inv();L=[X*a*Xi for a in G]
    F0=M(residues(X))+M([[31,62],[-31,93]])
    F=M([[0,0],[0,0]])
    for a,l in zip(G,L):F+=l*F0*a.inv()
    F=F.scalarmul(K.one/K.convert(len(G)));Fi=F.inv()
    require(residues(F)==residues(F0),'reduction of Reynolds average');count+=1
    for a,l in zip(G,L):
        require(l*F==F*a and a*Fi==Fi*l,'forward/reverse intertwiner');count+=2
    require(F*Fi==I and Fi*F==I,'two-sided inverse');count+=2
# Bad-prime counterexample: trivial and sign of C2 agree mod2 but not over Q.
require((1%2)==(-1%2) and (QQ(1)+QQ(-1))/2==0,'bad prime control');count+=1
print({'exact_good_prime_checks':count,'group':'S3 signed cyclotomic fixture','bad_prime_counterexample':'C2 at 2'})

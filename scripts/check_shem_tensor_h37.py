from itertools import product
from sympy import Matrix, GF, __version__
from sympy.polys.matrices import DomainMatrix
from collections import Counter
from math import prod
P=list(product(range(3),range(4),range(6)))
N=len(P)
# tensor of anchored differences, not a mean projection (3 and 6 are zero in F3).
def coeff(p,q):
    return prod((int(x==y) if x==0 else int(x==y)-int(y==0)) for x,y in zip(p,q))
T=Matrix([[coeff(p,q) for q in P] for p in P])
S=Matrix([[int(all(y==0 or y==x for x,y in zip(p,q))) for q in P] for p in P])
assert T*S==S*T==Matrix.eye(N)
assert DomainMatrix.from_Matrix(T).convert_to(GF(3)).rank()==72
counts=Counter(sum((x!=0)<<i for i,x in enumerate(p)) for p in P)
assert [counts[i] for i in range(8)]==[1,2,3,6,5,10,15,30]
words=['ויסעמלאךהאלהיםההלךלפנימחנהישראלוילךמאחריהםויסעעמודהענןמפניהםויעמדמאחריהם','ויבאביןמחנהמצריםוביןמחנהישראלויהיהענןוהחשךויאראתהלילהולאקרבזהאלזהכלהלילה','ויטמשהאתידועלהיםויולךיהוהאתהיםברוחקדיםעזהכלהלילהוישםאתהיםלחרבהויבקעוהמים']
assert all(len(w)==72 for w in words)
glyphs='אבגדהוזחטיכלמנסעפצקרשתךםןףץ'
def code(i):
    t=i//9; u=i%3; v=i%9//3
    return (t,(t+u)%3,(t+v)%3)
enc={g:code(i) for i,g in enumerate(glyphs)}
a,b,c=[Matrix([enc[g] for g in w]) for w in [words[0],words[1][::-1],words[2]]]
for name,g in [('zero',Matrix.zeros(72,3)),('copyA',a),('copyB',b),('minusSum',-a-b)]:
    r=(c-g).applyfunc(lambda x:x%3)
    z=(T*r).applyfunc(lambda x:x%3)
    assert (g+S*z).applyfunc(lambda x:x%3)==c
    zeros=[sum(all(z[j,i]==0 for i in range(3)) for j,p in enumerate(P) if sum((x!=0)<<k for k,x in enumerate(p))==m) for m in range(8)]
    print(name,'zero coefficients',zeros)
print('SymPy',__version__,'rank 72; both exact matrix inverses; four original source residuals PASS')

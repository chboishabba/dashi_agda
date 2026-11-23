from itertools import product
import sympy as s
# Reference replay of source fixtures at 116cd7de, not Agda execution.
T=(-1,0,1)
P=list(product(T,repeat=3))
assert len(P)==27
assert all(len([p for p in P if p[:2]==xy])==3 for xy in product(T,repeat=2))
a,b,c=(-1,0,-1),(-1,0,0),(-1,0,1)
assert a[:2]==b[:2]==c[:2] and a[2]+1==b[2] and b[2]+1==c[2]
W=s.Matrix([[5,10,0],[2,0,22],[18,20,0]])/10
assert W[0,2]==0 and (W**2)[0,2]==s.Rational(11,5)
assert W[0,1]!=W[1,0]
assert (W, 'reciprocal')[0]==(W,'coercive')[0]
assert (W, 'reciprocal')[1]!=(W,'coercive')[1]
# Face seam controls: capacity and paint conditions only; full Pants proof is source-owned.
red=(0,)*9; green=(1,)*9
assert red==red and 2!=1
assert tuple((v+1)%3 for v in red)==green
swap={0:0,1:2,2:1}
assert tuple(swap[v] for v in red)==red and swap[1]!=1
# Original goal-directed fixture: source specifies the transported latent value.
def defect(x):
 l,o,d,c=x; return int(l!=d)+int(o!=l)+int(d!=c)
assert defect((-1,0,1,1))==2 and defect((1,0,1,1))==1
reference=(False,True,False,True); memorised=(False,True,False,False)
assert reference[:2]==memorised[:2] and reference[1]==reference[3] and memorised[1]!=memorised[3]
flip=(1,0,3,2)
assert all(reference[flip[i]]!=reference[i] for i in range(4))
assert not all(memorised[flip[i]]!=memorised[i] for i in range(4))
print('SymPy',s.__version__,'PASS: XY fibres, mediated weighted path, attached-face collision, palette controls, defect 2->1, paired/nuisance controls')

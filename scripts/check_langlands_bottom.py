"""Bottom block affine gate on original lower type carrier."""
from pathlib import Path
exec(Path(__file__).with_name('check_langlands_block_row.py').read_text().split('# Fixed bottom six ORIGINAL rows')[0])
J=s.zeros(8);J[6:8,6:8]=s.eye(2);Gs=[]
for c,k in product(range(4),range(4)):
 G=s.zeros(8);G[6:8,2*c:2*c+2]=base[k]*(3 if k==0 else 1);Gs.append(G)
def gate(V,offset=False):
 return s.Matrix(list(V[6,:])+[ (V[7,j]-int(offset and j==7))/3**20 for j in range(8)])
V=R*J*b;M=s.Matrix.hstack(*[gate(R*g*b) for g in Gs]);c=gate(V,True);sol=cut(M,c);assert sol is not None
x,L,idx=sol;J=J+sum((a*g for a,g in zip(x,Gs)),s.zeros(8));G2=[sum((L[k,i]*g for k,g in enumerate(Gs)),s.zeros(8)) for i in range(16)]
print('bottom affine index',idx,'matrix mass exponent',16+idx)
assert idx==0 or idx>0
# Finite residue image of bottom C,D and full diagonal phase dependence mod27.
F=s.Matrix.hstack(*[s.Matrix([res(g[7,2*i]) for i in range(4)]) for g in G2]);rank=0;A=F.copy()
for j in range(A.cols):
 p=next((p for p in range(rank,A.rows) if A[p,j]%3),None)
 if p is None:continue
 A.row_swap(rank,p);A[rank,:]=(A[rank,:]*pow(int(A[rank,j]%3),-1,3)).applyfunc(lambda z:z%3)
 for p in range(rank+1,A.rows):A[p,:]=(A[p,:]-A[p,j]*A[rank,:]).applyfunc(lambda z:z%3)
 rank+=1
 if rank==A.rows:break
print('bottom D-residue image rank',rank,'base',list(J[7,::2].applyfunc(res)))
# The original root-free representative has exactly this bottom block (UDL upper action leaves it unchanged).
assert all(v3(z)>=0 for z in gate(R*j0*b,True))
assert all(v3(z)>=0 for z in gate(R*J*b,True))
assert all(v3(z)>=0 for G in G2 for z in gate(R*G*b))
# Bottom suffix extends to an integral unimodular basis when primitive mod3.
V=R*J*b; assert v3(V[7,7]-1)>=20 and all(v3(V[7,j])>=20 for j in range(7))
print('bottom penultimate residues',list(V[6,:].applyfunc(res)))
# Exact projected primitive-row gate on the bottom affine lattice.
F=s.Matrix.hstack(*[s.Matrix([res(z) for z in (R*g*b)[6,:7]]) for g in G2]);rows={}
for k in range(16):
 y=F[:,k]
 for p,r in sorted(rows.items()):y=(y-y[p]*r).applyfunc(lambda z:z%3)
 if any(y):
  p=next(i for i,z in enumerate(y) if z);rows[p]=(int(y[p])*y).applyfunc(lambda z:z%3)
rank=len(rows);y0=s.Matrix([res(z) for z in V[6,:7]])
from collections import Counter
counts=Counter()
for co in product(range(3),repeat=rank):
 y=(y0+sum((a*g for a,g in zip(co,rows.values())),s.zeros(7,1))).applyfunc(lambda z:z%3)
 counts['primitive' if any(y) else 'nonprimitive']+=1
print('bottom projected primitive image rank',rank,'counts',dict(counts),'actual',list((R*j0*b)[6,:7].applyfunc(res)))

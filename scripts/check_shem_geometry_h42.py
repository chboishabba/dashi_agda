from itertools import product
from math import prod
from sympy import Matrix, eye, __version__
for dims in [(3,4,6),(8,3,3),(2,4,3,3),(2,2,2,3,3)]:
 p=list(product(*(range(n) for n in dims)))
 T=Matrix([[prod(int(a==b) if a==0 else int(a==b)-int(b==0) for a,b in zip(x,y)) for y in p] for x in p])
 S=Matrix([[int(all(b==0 or a==b for a,b in zip(x,y))) for y in p] for x in p])
 assert T*S==S*T==eye(72)
 assert all(S[i,j]==0 for i in range(72) for j in range(i+1,72))
 print(dims,'two-sided inverse and causal synthesis PASS')
for m in range(8):
 s=[72*r+(71-j if m>>r&1 else j) for j in range(72) for r in range(3)]
 assert len(set(s))==216
 seams=[(a,b) for a,b in zip(s,s[1:]) if b-a==1]
 assert seams==([(143,144),(71,72)] if m==2 else seams)
 print(m,seams)
print('SymPy',__version__)

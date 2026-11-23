#!/usr/bin/env python3
"""Original side4->side2 Wilson block: exact free-group and support regression.
The halfspace here is a SELECTED geometric candidate, not published RP."""
from itertools import product,combinations
D=4
def shift(x,a,n,s=1):
 y=list(x);y[a]=(y[a]+s)%n;return tuple(y)
def reflect(x,n,k):
 y=list(x);y[0]=(k-y[0])%n;return tuple(y)
def inv(w):return tuple((e,-s) for e,s in reversed(w))
def red(seq):
 out=[]
 for e in seq:
  if out and out[-1][0]==e[0] and out[-1][1]==-e[1]:out.pop()
  else:out.append(e)
 return tuple(out)
def mul(*words):return red(e for w in words for e in w)
def link(x,a):return (((x,a),1),)
def pulled(x,a,k):
 y=reflect(x,4,k)
 return inv(link(shift(y,0,4,-1),0)) if a==0 else link(y,a)
def block(x,a):
 y=tuple(2*v for v in x)
 return mul(link(y,a),link(shift(y,a,4),a))
def pulled_block(x,a,k):
 y=tuple(2*v for v in x)
 return mul(pulled(y,a,k),pulled(shift(y,a,4),a,k))
def reflected_block(x,a,k):
 y=reflect(x,2,k//2)
 return inv(block(shift(y,0,2,-1),a)) if a==0 else block(y,a)
def plaq(x,a,b,fn):
 return mul(fn(x,a),fn(shift(x,a,4),b),inv(fn(shift(x,b,4),a)),inv(fn(x,b)))
def cyclic_real(a,b):
 for w in (b,inv(b)):
  for j in range(len(w)):
   if a==w[j:]+w[:j]:return True
 return False
def native_bonds(x,a):
 y=tuple(2*v for v in x)
 return ((y,a),(shift(y,a,4),a))
def coarse_plaquette_support(x,a,b):
 edges=((x,a),(shift(x,a,2),b),(shift(x,b,2),a),(x,b))
 return {e for y,c in edges for e in native_bonds(y,c)}
def candidate_half(e):
 y,a=e
 return y[0] in ({0,1} if a==0 else {0,1,2})
def main():
 fine=list(product(range(4),repeat=D))
 coarse=list(product(range(2),repeat=D))
 assert len(fine)==256 and len(coarse)==16
 for k in (0,2):
  assert all(reflect(reflect(x,4,k),4,k)==x for x in fine)
  assert all(pulled_block(x,a,k)==reflected_block(x,a,k) for x in coarse for a in range(D))
  assert all(cyclic_real(plaq(x,a,b,lambda y,c:pulled(y,c,k)),
      plaq(shift(reflect(x,4,k),0,4,-1) if a==0 or b==0 else reflect(x,4,k),a,b,link))
      for x in fine for a,b in combinations(range(D),2))
 selected=[(x,0) for x in coarse if x[0]==0]
 assert len(selected)==8
 assert all({e[0][0] for e in native_bonds(x,a)}=={0,1} for x,a in selected)
 positive=[(x,a,b) for x in coarse if x[0]==0 for a,b in combinations(range(D),2)]
 assert len(positive)==48
 assert all(all(candidate_half(e) for e in coarse_plaquette_support(x,a,b)) for x,a,b in positive)
 assert all(not {e[0][0] for e in native_bonds(x,0)}.issubset({1,2}) for x in coarse)
 print('PASS both mirror placements: 128/128 non-Abelian R445 block identities')
 print('PASS 3072/3072 reflected original plaquette real-trace identities')
 print('PASS 8 selected positive time blocks, 48/48 coarse positive plaquettes')
 print('OPEN source-published OS halfspace, Agda kernel, fine Wilson RP, physical D1/E1/D2')
if __name__=='__main__':main()

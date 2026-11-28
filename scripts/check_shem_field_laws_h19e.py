# H19e independent finite replay; polynomial product, field laws, proper conics, ratios.
from itertools import product
from collections import Counter
import sympy as sp
V=range(27); vec=lambda x:(x%3,x//3%3,x//9); enc=lambda v:sum(int(a)%3*3**i for i,a in enumerate(v))
t=sp.symbols('t'); p=sp.Poly(t**3-t-1,t,modulus=3); assert p.is_irreducible
pol=[sp.Poly(sum(a*t**i for i,a in enumerate(vec(x))),t,modulus=3) for x in V]
A=[[enc([a+b for a,b in zip(vec(x),vec(y))]) for y in V] for x in V]; N=[enc([-a for a in vec(x)]) for x in V]; D=[[A[x][N[y]] for y in V] for x in V]; M=[[enc([(pol[x]*pol[y]).rem(p).nth(i) for i in range(3)]) for y in V] for x in V]; I=[0]+[M[x].index(1) for x in range(1,27)]
for x,y in product(V,repeat=2):
 a,b,c=vec(x);d,e,f=vec(y); p0=a*d;p1=a*e+b*d;p2=a*f+b*e+c*d;p3=b*f+c*e;p4=c*f
 assert M[x][y]==enc([p0+p3,p1+p3+p4,p2+p4])
 assert D[A[x][y]][x]==y and A[x][D[y][x]]==y
 assert M[x][y]==M[y][x] and A[x][y]==A[y][x]
 if x: assert M[I[x]][M[x][y]]==y and M[x][M[I[x]][y]]==y
for x,y,z in product(V,repeat=3):
 assert A[A[x][y]][z]==A[x][A[y][z]]
 assert M[M[x][y]][z]==M[x][M[y][z]]
 assert M[x][A[y][z]]==A[M[x][y]][M[x][z]]
for x in V:
 assert A[x][0]==x and A[x][N[x]]==0 and M[x][1]==x and M[x][0]==0
 if x: assert M[x][I[x]]==1
pow3=lambda x:M[x][M[x][x]]
q=lambda x:M[pow3(x)][pow3(pow3(x))]
dot=lambda n,x:sum(a*b for a,b in zip(vec(n),vec(x)))%3
for n,x in product(V,repeat=2): assert (dot(n,I[x])==0)==(dot(n,q(x))==0)
for x in range(1,27):assert M[x][q(x)] in (1,2)
B=sp.Matrix([[1,1,1],[0,0,1],[0,1,2]]);Bi=B.inv_mod(3)
for n,x in product(V,repeat=2):assert int((Bi.T*sp.Matrix(vec(n))).dot(B*sp.Matrix(vec(x))))%3==dot(n,x)
for r in (22,14):
 for a,b in product(V,repeat=2):
  c=A[a][M[r][D[b][a]]]
  assert A[a][M[I[r]][D[c][a]]]==b
  assert M[I[D[1][r]]][D[c][M[r][b]]]==a
  assert (len({a,b,c})==3)==(a!=b)
  assert A[a][M[r][D[A[a][M[I[r]][D[b][a]]]][a]]]==b
  l=M[I[D[1][r]]][D[b][M[r][a]]]
  assert A[l][M[r][D[a][l]]]==b
pw=[1]
for i in range(1,13):pw.append(M[pw[-1]][3])
assert M[pw[-1]][3]==1
for i,s in product(range(13),range(2)):
 x=pw[(i-3)%13];y=pw[(3-i)%13]
 if s:x,y=N[x],N[y]
 assert I[x]==y
axes=sorted({min(x,N[x]) for x in range(1,27)})
lines=[{x for x in axes if dot(n,x)==0} for n in axes]; conics=[{x for x in axes if dot(n,q(x))==0} for n in axes]
assert all(len(x)==4 for x in conics) and not any(x==y for x in lines for y in conics)
assert all(Counter(len(l&c) for l in lines)=={0:3,1:4,2:6} for c in conics)
for n in axes:
 e=[1,3,9]; Q=lambda x:dot(n,q(x)); H=sp.Matrix(3,3,lambda i,j:2*(Q(A[e[i]][e[j]])-Q(e[i])-Q(e[j]))%3)
 assert H.det()%3!=0
print({'sympy':sp.__version__,'product_formula':729,'ring_law_triples_per_law':19683,'nonzero_inverse':26,'slot_inverse':26,'scale_cancel_each':702,'add_sub_each':729,'quadratic_zero_test':729,'norm_nonzero':26,'dual_covariance':729,'ratio_inverse_each_direction':1458,'ratio_pair_distinct':1458,'proper_conics':13,'line_conic_intersections':169})

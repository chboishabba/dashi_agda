#!/usr/bin/env python3
"""Exact source-produced R568 D/M on the actual C=1 Galerkin Fourier cube.

Master owner source: ExactSignedGalerkinCoefficient (ordered -iP_k (u_p.q)u_q),
Complex3GalerkinEquationAudit (complete physicalOutputFiber),
PeriodicHelicalFourierInfrastructure (helical +/- projectors),
R225 doubleMixedCell, R380/R388 doubleForcing, R566/R687 forcingPair.

Exact coefficient field Q[sqrt(2),sqrt(3),i], 8 rational basis entries.

IMPORTANT: the native R567/R687 owner currently fixes F=Q, which does NOT
contain sqrt(2) or sqrt(3). This exact physical helicity evaluation is a
faithful algebraic extension of the displayed Fourier formulas, NOT a
constructive inhabitant of the existing literal rational Agda record. An
explicit field extension/natural-transformation weld remains OPEN.
State u is divergence-free, conjugate-real, zero at k=0; N is computed
from the SAME complete ordered physical lattice and u; not proxy D/M.
No PDE spacetime estimate; finite static Galerkin states only.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import argparse, math, random

# Basis 1,rt2,rt3,rt6,i,i*rt2,i*rt3,i*rt6.
# Index's low two bits select radical, bit 2 selects i.
BASE=(1,2,3,6)
MULT=[[None]*8 for _ in range(8)]
for a in range(8):
 for b in range(8):
  t=(a^b);coef=(-1 if a&4 and b&4 else 1)
  if a&b&1:coef*=2
  if a&b&2:coef*=3
  MULT[a][b]=(t,coef)
class F:
 __slots__=('c',)
 def __init__(self,c=0):
  if isinstance(c,F):self.c=c.c
  elif isinstance(c,(int,Q)):self.c=(Q(c),)+(Q(0),)*7
  else:self.c=tuple(Q(x) for x in c);assert len(self.c)==8
 def __add__(a,b):
  b=F(b);return F(tuple(x+y for x,y in zip(a.c,b.c)))
 __radd__=__add__
 def __neg__(a):return F(tuple(-x for x in a.c))
 def __sub__(a,b):return a+-F(b)
 def __rsub__(a,b):return F(b)+-a
 def __mul__(a,b):
  b=F(b);out=[Q(0)]*8
  for i,x in enumerate(a.c):
   if x==0:continue
   for j,y in enumerate(b.c):
    if y==0:continue
    k,z=MULT[i][j];out[k]+=x*y*z
  return F(out)
 __rmul__=__mul__
 def __truediv__(a,b):
  if not isinstance(b,(int,Q)):raise TypeError('division only by rational')
  return F(tuple(x/b for x in a.c))
 def __eq__(a,b):return a.c==F(b).c
 def conjugate(a):return F(tuple(x if i<4 else -x for i,x in enumerate(a.c)))
 def real(a):return F(a.c[:4]+(Q(0),)*4)
 def scalar(a):assert all(x==0 for x in a.c[1:]);return a.c[0]
 def decimal(a):
  t=(1,2**.5,3**.5,6**.5)
  return float(sum(float(x)*t[i] for i,x in enumerate(a.c[:4])))
 def __repr__(a):return f'F({a.c})'
Z=F(0);ONE=F(1);I=F((0,0,0,0,1,0,0,0));RT2=F((0,1,0,0,0,0,0,0));RT3=F((0,0,1,0,0,0,0,0))
INVRT={1:ONE,2:RT2/2,3:RT3/3}
VZERO=(Z,Z,Z)

def vadd(a,b):return tuple(x+y for x,y in zip(a,b))
def vsub(a,b):return tuple(x-y for x,y in zip(a,b))
def vmul(z,a):return tuple(z*x for x in a)
def conj(a):return tuple(x.conjugate() for x in a)
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Z)
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def reHerm(a,b):return sum((x.conjugate()*y for x,y in zip(a,b)),Z).real()
def kvec(k):return tuple(F(x) for x in k)
def m2(k):return sum(x*x for x in k)
def proj(k,v):
 if not m2(k):return VZERO
 return vsub(v,vmul(dot(kvec(k),v)/m2(k),kvec(k)))
def hel(k,v,sgn):
 if not m2(k):return VZERO
 return vmul(Q(1,2),vadd(proj(k,v),vmul(I*sgn*INVRT[m2(k)],cross(kvec(k),v))))
def exact_mode_norm(k):
 if m2(k)==0:return Z
 return {1:ONE,2:RT2,3:RT3}[m2(k)]

def audit_helicity(k,v):
 if m2(k)==0:
  assert v==VZERO
  return
 hp,hm=hel(k,v,1),hel(k,v,-1)
 assert vadd(hp,hm)==proj(k,v)
 curlp=vmul(I,cross(kvec(k),hp));curlm=vmul(I,cross(kvec(k),hm))
 norm=exact_mode_norm(k)
 assert curlp==vmul(norm,hp),('positive curl',k)
 assert curlm==vmul(-norm,hm),('negative curl',k)
 assert exact_mode_norm(k)*INVRT[m2(k)]==ONE

def exact_real_interval(a,precision=10**13):
 """Outward rational interval for exact a in Q(sqrt(2),sqrt(3)); no floats."""
 assert all(c==0 for c in a.c[4:]),('nonreal sign target',a)
 lo=hi=Q(0)
 for n,c in zip((1,2,3,6),a.c[:4]):
  low=Q(math.isqrt(n*precision*precision),precision)
  high=Q(math.isqrt(n*precision*precision)+1,precision)
  assert low*low<=n<high*high
  if c>=0:lo+=c*low;hi+=c*high
  else:lo+=c*high;hi+=c*low
 assert lo<=hi
 return lo,hi

def exact_sign(a):
 lo,hi=exact_real_interval(a)
 if lo>0:return 1
 if hi<0:return -1
 if a==Z:return 0
 raise AssertionError(('undecidable interval; increase precision',lo,hi))

def exact_bracket(a):
 lo,hi=exact_real_interval(a)
 return f'[{float(lo):.12f}, {float(hi):.12f}]'

def modes(C=1):return list(product(range(-C,C+1),repeat=3))
def neg(k):return tuple(-t for t in k)
def output_fibre(C,k):
 return [(p,tuple(k[i]-p[i] for i in range(3))) for p in modes(C)
         if all(abs(k[i]-p[i])<=C for i in range(3))]
def paired_state(seed,sparse=False):
 rng=random.Random(seed);u={k:VZERO for k in modes()}
 pset=[k for k in modes() if k!= (0,0,0) and k>neg(k)]
 for k in pset:
  if sparse and k not in {(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)}:continue
  v=tuple(F((rng.randrange(-2,3),0,0,0,rng.randrange(-2,3),0,0,0)) for _ in range(3))
  u[k]=proj(k,v);u[neg(k)]=conj(u[k])
 return u

def galerkin_nonlinearity(u,C=1):
 G={k:VZERO for k in modes(C)}
 active=[(p,up) for p,up in u.items() if up!=VZERO]
 for p,up in active:
  for q,uq in active:
   k=tuple(p[i]+q[i] for i in range(3))
   if k==(0,0,0) or any(abs(x)>C for x in k):continue
   term=vmul(-I*dot(up,kvec(q)),proj(k,uq))
   G[k]=vadd(G[k],term)
 return G

def physical_cells(u,G,k,C=1):
 assert max(abs(x) for x in k)<=C and k!=(0,0,0)
 # Cache BOTH original helical projectors on each velocity and its own nonlinear force.
 H={p:(hel(p,u[p],1),hel(p,u[p],-1),hel(p,G[p],1),hel(p,G[p],-1)) for p in modes(C)}
 rows=[]
 for p,q in output_fibre(C,k):
  a,b,c,d=H[p];e,f,g,h=H[q]
  M=vmul(F(2),vsub(cross(a,f),cross(b,e)))
  # Original R388: 2[ R230 productRule(p,q) + R230 productRule(q,p) ].
  D=vmul(F(2),vadd(vadd(cross(c,f),cross(a,h)),vadd(cross(g,b),cross(e,d))))
  rows.append((p,q,m2(p)+m2(q),D,M))
 return rows

def sumv(vectors):
 out=VZERO
 for a in vectors:out=vadd(out,a)
 return out

def inspect_source(u,k):
 C=1;G=galerkin_nonlinearity(u,C);rs=physical_cells(u,G,k,C)
 for p,v in u.items():
  assert dot(kvec(p),v)==Z and u[neg(p)]==conj(v),('state',p)
  assert dot(kvec(p),G[p])==Z and G[neg(p)]==conj(G[p]),('force',p)
  audit_helicity(p,v);audit_helicity(p,G[p])
 by=defaultdict(list)
 for index,(_,_,m,D,M) in enumerate(rs):by[m].append(index)
 aggregated={m:(sumv(rs[i][3] for i in idx),sumv(rs[i][4] for i in idx)) for m,idx in by.items()}
 Fpair=Z
 activeD=[x for x in rs if x[3]!=VZERO]
 activeM=[x for x in rs if x[4]!=VZERO]
 for p,q,m,D,_ in activeD:
  for _,_,n,_,M in activeM:
   Fpair+=reHerm(D,M)/(m+n)
 Fbucket=sum((reHerm(D,M)/(m+n) for m,(D,_) in aggregated.items()
             for n,(_,M) in aggregated.items()),Z)
 assert Fpair==Fbucket,('actual D/M source inconsistency',Fpair,Fbucket)
 lifted=sum((reHerm(D,M) for m,(D,_) in aggregated.items()
             for n,(_,M) in aggregated.items()),Z)
 assert lifted==reHerm(sumv(rs[i][3] for i in range(len(rs))),sumv(rs[i][4] for i in range(len(rs))))
 # R290/R596/R560 same-object finite Cauchy-GRAM evolution in the actual
 # algebraic helicity carrier.  Mdot_m=D_m-m*M_m is the R388 physical damped
 # mixed-product tangent with nu=1, not an arbitrary time derivative.
 # Qraw = sum K Re<M_a,M_b> is HALF the source R596 coherent-work Gram.
 # Therefore Qraw'=2*Fpair-||sum_a M_a||^2;
 # Qsource=2*Qraw has Qsource'=4*Fpair-2*||sum_a M_a||^2.
 # A native scalar FTC and genuine R240 trajectory remain external obligations.
 gram=sum((reHerm(Ma,Mb)/(m+n) for m,(_,Ma) in aggregated.items()
           for n,(_,Mb) in aggregated.items()),Z)
 mdot={m:vsub(D,vmul(F(m),M)) for m,(D,M) in aggregated.items()}
 gram_prime=sum(((reHerm(mdot[m],Mb)+reHerm(Ma,mdot[n]))/(m+n)
                 for m,(_,Ma) in aggregated.items()
                 for n,(_,Mb) in aggregated.items()),Z)
 coherent_self=reHerm(sumv(rs[i][4] for i in range(len(rs))),
                     sumv(rs[i][4] for i in range(len(rs))))
 assert gram_prime==F(2)*Fpair-coherent_self
 assert gram==Z or exact_sign(gram)>0
 # Independently check both nontrivial source welds R225/R230/R542:
 # Msum = 4*sum(u_p^+ x u_q^-) and Dsum = 4*sum(forcing commutator cell).
 positive_mixed=VZERO;commutator=VZERO
 for p,q,_,_,_ in rs:
  up=hel(p,u[p],1);uqminus=hel(q,u[q],-1)
  gp=hel(p,G[p],1);gqminus=hel(q,G[q],-1)
  gpminus=hel(p,G[p],-1);uqplus=hel(q,u[q],1)
  positive_mixed=vadd(positive_mixed,cross(up,uqminus))
  commutator=vadd(commutator,vsub(cross(gp,uqminus),cross(gpminus,uqplus)))
 Mfold=sumv(r[4] for r in rs);Dfold=sumv(r[3] for r in rs)
 assert Mfold==vmul(F(4),positive_mixed),('R225 actual sum failed',k)
 assert Dfold==vmul(F(4),commutator),('R230/R542 actual sum failed',k)
 # Original R687 LiftedFull = 8 coherentWork(M,C); coherentWork=2 Re.
 assert lifted==F(16)*reHerm(positive_mixed,commutator)

 # For each incidence swap(p,q), M and D must be exactly symmetric.
 rowmap={(p,q):(m,D,M) for p,q,m,D,M in rs}
 for p,q,m,D,M in rs:
  sm,sD,sM=rowmap[(q,p)]
  assert sm==m and sD==D and sM==M
 # Full within-rate radical projection: original D/M need not themselves be uniform.
 Dp={};Mp={}
 for m,idx in by.items():
  Dm,Mm=aggregated[m];avgD=vmul(F(Q(1,len(idx))),Dm);avgM=vmul(F(Q(1,len(idx))),Mm)
  for i in idx:Dp[i]=avgD;Mp[i]=avgM
 projection_pair=Z
 for i,(_,_,m,_,_) in enumerate(rs):
  for j,(_,_,n,_,_) in enumerate(rs):
   projection_pair+=reHerm(Dp[i],Mp[j])/(m+n)
 assert projection_pair==Fpair
 return {'F':Fpair,'L':lifted,'incidences':len(rs),'rates':len(by),
         'D_active':len(activeD),'M_active':len(activeM),'rank':len(by),
         'nullity':len(rs)-len(by),'by':aggregated,'rows':rs,
         'Qraw':gram,'QrawPrime':gram_prime,'selfGram':coherent_self}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=12);ap.add_argument('--start-seed',type=int,default=0);ap.add_argument('--require-opposite',action='store_true');ap.add_argument('--print-certificate',action='store_true')
 ap.add_argument('--output',default='1,0,0');ap.add_argument('--sparse',action='store_true')
 args=ap.parse_args();k=tuple(map(int,args.output.split(',')))
 assert k!=(0,0,0) and all(abs(t)<=1 for t in k)
 nonzero=0;disagree=0
 for seed in range(args.start_seed,args.start_seed+args.seeds):
  u=paired_state(seed,sparse=args.sparse)
  o=inspect_source(u,k)
  Fval,Lval=o['F'].decimal(),o['L'].decimal()
  if o['F']!=Z:nonzero+=1
  reversal=exact_sign(o['F'])*exact_sign(o['L'])==-1
  if reversal:disagree+=1
  if args.print_certificate:
   print('CERT exact F in Q[sqrt2,sqrt3] =',tuple(str(x) for x in o['F'].c[:4]),
         'interval',exact_bracket(o['F']),flush=True)
   print('CERT exact L in Q[sqrt2,sqrt3] =',tuple(str(x) for x in o['L'].c[:4]),
         'interval',exact_bracket(o['L']),flush=True)
   print('CERT Qraw=1/2 R596 coherent-resolvent Gram =',
         tuple(str(x) for x in o['Qraw'].c[:4]),
         'interval',exact_bracket(o['Qraw']),flush=True)
   print('CERT QrawPrime from actual R388 damped tangent =',
         tuple(str(x) for x in o['QrawPrime'].c[:4]),
         'interval',exact_bracket(o['QrawPrime']),flush=True)
   print('CERT exact normalized source evolution: QsourcePrime=4F-2||Msum||^2',flush=True)
  print('PASS exact ORIGINAL projected Galerkin helical state',seed,'k',k,
        'N',o['incidences'],'R',o['rates'],'nullity',o['nullity'],
        'active D/M',o['D_active'],o['M_active'],
        'F',round(Fval,10),'L',round(Lval,10),
        'certified sign reversal',reversal,flush=True)
 print('PASS physical same-state consistency',args.seeds,'fixtures, nonzero=',nonzero,
       'physical sign reversals=',disagree)
 if args.require_opposite:assert disagree>=1,'No actual Galerkin sign reversal found'
 print('OPEN: original Agda rational-scalar-to-exact-algebraic-helicity transport; R240 trajectory/time integration, C1/C2 estimates, 3D PDE limit; not kernel-certified')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact localized-helicity reconnaissance on the six-mode quartic witness."""
from __future__ import annotations
import argparse, json
from fractions import Fraction as F
from itertools import product
from pathlib import Path

C=tuple[F,F]; V=list[C]; M=tuple[int,int,int]
def c(r=0,i=0): return F(r),F(i)
def ca(a,b): return a[0]+b[0],a[1]+b[1]
def cm(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def cs(r,a): return r*a[0],r*a[1]
def cc(a): return a[0],-a[1]
def mi(a): return a[1],-a[0]
def va(a,b): return [ca(x,y) for x,y in zip(a,b,strict=True)]
def vs(z,v): return [cm(z,x) for x in v]
def md(k,v):
 t=c()
 for n,x in zip(k,v,strict=True): t=ca(t,cs(F(n),x))
 return t
def hp(v,w):
 t=c()
 for x,y in zip(v,w,strict=True): t=ca(t,cm(cc(x),y))
 return t
def n2(k): return sum(x*x for x in k)
def leray(k,v):
 r=md(k,v); return [ca(x,cs(F(-a,n2(k)),r)) for a,x in zip(k,v,strict=True)]
def curl(k,v):
 x,y,z=k;a,b,d=v
 q=[(y*d[0]-z*b[0],y*d[1]-z*b[1]),(z*a[0]-x*d[0],z*a[1]-x*d[1]),(x*b[0]-y*a[0],x*b[1]-y*a[1])]
 return [(-e[1],e[0]) for e in q]
def neg(k): return tuple(-x for x in k)
P=(-1,0,3);Q=(2,-3,-3);K=(1,-3,0); POS=(P,Q,K)
U=(c(1),c(0,1),c(-1),c(0,-1))
BASE={P:[c(3,3),c(-3,-3),c(1,1)],Q:[c(-3),c(),c(-2)],K:[c(3,-3),c(1,-1),c()]}
def state(ph=(0,0,0),amp=(1,1,1)):
 u={}
 for k,j,a in zip(POS,ph,amp,strict=True):
  v=vs(U[j],[cs(F(a),x) for x in BASE[k]]);u[k]=v;u[neg(k)]=[cc(x) for x in v]
 return u
def triads(u):
 ms=tuple(u);s=set(ms);return [(p,tuple(k[i]-p[i] for i in range(3)),k) for k in ms for p in ms if tuple(k[i]-p[i] for i in range(3)) in s]
def nt(u,k,p,q): return [mi(x) for x in leray(k,vs(md(q,u[p]),u[q]))]
def nonlinear(u):
 out={}
 for k in u:
  raw=[c(),c(),c()]
  for p,q,o in triads(u):
   if o==k: raw=va(raw,vs(md(q,u[p]),u[q]))
  out[k]=[mi(x) for x in leray(k,raw)]
 return out
def metrics(u):
 N=nonlinear(u); norms={k:hp(v,v)[0] for k,v in u.items()};E=F(1,2)*sum(norms.values());D=sum(n2(k)*norms[k] for k in u)
 A=sum((1+n2(k))**3*n2(k)*norms[k] for k in u);B=2*E*D
 C0=sum((1+n2(k))**3*hp(u[k],N[k])[0] for k in u)
 L={k:hp(u[k],curl(k,N[k]))[0] for k in u};assert sum(L.values())==0
 return A,B,C0,L

# Q(sqrt(10),sqrt(22)) basis 1,a,b,ab.
Z=(F(0),)*4; A10=(F(0),F(1),F(0),F(0)); A22=(F(0),F(0),F(1),F(0))
def b(x=0): return (F(x),F(0),F(0),F(0))
def ba(x,y): return tuple(x[i]+y[i] for i in range(4))
def bn(x): return tuple(-v for v in x)
def bs(r,x): return tuple(r*v for v in x)
def bm(x,y):
 o=[F(0)]*4
 for i,xi in enumerate(x):
  for j,yj in enumerate(y):
   aa=(i&1)+(j&1);bb=((i>>1)&1)+((j>>1)&1);v=xi*yj
   if aa==2:v*=10;aa=0
   if bb==2:v*=22;bb=0
   o[aa|(bb<<1)]+=v
 return tuple(o)
def ac(r=Z,i=Z): return r,i
def aca(x,y): return ba(x[0],y[0]),ba(x[1],y[1])
def acn(x): return bn(x[0]),bn(x[1])
def acm(x,y): return ba(bm(x[0],y[0]),bn(bm(x[1],y[1]))),ba(bm(x[0],y[1]),bm(x[1],y[0]))
def acc(x): return x[0],bn(x[1])
def acs(r,x): return bs(r,x[0]),bs(r,x[1])
def acmi(x): return x[1],bn(x[0])
def avs(z,v): return [acm(z,x) for x in v]
def amd(k,v):
 t=ac()
 for n,x in zip(k,v,strict=True):t=aca(t,acs(F(n),x))
 return t
def ahp(v,w):
 t=ac()
 for x,y in zip(v,w,strict=True):t=aca(t,acm(acc(x),y))
 return t
def aleray(k,v):
 r=amd(k,v);return [aca(x,acs(F(-a,n2(k)),r)) for a,x in zip(k,v,strict=True)]
def acurl(k,v):
 x,y,z=k;a,bv,d=v;q=[aca(acs(F(y),d),acn(acs(F(z),bv))),aca(acs(F(z),a),acn(acs(F(x),d))),aca(acs(F(x),bv),acn(acs(F(y),a)))]
 return [acmi(acn(e)) for e in q]
def ainv(k): return bs(F(1,10),A10) if n2(k)==10 else bs(F(1,22),A22)
def aproj(k,v,s): return [acs(F(1,2),aca(x,acm(ac(bs(F(s),ainv(k))),y))) for x,y in zip(v,acurl(k,v),strict=True)]
def hrow(u,k,p,q,sp,sq,sk):
 au={m:[ac(b(x[0]),b(x[1])) for x in v] for m,v in u.items()};up=aproj(p,au[p],sp);uq=aproj(q,au[q],sq);uk=aproj(k,au[k],sk)
 N=[acmi(x) for x in aleray(k,avs(amd(q,up),uq))];T=ahp(uk,N);root=A10 if n2(k)==10 else A22
 return T,bs(F(2*sk),bm(root,T[0]))
def ftxt(x):return str(x.numerator) if x.denominator==1 else f"{x.numerator}/{x.denominator}"
def bj(x):return {"1":ftxt(x[0]),"sqrt10":ftxt(x[1]),"sqrt22":ftxt(x[2]),"sqrt220":ftxt(x[3])}
def geom(p,q,k):return "near" if max(n2(p),n2(q),n2(k))<=4*min(n2(p),n2(q),n2(k)) else "separated"
def symbols():
 out=[]
 for j in (1,2,4,8,16,32,64):
  out += [(f"lowPass-{j}",lambda n,j=j:F(j,j+n)),(f"highPass-{j}",lambda n,j=j:F(n,j+n)),(f"smoothWindow-{j}",lambda n,j=j:F(j*n,(j+n)**2)),(f"dyadicBand-{j}",lambda n,j=j:F(2*j,2*j+n)-F(j,j+n))]
 return out

def run():
 u=state();ts=triads(u);assert len(ts)==12 and tuple(P[i]+Q[i] for i in range(3))==K
 for k,v in u.items():assert md(k,v)==c() and hp(v,curl(k,v))==c() and u[neg(k)]==[cc(x) for x in v]
 rows=[]
 for p,q,k in ts:
  x=nt(u,k,p,q);l=hp(x,curl(k,u[k]));r=hp(u[k],curl(k,x));assert l[0]==r[0]==0 and ca(l,r)==c()
  hs=[];total=Z;phase=False
  for sp,sq,sk in product((1,-1),repeat=3):
   T,d=hrow(u,k,p,q,sp,sq,sk);total=ba(total,d);phase|=T[1]!=Z;hs.append({"signs":[sp,sq,sk],"transfer":{"real":bj(T[0]),"imag":bj(T[1])},"chainReal":bj(d)})
  assert total==Z and phase;rows.append({"p":p,"q":q,"k":k,"geometry":geom(p,q,k),"leftImag":ftxt(l[1]),"rightImag":ftxt(r[1]),"resolved":hs})
 A0,B0,C0,L=metrics(u);gap=C0*C0-4*A0*B0;assert (A0,B0,abs(C0),gap)==(8503484,245944,6111504,28984957666432) and all(v==0 for v in L.values())
 fs=[]
 for name,chi in symbols():
  corr=sum(chi(n2(k))*v for k,v in L.items());assert corr==0
  for s,e in product((-1,1),range(8)):assert (C0+s*e*corr)**2-4*A0*B0==gap
  fs.append({"name":name,"chi10":ftxt(chi(10)),"chi22":ftxt(chi(22)),"correction":"0"})
 variants=dangerous=safeFlux=badFlux=0;samples=[]
 for ph in product(range(4),repeat=3):
  for amp in product((1,2),repeat=3):
   variants+=1;a,b0,c0,l=metrics(state(ph,amp));g=c0*c0-4*a*b0;nz=any(l.values())
   if g>0:dangerous+=1;badFlux+=int(nz);assert not nz
   elif nz:safeFlux+=1
   if len(samples)<16 and (g>0 or nz):samples.append({"phase":ph,"amplitude":amp,"C":ftxt(c0),"gap":ftxt(g),"localized":[ftxt(l[k]) for k in POS]})
 assert (variants,dangerous,badFlux,safeFlux)==(512,256,0,256)
 return {"witness":{"A":ftxt(A0),"B":ftxt(B0),"C":ftxt(C0),"gap":ftxt(gap)},"orderedRows":rows,"fixedSymbols":fs,"balancedFamily":{"variants":variants,"dangerous":dangerous,"dangerousWithNonzeroLocalized":badFlux,"safeWithNonzeroLocalized":safeFlux,"samples":samples},"decision":{"scalarLocalizedHelicity":False,"triadPhaseCarrier":True}}
def main():
 p=argparse.ArgumentParser();p.add_argument("--json",type=Path);a=p.parse_args();r=run()
 if a.json:a.json.write_text(json.dumps(r,indent=2,sort_keys=True)+"\n",encoding="utf-8")
 print("verified exact localized-helicity reconnaissance: 12 ordered triads, 96 helical rows, 28 fixed symbols, 512 balanced variants; all 256 dangerous variants have zero scalar-localized correction; triad phase remains nontrivial")
if __name__=="__main__":main()

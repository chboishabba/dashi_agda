#!/usr/bin/env python3
"""Finite Hatcher C3 / binary-icosahedral SU2 gauge simulator.

Exact Q(phi) 120-unit quaternion group and compatible commutator
labels; floating point ONLY for Gaussian control errors and shot
readout. This is not a manufactured wild space or lab observation.
Sources: Alexander (1924), Hatcher Ex 2B.2; Klein/Hamilton 2I.
"""
import argparse,csv,json,math,random
from fractions import Fraction as F
from functools import lru_cache
from itertools import product,permutations
from pathlib import Path

Z=(F(0),F(0));O=(F(1),F(0));H=(F(1,2),F(0))
PHI=(F(0),F(1));INVPHI=(F(-1),F(1))
def add(x,y):return x[0]+y[0],x[1]+y[1]
def neg(x):return -x[0],-x[1]
def sub(x,y):return add(x,neg(y))
def scale(x,k):return k*x[0],k*x[1]
@lru_cache(maxsize=3000)
def fm(x,y):
 a,b=x;c,d=y
 return a*c+b*d,a*d+b*c+b*d
ID=(O,Z,Z,Z);NEG=(neg(O),Z,Z,Z)
@lru_cache(maxsize=25000)
def mul(q,r):
 a,b,c,d=q;e,f,g,h=r
 return (sub(sub(sub(fm(a,e),fm(b,f)),fm(c,g)),fm(d,h)),
   add(add(sub(fm(a,f),fm(d,g)),fm(b,e)),fm(c,h)),
   add(add(sub(fm(a,g),fm(b,h)),fm(c,e)),fm(d,f)),
   add(add(sub(fm(a,h),fm(c,f)),fm(b,g)),fm(d,e)))
def inv(q):return q[0],neg(q[1]),neg(q[2]),neg(q[3])
def powq(q,n):
 a=ID
 for _ in range(n):a=mul(a,q)
 return a
def comm(a,b):return mul(mul(mul(a,b),inv(a)),inv(b))
def even(p):return sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))%2==0
def icosians():
 s=set()
 for i in range(4):
  for sign in (-1,1):
   x=[Z]*4;x[i]=scale(O,F(sign));s.add(tuple(x))
 for ss in product((-1,1),repeat=4):
  s.add(tuple(scale(H,F(sign)) for sign in ss))
 for p in permutations(range(4)):
  if not even(p):continue
  for ss in product((-1,1),repeat=3):
   q=[Z,scale(H,F(ss[0])),scale(PHI,F(ss[1],2)),scale(INVPHI,F(ss[2],2))]
   s.add(tuple(q[i] for i in p))
 assert len(s)==120
 return tuple(sorted(s))
def generated(gs):
 done={ID};todo=[ID]
 while todo:
  x=todo.pop()
  for g in gs:
   y=mul(x,g)
   if y not in done:done.add(y);todo.append(y)
 return done
def build():
 group=icosians();q=(H,H,H,H)
 for a in group:
  assert mul(a,inv(a))==ID
  for b in group:assert mul(a,b) in group
 assert powq(q,3)==NEG and powq(q,6)==ID
 sec={};rootpair=None
 for a in group:
  for b in group:
   c=comm(a,b);sec.setdefault(c,(a,b))
   if c==q and rootpair is None and len(generated((a,b)))==120:rootpair=a,b
 assert len(sec)==120 and rootpair
 # Evaluate Q8 one-stage sign and verify the derived subgroup cannot
 # generate noncentral child values at the next refinement.
 I=(Z,O,Z,Z);J=(Z,Z,O,Z)
 assert comm(I,J)==NEG
 K=mul(I,J)
 q8={ID,NEG,I,inv(I),J,inv(J),K,inv(K)}
 assert len(q8)==8 and {comm(a,b) for a in q8 for b in q8}=={ID,NEG}
 return group,q,sec,rootpair
def tower(q,sec,rootpair,depth):
 levels=[{():q}]
 for d in range(depth):
  nxt={}
  for addr,x in levels[-1].items():
   a,b=rootpair if d==0 else sec[x]
   assert comm(a,b)==x
   nxt[addr+(0,)]=a;nxt[addr+(1,)]=b
  levels.append(nxt)
 return levels
def expand(word):
 ans=[]
 for l in word:
  a=2*(abs(l)-1)+1;b=a+1
  ans.extend((a,b,-a,-b) if l>0 else (b,a,-b,-a))
 return tuple(ans)
def holonomy(word,labels):
 z=ID
 for l in word:
  x=labels[abs(l)-1]
  z=mul(z,x if l>0 else inv(x))
 return z
def real(x):return float(x[0])+float(x[1])*(1+math.sqrt(5))/2
def tofloat(q):return tuple(real(x) for x in q)
def fmul(a,b):
 w,x,y,z=a;W,X,Y,Z=b
 return w*W-x*X-y*Y-z*Z,w*X+x*W+y*Z-z*Y,w*Y-x*Z+y*W+z*X,w*Z+x*Y-y*X+z*W
def noise(rng,sigma):
 if sigma==0:return 1.,0.,0.,0.
 theta=math.radians(rng.gauss(0,sigma))
 xyz=[rng.gauss(0,1) for _ in range(3)]
 norm=math.sqrt(sum(a*a for a in xyz))
 return (math.cos(theta/2),)+tuple(math.sin(theta/2)*a/norm for a in xyz)
def noisy_word(word,labels,rng,sigma):
 p=(1.,0.,0.,0.)
 for l in word:
  q=labels[abs(l)-1]
  gate=q if l>0 else (q[0],-q[1],-q[2],-q[3])
  p=fmul(p,fmul(noise(rng,sigma),gate))
 return p
def simulate(depth,trials,shots,sigma,seed):
 assert 0<=depth<=7 and trials>0 and shots>0 and sigma>=0
 G,q,sec,pair=build();levels=tower(q,sec,pair,depth)
 rng=random.Random(seed);out=[];word=(1,)
 for d in range(depth+1):
  labels=[levels[d][tuple((j>>k)&1 for k in range(d-1,-1,-1))]
          for j in range(2**d)]
  assert holonomy(word,labels)==q
  assert powq(holonomy(word,labels),3)==NEG
  fl=[tofloat(v) for v in labels]
  noisy=[];observed=[]
  for _ in range(trials):
   m=(1.,0.,0.,0.)
   for _ in range(3):m=fmul(m,noisy_word(word,fl,rng,sigma))
   t=max(-1.,min(1.,m[0]));noisy.append(t)
   hits=sum(rng.random()<(1+t)/2 for _ in range(shots))
   observed.append(2*hits/shots-1)
  avg=sum(observed)/trials
  sd=math.sqrt(sum((x-avg)**2 for x in observed)/trials)
  out.append({'depth':d,'generators_per_sector':2**d,'three_sector_generators':3*2**d,
              'loop_gates':3*len(word),'ideal_halftrace':-1.,
              'noisy_halftrace':sum(noisy)/trials,'observed_halftrace':avg,
              'observed_sd':sd,'shots_per_trial':shots,'trials':trials})
  word=expand(word)
 return {'meta':{'seed':seed,'noise_deg':sigma,'finite_binary_icosahedral_order':len(G),
         'all_elements_commutators':len(sec)==len(G),
         'geometric_flatness_or_lab_measurement_claim':False},
         'controls':{'commuting_U1_halftrace':1.,'Q8_one_step_halftrace':-1.,
                     'Q8_supports_full_recursion':False},'rows':out}
def main():
 p=argparse.ArgumentParser()
 p.add_argument('--max-depth',type=int,default=4)
 p.add_argument('--trials',type=int,default=40)
 p.add_argument('--shots',type=int,default=512)
 p.add_argument('--noise-deg',type=float,default=1.)
 p.add_argument('--seed',type=int,default=20261025)
 p.add_argument('--json',type=Path)
 p.add_argument('--csv',type=Path)
 a=p.parse_args();x=simulate(a.max_depth,a.trials,a.shots,a.noise_deg,a.seed)
 for r in x['rows']:
  print('depth={depth} gates={loop_gates} ideal={ideal_halftrace:+.3f} noisy={noisy_halftrace:+.4f} observed={observed_halftrace:+.4f}'.format(**r))
 if a.json:a.json.write_text(json.dumps(x,indent=2)+'\n')
 if a.csv:
  with a.csv.open('w',newline='') as f:
   wr=csv.DictWriter(f,fieldnames=x['rows'][0].keys());wr.writeheader();wr.writerows(x['rows'])
 print('SIMULATION ONLY; finite group assignments do not measure a wild-space connection')
if __name__=='__main__':main()

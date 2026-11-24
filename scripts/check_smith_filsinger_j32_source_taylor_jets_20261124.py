"""Exact interval Taylor jets for source J31 with analytic rational capacitor.
Remainder by derivative coefficients evaluated on a validated whole-time tube.
No floating-point estimates in mathematical inequalities.
"""
from fractions import Fraction as F
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s
I=s.I
class Jet:
 __slots__=('c',)
 NN=6
 def __init__(self,a):
  if isinstance(a,Jet):self.c=a.c[:];return
  self.c=[I(a)]+[I(0)]*self.NN
 @classmethod
 def fromcoeff(cls,cs):
  z=cls(0);z.c=cs;return z
 def __add__(self,z):
  z=Jet(z);return Jet.fromcoeff([a+b for a,b in zip(self.c,z.c)])
 __radd__=__add__
 def __neg__(self):return Jet.fromcoeff([-a for a in self.c])
 def __sub__(self,z):return self+-Jet(z)
 def __rsub__(self,z):return Jet(z)+-self
 def __mul__(self,z):
  z=Jet(z)
  return Jet.fromcoeff([sum((self.c[i]*z.c[n-i] for i in range(n+1)),I(0)) for n in range(self.NN+1)])
 __rmul__=__mul__
 def __truediv__(self,z):
  z=Jet(z);q=[]
  for n in range(self.NN+1):
   a=self.c[n]-sum((z.c[i]*q[n-i] for i in range(1,n+1)),I(0))
   q.append(a/z.c[0])
  return Jet.fromcoeff(q)
 def __rtruediv__(self,z):return Jet(z)/self

def deriv_coeff(start_x,sn,co,mode,order=6):
 """Coefficients x_k=x^{(k)}/k!, for k<=order, at a real state/time
 in initial intervals, by purely algebraic differential recurrence.
 """
 Jet.NN=order
 xs=[Jet(x) for x in start_x];ss=Jet(sn);cc=Jet(co)
 p=s.PARAM
 U,V,chi=mode
 def vector():
  i,j,u,v,b,q,r,ih,cap=xs
  ju=(u-b-p['Vd'])/p['Rd'] if U else Jet(0)
  jv=(v-b-p['Vd'])/p['Rd'] if V else Jet(0)
  a=-p['R1']*i;bb=u-v-p['R2']*j
  left=-j-ju+p['k']*q+p['kh']*ih
  right=j-jv
  return [
   (p['L2']*a-p['M']*bb)/F('2.64'),
   (-p['M']*a+p['L1']*bb)/F('2.64'),
   (F('1.55')*left+right)/F('1.17'),
   (left+F('1.4')*right)/F('1.17'),
   (ju+jv-p['Gbleed']*b-chi*ih)/p['Cb'],
   p['omega']*r-p['gamma']*q-p['k']*u/F(2)+Jet(s.K)*cc,
   -p['omega']*q-p['gamma']*r-Jet(s.K)*ss,
   (chi*b-cap-(p['Rcoil']+chi*p['Rgap'])*ih-p['kh']*u)/p['Lh'],
   (ih-p['Gload']*cap)/(p['Ch']*(1+F('1.5')*cap*cap))]
 for n in range(order):
  ans=vector()
  for j in range(9):xs[j].c[n+1]=ans[j].c[n]/F(n+1)
  ss.c[n+1]=p['omega']*cc.c[n]/F(n+1)
  cc.c[n+1]=-p['omega']*ss.c[n]/F(n+1)
 return [x.c[:] for x in xs]

def taylor_point_with_remainder(point,t0,h,mode,tube,window,order=6):
 a,b=s.phase(I(t0))
 cpoint=deriv_coeff([I(x) for x in point],a,b,mode,order)
 alpha,beta=s.phase(window)
 ctube=deriv_coeff(tube,alpha,beta,mode,order+1)
 center=[];tail=[]
 for i in range(9):
  z=sum((cpoint[i][j]*h**j for j in range(order+1)),I(0))
  r=s.up(ctube[i][order+1].mag()*h**(order+1))
  center.append(z+I(-r,r))
  tail.append(r)
 return center,tail

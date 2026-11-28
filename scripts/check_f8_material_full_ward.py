"""Independent variable-FRW Ward replay for the material principal and lower-order response."""
import sympy as S
from itertools import product
t,x,y,z=S.symbols('t x y z',real=True,positive=True);coords=(t,x,y,z);b=1/t
K=S.Function('K')(t);w=S.Function('w')(t);rho=S.Function('rho')(t);p=K+w-rho
u=S.Function('u')(t,x);v=S.Matrix([S.Function('v'+str(i))(t,x) for i in range(3)])
l=S.Function('l')(t,x);m=S.Matrix([S.Function('m'+str(i))(t,x) for i in range(3)]);J=S.Matrix(3,3,lambda i,j:S.Function('J%d%d'%(min(i,j),max(i,j)))(t,x)); tr=S.trace(J)
g=S.diag(-1,t*t,t*t,t*t); gi=g.inv(); h=S.diag(l,t*t*J);h[0,1:]=t*m.T;h[1:,0]=t*m
D=b*v[0].diff(x)-tr/2; L=u.diff(t)+l/2;vel=v.diff(t)-b*v;grad=S.Matrix([b*u.diff(q) for q in coords[1:]])
dr=w*D+K*L-3*b*K*u;dp=w*D/3+K*L+(K.diff(t)+3*b*K)*u
T=S.diag(-dr,dp*S.eye(3));T[0,1:]=(w*(m-vel)-K*grad).T;T[1:,0]=w*vel+K*(m+grad)
Q=S.diag(1,t,t,t); T=Q.inv()*T*Q; T0=S.diag(-rho,p,p,p)
ix=range(4); G={}; dG={}; di=-gi*h*gi
for a,i,j in product(ix,repeat=3):
 G[a,i,j]=sum(gi[a,k]*(g[k,j].diff(coords[i])+g[k,i].diff(coords[j])-g[i,j].diff(coords[k]))/2 for k in ix)
 dG[a,i,j]=sum((di[a,k]*(g[k,j].diff(coords[i])+g[k,i].diff(coords[j])-g[i,j].diff(coords[k]))+gi[a,k]*(h[k,j].diff(coords[i])+h[k,i].diff(coords[j])-h[i,j].diff(coords[k])))/2 for k in ix)
for nu in ix:
 res=sum(T[a,nu].diff(coords[a]) for a in ix)+sum(G[a,a,c]*T[c,nu]-G[c,a,nu]*T[a,c]+dG[a,a,c]*T0[c,nu]-dG[c,a,nu]*T0[a,c] for a,c in product(ix,repeat=2))
 C4=-l.diff(t)/2+b*m[0].diff(x)-tr.diff(t)/2
 if nu==0: expected=-K*(u.diff(t,2)+(3*b+K.diff(t)/K)*u.diff(t)-b*b*u.diff(x,2)+3*b*b*u-C4+(3*b+K.diff(t)/(2*K))*l)
 else:
  i=nu-1; expected=t*w*(m[i].diff(t)-v[i].diff(t,2)+b*v[i].diff(t)-b*b*v[i]+b*(b*v[0].diff(x)/3-tr/6-l/2).diff(coords[nu]))
 assert S.simplify((res-expected).subs(w.diff(t),-4*b*w))==0
print("four full variable-FRW Ward components PASS (one spatial dependence, three displacement components)")

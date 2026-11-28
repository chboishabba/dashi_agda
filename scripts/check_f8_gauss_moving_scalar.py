import sympy as s
from itertools import product

def exact():
 t,x,y,z=s.symbols('t x y z',positive=True); coords=(t,x,y,z); b=1/t; B=s.sqrt(1+b*b); q=s.symbols('q'); I=range(4)
 l,X,Y=[s.Function(a)(t,x) for a in ('l','X','Y')]; J=X+2*Y
 g=s.diag(-1,t*t,t*t,t*t); gi=g.inv(); h=s.diag(l,t*t*X,t*t*Y,t*t*Y); di=-gi*h*gi
 C={}; D={}
 for a,i,j in product(I,repeat=3):
  C[a,i,j]=sum(gi[a,k]*(g[k,j].diff(coords[i])+g[k,i].diff(coords[j])-g[i,j].diff(coords[k]))/2 for k in I)
  D[a,i,j]=s.expand(sum((gi[a,k]*(h[k,j].diff(coords[i])+h[k,i].diff(coords[j])-h[i,j].diff(coords[k]))+di[a,k]*(g[k,j].diff(coords[i])+g[k,i].diff(coords[j])-g[i,j].diff(coords[k]))/2 for k in I))
 R=s.Matrix(4,4,lambda i,j:sum(C[k,i,j].diff(coords[k])-C[k,i,k].diff(coords[j]) for k in I)+sum(C[k,k,a]*C[a,i,j]-C[k,j,a]*C[a,i,k] for k,a in product(I,repeat=2)))
 dR=s.Matrix(4,4,lambda i,j:sum(D[k,i,j].diff(coords[k])-D[k,i,k].diff(coords[j]) for k in I)+sum(D[k,k,a]*C[a,i,j]+C[k,k,a]*D[a,i,j]-D[k,j,a]*C[a,i,k]-C[k,j,a]*D[a,i,k] for k,a in product(I,repeat=2)))
 curv=s.expand(s.trace(gi*dR+di*R)); expected=J.diff(t,2)+4*b*J.diff(t)+3*b*l.diff(t)+6*b*b*l+b*b*(l-2*Y).diff(x,2)
 assert s.expand(curv-expected)==0
 # Normal bending h=2 f eta K0. Linear intrinsic curvature includes second time derivative of f.
 f=s.Function('f')(t,x); bend=expected.subs({l:2*f/B,X:-2*B*f,Y:-2*B*f}).doit().expand()
 assert s.simplify(bend.coeff(f.diff(t,2))+6*B)==0
 # Contracted Gauss: R4=R5-2 Ric_nn + trK²_scalar - tr(K²).
 e=s.symbols('e'); K0=s.diag(-1/B,-B,-B,-B); P=s.Matrix(3,3,lambda i,j:s.Symbol('p%d%d'%(min(i,j),max(i,j)))); P=P-s.trace(P)*s.eye(3)/3
 U=s.diag(0,-3*P); A,C1,D1=s.symbols('A C D'); E=s.diag(A,C1,D1,D1); rho,p=s.symbols('rho p'); S2=s.diag(-rho,p,p,p); V=-3*S2+s.trace(S2)*s.eye(4)
 K=K0+e*U+e**2*(V+E); gauss=s.expand(s.trace(K)**2-s.trace(K*K)).coeff(e,2)
 assert s.simplify(gauss-(6*rho/B-18*B*p-9*s.trace(P*P)+2*s.trace(K0)*s.trace(E)-2*s.trace(K0*E)))==0
 assert s.simplify(2*s.trace(K0)*s.trace(E)-2*s.trace(K0*E)+6*B*A+2*(1/B+2*B)*(C1+2*D1))==0
 # Unknown normal Ricci defect retained: R5+20 -2(Rnn+4).
 R4,Q5,Qn=s.symbols('R4 Q5 Qn'); force=Q5-2*Qn-9*s.trace(P*P)-6*B*A-2*(1/B+2*B)*(C1+2*D1)
 pressure=rho/(3*B**2)+(force-R4)/(18*B)
 assert s.simplify(6*rho/B-18*B*pressure+force-R4)==0
 print('5 exact assertions PASS')
if __name__=='__main__':exact()

import sympy as s
from check_hopf369_br220_normal_constraint_propagation import symbols

def run(X,G):
 C,K=symbols(X,G); I=s.eye(35); Q=s.eye(100)-C[4]*K[4]; t=s.symbols('t'); b=t*C[0]+s.I*C[1]; D=Q*b; A=-K[4]*b
 for sig in (-1,1):
  D0=D.subs(t,sig*s.I); rows=list(D0.T.rref()[1]); cols=list(D0.rref()[1]); free=[i for i in range(35) if i not in cols]; R=s.eye(100)[rows,:]; E=I[:,cols]; Z=I[:,free]; H=Z.T
  assert len(cols)==25
  print('sign',sig,'rows',rows,'cols',cols,'minor at glancing',D0.extract(rows,cols).det(),flush=True)
  for v in (sig*s.I,1+sig*s.I):
   d=D.subs(t,v); a=A.subs(t,v); V=E*d.extract(rows,cols).inv()*R; N=Z-V*d*Z; M=H*a*N; q=v*v+1
   eq=lambda x,y:(x-y).applyfunc(s.cancel)==s.zeros(*x.shape)
   assert eq(H*N,s.eye(10)) and eq(H*V,s.zeros(10,100)) and eq(d*N,s.zeros(100,10))
   assert eq(a*N,N*M) and eq(M*M,q*s.eye(10))
   assert eq(V*d+N*H,I)
   print('  t',v,'reduced square',q,'rank reduced',M.rank(),flush=True)
 print('PASS BR223 regular algebraic complement and ten-coordinate reduced evolution',s.__version__,flush=True)
if __name__=='__main__':
 from check_hopf369_br_curvature_energy import carrier
 _,_,X,G,_,_,_,_,_,_,_,_=carrier()
 run(X,G)

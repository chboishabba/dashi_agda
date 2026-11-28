import sympy as s
from itertools import product

def exact():
 t,x,y,w=s.symbols('t x y w',positive=True); X=(t,x,y,w); b=1/t
 H=s.Matrix([[0,t*w,t*y],[t*w,t*x,0],[t*y,0,-t*x]])
 E=s.Matrix([[x,y,w],[y,t,-x],[w,-x,-x-t]])
 assert H.trace()==E.trace()==0
 g=s.diag(-1,t*t*s.eye(3)); h=s.diag(0,t*t*H); gi=g.inv(); di=-gi*h*gi
 ix=range(4)
 C={(a,i,j):s.expand(sum((gi[a,k]*(h[k,j].diff(X[i])+h[k,i].diff(X[j])-h[i,j].diff(X[k]))+di[a,k]*(g[k,j].diff(X[i])+g[k,i].diff(X[j])-g[i,j].diff(X[k])))/2 for k in ix)) for a,i,j in product(ix,repeat=3)}
 E1=s.diag(0,E)
 D=s.Matrix([s.expand(sum(C[a,a,c]*E1[c,j]-C[c,a,j]*E1[a,c] for a,c in product(ix,repeat=2))) for j in ix])
 expected=s.Matrix([-s.trace(E*H.diff(c))/2 for c in X])
 assert (D-expected).applyfunc(s.expand)==s.zeros(4,1)
 # E2 mixed residual need not be symmetric with respect to background if E1!=0.
 # g E2+h E1 symmetric => E2-E2^T=E H-H E for spatial block.
 skew=(E*H-H*E)/2
 assert skew.T==-skew
 assert ((skew+H*E)-(skew+H*E).T).applyfunc(s.expand)==s.zeros(3)
 # The symmetric effective residual is E2-skew; retain skew divergence in source.
 skewdiv=s.Matrix([0]+[sum(skew[i,j].diff(X[i+1]) for i in range(3)) for j in range(3)])
 assert s.expand(sum(skewdiv[i+1].diff(X[i+1]) for i in range(3)))==0
 # normal projection of lower bulk Ricci residual at wall, coordinates T,x,y,w,z.
 B=s.sqrt(1+b*b); n=s.Matrix([-b,0,0,0,B])*b; e=s.Matrix([B,0,0,0,-b])*b
 Q=s.Matrix(5,5,lambda i,j:s.Symbol('Q%d%d'%(min(i,j),max(i,j))))
 assert s.simplify((n.T*Q*e)[0]-b*b*((B*B+b*b)*Q[0,4]-b*B*(Q[0,0]+Q[4,4])))==0
 for i in range(1,4):
  assert s.expand((n.T*Q*(b*s.eye(5)[:,i]))[0]-b*b*(-b*Q[0,i]+B*Q[4,i]))==0
 # Off-shell wall defect correction disappears for exact first-order Israel.
 print('9 assertions PASS: Ward/Codazzi first-order defect, skew transport, normal projection')
if __name__=='__main__': exact()

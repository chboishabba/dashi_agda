"""Original full Cartesian scalar first-order reference, exact symbol/flux checks.
Ginoux--Murro theorem application is analytic, not a local PDE kernel run.
"""
import json
import sympy as s

def check():
    v,tau,eta,x1,x2,x3=s.symbols('v tau eta x1 x2 x3',real=True);sig=1-v*v
    # State (U,W,N,X1,X2,X3); multiply the evolution by H.
    H=s.diag(1,1,sig,1,1,1);Ay=s.zeros(6);Ay[1,1]=2*v;Ay[1,2]=sig;Ay[2,1]=1
    Ax=[]
    for i in range(3):
        a=s.zeros(6);a[1,3+i]=a[3+i,1]=1;Ax.append(a)
    for a in [Ay,*Ax]:assert H*a==(H*a).T
    symbol=H*(tau*s.eye(6)-eta*Ay-sum((x*a for x,a in zip((x1,x2,x3),Ax)),s.zeros(6)))
    Q=tau**2-2*v*tau*eta-sig*eta**2-x1*x1-x2*x2-x3*x3
    assert s.factor(symbol.det()-sig*tau**4*Q)==0
    # Schur complement after isolating W; tau>0 and Q>0 by timelike covector.
    idx=[0,2,3,4,5];C=symbol.extract(idx,idx);B=symbol.extract([1],idx)
    assert s.cancel(symbol[1,1]-(B*C.inv()*B.T)[0]-Q/tau)==0
    assert C==s.diag(tau,sig*tau,tau,tau,tau)
    # Outward conormal -dy, overall positive unit-normal multiplier omitted.
    normal=H*Ay;assert s.factor(normal.extract([1,2],[1,2]).det()+sig**2)==0
    U,W,N,X,Y,Z=s.symbols('U W N X Y Z',real=True);state=s.Matrix([U,W,N,X,Y,Z]);G=v*W+sig*N
    assert s.expand((state.T*normal*state)[0]-2*W*G)==0
    basis=s.Matrix.hstack(s.eye(6)[:,0],s.Matrix([0,sig,-v,0,0,0]),s.eye(6)[:,3],s.eye(6)[:,4],s.eye(6)[:,5]);assert basis.T*normal*basis==s.zeros(5)
    assert basis.rank()==5
    # Exact moving-coordinate principal metric and normal.
    g=s.Matrix([[-sig,v,0,0,0],[v,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]])
    ginv=s.Matrix([[-1,v,0,0,0],[v,sig,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]])
    assert s.simplify(g*ginv-s.eye(5))==s.zeros(5)
    xi=s.Matrix([tau,eta,x1,x2,x3]);assert s.expand((xi.T*ginv*xi)[0]+Q)==0
    # Constraint time derivative vanishes in the exact first-order system.
    T,y,x=s.symbols('T y x');u=s.Function('u')(T,y,x);w=s.Function('w')(T,y,x);n=s.Function('n')(T,y,x);a=s.Function('a')(T,y,x)
    assert s.diff(n-s.diff(u,y),T).subs({s.diff(n,T):s.diff(w,y),s.diff(u,T,y):s.diff(w,y)})==0
    assert s.diff(a-s.diff(u,x),T).subs({s.diff(a,T):s.diff(w,x),s.diff(u,T,x):s.diff(w,x)})==0
    q=s.Function('q')(T,x);bump=s.Function('chi')(y);lift=y*bump*q/sig
    assert s.simplify((v*s.diff(lift,T)+sig*s.diff(lift,y)).subs(y,0).subs(bump.subs(y,0),1)-q)==0
    return dict(symmetric_principal_matrices=4,characteristic_polynomial=True,timelike_schur_complement=True,boundary_inertia=[1,1,4],admissible_dimension=5,zero_flux=True,metric_inverse=True,gradient_constraint_types=2,inhomogeneous_wall_lift=True,scope='symbolic original scalar first-order weld; external smooth existence and causal support theorem application separate from numerical error and physical source')
if __name__=='__main__':print(json.dumps(check(),indent=2))

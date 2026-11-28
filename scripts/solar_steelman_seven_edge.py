"""Exact original graph charge/cycle lift on normalized Whitney shell.
Finite weighted copies of graph, not calibrated physical conductor width.
"""
import sympy as S
from itertools import permutations, combinations
from solar_steelman_whitney_lift import geometry, solve
from solar_spherical_whitney import shell_mesh

edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
Gp=S.zeros(7,6)
for k,(a,b) in enumerate(edges): Gp[k,a]=-1;Gp[k,b]=1
Dp=S.Matrix([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
assert Dp*Gp==S.zeros(2,6)

def run():
    M,N,G,C,D,loops=geometry();xyz,s,m,_=shell_mesh([1,1.5,2]);I=S.I
    # Embed all original graph edges on one octahedral layer, then average
    # two oriented whole copies under an octahedral rotation. Retain charge.
    p=next(p for p in permutations(range(6)) if all(p[a]//2!=p[b]//2 for a,b in edges))
    rot=[2,3,4,5,0,1]
    def trace(layer):
        V=S.zeros(6,G.cols);T=S.zeros(7,G.rows)
        for weight,perm in [(S.Rational(2,3),p),(S.Rational(1,3),[rot[j] for j in p])]:
            for j,v in enumerate(perm): V[j,layer*6+v]+=weight
            for j,(a,b) in enumerate(edges):
                u,v=layer*6+perm[a],layer*6+perm[b];T[j,m[1][tuple(sorted((u,v)))]]+=weight*(1 if u<v else -1)
        assert T*G==Gp*V and T.rank()==7
        return T,V
    mid,Vm=trace(1);inner,Vi=trace(0)
    # Exact orthogonal decomposition on original seven-dimensional port.
    P=Dp.T*(Dp*Dp.T).inv()*Dp;Q=S.eye(7)-P
    assert P*P==P and P.T==P and Gp.T*P==S.zeros(6,7) and Q.rank()==5 and P.rank()==2
    # Same actual shell field matrix; both bands retain all 15 port rows.
    T=loops[:1,:].col_join(mid).col_join(inner)
    assert T.rank()==15
    def transfer(w,source,receiver):
        K=C.T*N*C-w*w*M; A=solve(K,T.T);assert K*A==T.T
        X=w*T*A;assert X==X.T
        # Fixed unit source direction, all seven receiver currents allowed.
        x=receiver*X*source;R=(x.T*x)[0];assert R>0
        p=I*x/R
        # Independent solve of compensated full seven-port network.
        block=S.ones(1,1).row_join(-I*x.T).col_join((I*x).row_join(-R*S.eye(7)))
        f=solve(block,S.Matrix([2]+[0]*7));assert f==S.Matrix([1]).col_join(p)
        current=source-receiver.T*p;e=I*w*A*current;b=-C*e/(I*w);v=T*e
        assert (I*w*M*e-C.T*N*b-T.T*current).applyfunc(S.simplify)==S.zeros(M.rows,1)
        charge=G.T*M*e
        assert (I*w*charge-G.T*T.T*current).applyfunc(S.simplify)==S.zeros(G.cols,1)
        assert (D*b).applyfunc(S.simplify)==S.zeros(D.rows,1)
        assert S.simplify((p.H*(receiver*v))[0].as_real_imag()[0])==1
        assert S.simplify((source.T*v)[0].as_real_imag()[0])==1
        # Both cycle and charge sectors present, and periodic charge integral zero.
        assert P*p!=S.zeros(7,1) and Q*p!=S.zeros(7,1) and charge!=S.zeros(G.cols,1)
        assert S.simplify((p.H*(R*S.eye(7))*p)[0])==1
        print('band',w,'rank7 matched, reflection=0 useful=1 charge nonzero, cycle nonzero',flush=True)
        return p,R
    high=transfer(S.Integer(2),S.eye(15)[:,0],S.eye(15)[1:8,:])
    low=transfer(S.Integer(1),S.eye(15)[:,1],S.eye(15)[8:15,:])
    # Reciprocal piecewise constant cell-current map (same Whitney integral
    # as spherical_material_weld); test actual trace range, no new source.
    W=S.zeros(M.rows,3*len(s[3]))
    for k,t in enumerate(s[3]):
        a=S.Matrix([[S.Rational(float(v)) for v in xyz[j]] for j in t]);V=abs((a[1:,:]-S.ones(3,1)*a[0,:]).det())/6
        g=S.ones(4,1).row_join(a).inv()[1:,:]
        for i,j in combinations(range(4),2):W[m[1][(t[i],t[j])],3*k:3*k+3]=(V*(g[:,j]-g[:,i])/4).T
    # Find exact obstruction: null(W^T) tests whether port injection can
    # be produced by local piecewise constant material currents.
    null=W.T.nullspace();Z=S.Matrix.hstack(*null) if null else S.zeros(M.rows,0)
    residual=Z.T*T.T
    print('material map rank',M.rows-len(null),'trace obstruction rank',residual.rank(),flush=True)
    assert Z.T*W==S.zeros(Z.cols,W.cols)
    for name,p,receiver in [('high',high[0],mid),('low',low[0],inner)]:
        r=Z.T*receiver.T*p
        print(name,'material current range membership',r==S.zeros(Z.cols,1),flush=True)
    # Enrich with the minimum number of globally assembled Whitney current
    # basis directions. M is invertible, so Z^T M has full row rank.
    piv=(Z.T*M).rref()[1];assert len(piv)==Z.cols
    B=M[:,list(piv)];Wplus=W.row_join(B)
    assert Wplus.rank()==M.rows
    # Exact current representative via an independent column subset.
    cols=Wplus.rref()[1];Cw=Wplus[:,list(cols)]
    for p,receiver in [(high[0],mid),(low[0],inner)]:
        target=receiver.T*p;coeff=solve(Cw,target)
        assert (Cw*coeff-target).applyfunc(S.simplify)==S.zeros(M.rows,1)
    # Reciprocal work uses the same enriched map and its transpose.
    print('minimal enrichment',len(piv),'Whitney edge basis indices',piv,'rank',Wplus.rank(),flush=True)
    print('PASS exact enriched material injection, charge continuity, fixed-source matching; physical constitutive admission open')
if __name__=='__main__':run()

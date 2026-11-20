#!/usr/bin/env python3
"""S4b: exact conditional flux observers; no physiological calibration."""
from itertools import combinations
from sympy import Matrix, diag, eye, ones, zeros, symbols, exp, simplify, __version__
from reactive_pnp_369 import POINTS, BONDS


def check():
    # TransferStep order: packing, exocytosis, efflux, reuptake, C/E loss.
    T = Matrix([[-1,0,-1,1,-1,0],[1,-1,0,0,0,0],[0,1,1,-1,0,-1]])
    K = Matrix([[1,0,0],[1,0,0],[0,1,1],[1,1,0],[0,0,-1],[0,0,1]])
    assert T.rank()==3 and K.rank()==3 and T*K==zeros(3,3)
    p,r,f,u,lc,le = list(eye(6).row(i) for i in range(6))
    target = Matrix.vstack(r,f-u)
    gross = Matrix.vstack(r,f,u)
    assert (target*K).rank()==2 and (gross*K).rank()==3
    menu = dict(zip(('p','r','f','u','lC','lE','net'), (p,r,f,u,lc,le,f-u)))
    def panels(goal, n):
        out=[]
        for names in combinations(menu,n):
            Q=Matrix.vstack(*(menu[k] for k in names))*K
            if Q.col_join(goal*K).rank()==Q.rank():
                out.append(names)
        return out
    assert not panels(target,1) and not panels(gross,2)
    a,b=panels(target,2),panels(gross,3)
    assert ('r','lE') in a and ('r','f','u') in b
    # reaction and external exchange must already be accounted for.
    x=Matrix(symbols('p r f u lC lE')); delta=T*x
    assert simplify(delta[2]-(r*x)[0]+(le*x)[0]-( (f-u)*x )[0])==0
    # Gross efflux/reuptake remain invisible even with r and E loss observed.
    assert Matrix.vstack(T,r,le)*K[:,1]==zeros(5,1) and (gross*K[:,1])!=zeros(3,1)
    # Native SG outward sign: J=-W B^T y, y=c exp(psi), fixed W positive.
    A,D,h,pa,pb,ca,cb=symbols('A D h pa pb ca cb', positive=True)
    du=pb-pa
    w=D/h*A*exp(-pa)
    assert simplify(w*(ca*exp(pa)-cb*exp(pb))-D/h*A*(ca-exp(du)*cb))==0
    B=zeros(len(POINTS),len(BONDS))
    for j,(i,k) in enumerate(BONDS):
        B[i,j],B[k,j]=-1,1
    assert B.shape==(27,54) and B.rank()==26 and ones(1,27)*B==zeros(1,54)
    Z=Matrix.hstack(*B.nullspace())
    assert B*Z==zeros(27,28)
    def reconstruct(div,W):
        assert sum(div)==0
        L=B*W*B.T
        y=zeros(27,1)
        y[:26,0]=-L[:26,:26].inv(method="DM")*div[:26,0]
        return -W*B.T*y
    # Exact rational positive conductances, not fitted SG diffusivities.
    W=diag(*[1+(i%3) for i in range(54)])
    y=Matrix([i*i+1 for i in range(27)])
    J=-W*B.T*y
    assert Z.T*W.inv(method="DM")*J==zeros(28,1)
    assert reconstruct(B*J,W)==J
    assert B.col_join(Z.T*W.inv(method="DM")).to_DM().rank()==54
    # Fixed W unique even on disconnected active support: restrict to active edges.
    active=[j for j,(a0,b0) in enumerate(BONDS) if a0!=0 and b0!=0]
    Ba=B[:,active]
    assert Ba.rank()==25 and len(Ba.nullspace())==len(active)-25
    # Time-varying weight countermodel: opposite divergences, different flows.
    W1=eye(54); W2=eye(54); W2[0,0]=2
    j1=-W1*B.T*eye(27)[:,0]
    j2=reconstruct(-B*j1,W2)
    assert B*(j1+j2)==zeros(27,1) and j1+j2!=zeros(54,1)
    assert Z.T*j1==zeros(28,1) and Z.T*W2.inv(method="DM")*j2==zeros(28,1)
    print(f'SymPy {__version__}: target minimal pairs {len(a)}/21: {a}')
    print(f'Gross minimal triples {len(b)}/35: {b}')
    print('SG sign, 54-rank weighted closure, exact reconstruction, disconnected support, varying-weight counterexample PASS')
    print('Integrated nonzero cycle first bond:', (j1+j2)[0])


if __name__=='__main__':
    check()

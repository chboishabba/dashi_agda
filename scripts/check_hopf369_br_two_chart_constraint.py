#!/usr/bin/env python3
"""BR26: exact fixed material two-chart boundary and homogeneous gauge weld."""
import sympy as s


def run():
    # First jets of arbitrary 4D Lorentz tangential block, shift and normal scale.
    # Test with independent jets at a diagonal tangential point; beta arbitrary.
    h=s.diag(-1,1,1,1); I=s.eye(4); l=s.Symbol('lam',positive=True)
    beta=s.Matrix(s.symbols('b0:4',real=True)); dl=s.Matrix(s.symbols('dl0:5'))
    dh=[s.Matrix(4,4,lambda i,j:s.Symbol('h%d_%d_%d'%(a,min(i,j),max(i,j)))) for a in range(5)]
    db=[s.Matrix(s.symbols('b%d_0:4'%a)) for a in range(5)]
    g=h.row_join(h*beta).col_join((beta.T*h).row_join(s.Matrix([[l*l+(beta.T*h*beta)[0]]])))
    gi=(h.inv()+beta*beta.T/l**2).row_join(-beta/l**2).col_join((-beta.T/l**2).row_join(s.Matrix([[1/l**2]])))
    assert (g*gi-s.eye(5)).applyfunc(s.expand)==s.zeros(5)
    dg=[]
    for a in range(5):
        c=dh[a]*beta+h*db[a]
        d=2*l*dl[a]+(2*db[a].T*h*beta+beta.T*dh[a]*beta)[0]
        dg.append(dh[a].row_join(c).col_join(c.T.row_join(s.Matrix([[d]]))))
    G=s.Matrix([sum(gi[a,b]*(dg[a][i,b]-dg[i][a,b]/2) for a in range(5) for b in range(5)) for i in range(5)])
    Gh=s.Matrix([sum(h[a,b]*(dh[a][i,b]-dh[i][a,b]/2) for a in range(4) for b in range(4)) for i in range(4)])
    Dy=lambda values:values[4]-sum((beta[a]*values[a] for a in range(4)),s.zeros(*values[4].shape))
    Dy_l=dl[4]-beta.dot(dl[:4,0]); Dy_b=Dy(db)
    divb=sum(db[a][a] for a in range(4))
    tau=(s.trace(h*Dy(dh))/2-divb)/l
    normal=(G[4]-(beta.T*G[:4,0])[0])/l
    assert s.expand(normal+tau-Dy_l/l**2)==0
    assert (G[:4,0]-Gh+dl[:4,0]/l-h*Dy_b/l**2).applyfunc(s.expand)==s.zeros(4,1)
    # Isometric wall identification permits unequal normal coordinate scales.
    lp,lm=s.symbols('lp lm',positive=True)
    Gp=g.subs(l,lp); Gm=g.subs(l,lm)
    # Pull minus chart into plus normal coordinate, including shift correction.
    J=I.row_join(beta*(1-lp/lm)).col_join(s.zeros(1,4).row_join(s.Matrix([[lp/lm]])))
    assert (J.T*Gm*J-Gp).applyfunc(s.expand)==s.zeros(5)
    # Gaussian trace Codazzi: jump Ric_na=0 implies Robin for continuous C_a
    # with C_n=0 on both traces.
    j=s.Symbol('j',real=True,nonzero=True); c=s.Matrix(s.symbols('c0:4'))
    K=s.Matrix(4,4,lambda a,b:s.Symbol('k%d%d'%(min(a,b),max(a,b))))
    dcp,dcm=s.Matrix(s.symbols('dp0:4')),s.Matrix(s.symbols('dm0:4'))
    Ricjump=(dcp-dcm)/2-(K+j*h)*h*c+K*h*c
    assert (Ricjump-(dcp-dcm)/2+j*c).applyfunc(s.expand)==s.zeros(4,1)
    # Gauss: equal Lambda, [K]=j h, [G_nn]=3j tr M.
    M=h*K; Ap=M+j*I/2; Am=M-j*I/2
    gauss=lambda A:(s.trace(A)**2-s.trace(A*A))/2
    assert s.expand(gauss(Ap)-gauss(Am)-3*j*s.trace(M))==0
    # 10 h continuity, 4 beta continuity, 10 Israel, 4 C_a jump, 2 C_n.
    assert 10+4+10+4+2==2*15
    print('PASS exact nonlinear contracted source, unequal-lapse chart gluing, Codazzi Robin and normal force reconstruction')

if __name__=='__main__':run()

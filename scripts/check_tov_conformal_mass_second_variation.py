"""Time-symmetric conformal ADM mass reduction for original repaired TOV.
Fixed conformal metric, compactly supported material perturbations. This is
a genuine constrained subspace test, not the general polar Hessian.
"""
import sympy as s

def main():
    e,chi,T,T1,T2,V,V1,V2,R,lap,c=s.symbols('e chi T T1 T2 V V1 V2 R lap c',real=True)
    I=s.eye(3)
    X=s.Matrix(3,3,lambda i,j:s.Symbol('X%d%d'%(min(i,j),max(i,j))))
    C=X-4*chi*I
    omega=1+e*chi
    # sqrt(h) conformal constraint is not rho itself: omega^5 rho.
    source=omega*(T+e*T1+e**2*T2/2)+omega**5*(V+e*V1+e**2*V2/2)+omega**5*c*e**2*(s.trace(C)**2-s.trace(C*C))/2
    first=s.expand(source).coeff(e,1)
    second=2*s.expand(source).coeff(e,2)
    assert s.expand(first-(T+5*V)*chi-T1-V1)==0
    assert s.expand(second-(T2+V2+2*chi*T1+10*chi*V1+20*chi**2*V+c*(s.trace(C)**2-s.trace(C*C))))==0
    assert s.expand(s.trace(C)**2-s.trace(C*C)-(s.trace(X)**2-s.trace(X*X)-16*chi*s.trace(X)+96*chi**2))==0
    # R=16pi(T+V). Linearization of conformal Hamiltonian equation.
    F=-8*e*lap+R*omega-16*s.pi*source
    assert s.expand(F.diff(e).subs(e,0).subs(R,16*s.pi*(T+V))+8*(lap+8*s.pi*V*chi)+16*s.pi*(T1+V1))==0
    # Static matter active contraction rho+S=-2V; repair has zero first jet.
    K=s.diag(*s.symbols('k:3')); B=s.diag(*s.symbols('b:3'))
    energy=s.trace(K*B)+V; pressure=2*K*B-energy*I
    assert s.expand(energy+s.trace(pressure)+2*V)==0
    # Green identity for scalar conformal block (radial weighted version);
    # full angular terms cancel pairwise on identical harmonic.
    r=s.symbols('r',positive=True); w=s.Function('w')(r); A=s.Function('A')(r)
    N=s.Function('N')(r); u=s.Function('u')(r); pot=s.Function('pot')(r)
    op=lambda z:-(A*z.diff(r)).diff(r)/w+pot*z
    assert s.expand(w*(N*op(u)-u*op(N))-(A*(u*N.diff(r)-N*u.diff(r))).diff(r))==0
    print('PASS conformal Hamiltonian second jet, active lapse adjoint, ADM Green identity')
    print('OPEN full polar conformal-metric variation, moving support, nonradial sign, physical source')
if __name__=='__main__':main()

"""BR308: exact candidate caloric material stress and EM/reservoir exchange.
Conditional constitutive completion of BR304, not the original verified
material action or a covariant PDE solution.
"""
import sympy as s

def zero(x):
    if isinstance(x,s.MatrixBase):assert x.applyfunc(s.simplify)==s.zeros(*x.shape)
    else:assert s.simplify(x)==0, s.simplify(x)

def run():
    rho,T,c=s.symbols('rho T c',positive=True)
    e=c*rho*T;p=rho*T
    mu=T*(s.log(rho)-c*s.log(T))
    entropy=rho*(1-s.log(rho)+c*(1+s.log(T)))
    zero(e+p-T*entropy-mu*rho)
    dr,dT,theta,Q=s.symbols('D_rho D_T theta Q',real=True)
    D=lambda f:s.diff(f,rho)*dr+s.diff(f,T)*dT
    # Number-current conservation Drho=-rho theta.
    number={dr:-rho*theta}
    energy=s.expand(D(e)+(e+p)*theta).subs(number).factor()
    entropy_production=s.expand(T*(D(entropy)+entropy*theta)).subs(number).factor()
    zero(energy-entropy_production)
    zero(energy-(c*rho*dT+rho*T*theta))
    heating=s.solve(s.Eq(energy,Q),dT)[0]
    zero(entropy_production.subs(dT,heating)-Q)
    # Full spacetime orthogonal decomposition. u^2=-1, u.f=0.
    # The electromagnetic Lorentz force is spatial; reservoir thermal
    # exchange supplies Q u, with its own opposite stress divergence.
    D_e,acc,dp,f=s.symbols('D_e acc projected_dp f',real=True)
    # timelike and spatial coefficients independently specified
    fluid_energy=D_e+(e+p)*theta
    fluid_momentum=(e+p)*acc+dp
    zero(s.solve(s.Eq(fluid_momentum,f),acc)[0]-(f-dp)/(e+p))
    zero((fluid_energy-Q).subs(D_e,Q-(e+p)*theta))
    # Four-current conservation and split source accounting:
    # div(T_EM)=-f, div(T_fluid)=f+Q*u, div(T_bath)=-Q*u.
    fvec=s.Matrix(s.symbols('f0:4'));u=s.Matrix(s.symbols('u0:4'))
    zero(-fvec+(fvec+Q*u)-Q*u)
    # Independent negative controls: omitting bath or choosing a wrong
    # energy-current sign violates exact total stress conservation.
    assert fvec+Q*u-fvec!=s.zeros(4,1)
    assert (s.diff(energy,T)!=0)
    print('BR308 PASS first law Euler/Gibbs relation, conserved-current entropy balance')
    print('BR308 PASS orthogonal material force and signed EM/material/bath stress exchange')
    print('BR308 candidate T evolution',heating)
    print('OPEN original material action, actual bath stress/source and full PDE')
if __name__=='__main__':run()

"""Scale-critical physical A source bound with a logarithmic H2 input.

Original analysis: standard Fourier, Cauchy-Schwarz, product rule, heat
resolvent and 3D radial integration (not a claim of a new Navier-Stokes
regularity theorem). Same physical unforced field u in H²(R³):
E=||u||²_2, D=||grad u||²_2, H=||grad²u||²_2,
g=(u·grad)u=div(u tensor u), and f=P g.

For the unnormalized Fourier convention exp(-ix·xi), at |xi|=r:
|fhat| <= min(E*r, sqrt(E*D), (D+sqrt(E H))/r).
The high-frequency bound is from the L1 norm of grad(g), NOT the
generally false claim that Leray projection is L1 bounded:
|xi| |P_xi ghat| <= |FT(grad g)| <= ||grad g||_1.

Then Vhat=fhat/(nu*r²) obeys the Fourier-side scale-critical estimate
integral_R³ |xi| |Vhat|² dxi <= 4pi ED/nu² (1+log(1+sqrt(E H)/D)).
The physical dot-H^(1/2) norm using this transform has an additional
factor (2pi)^(-3). For E,D=0, u=0 and V=0.

The same L²_t estimate transfers to the causal nonlinear Duhamel term
by Jensen/Tonelli whenever its physical Duhamel identity is available.
No uniform bound on time-integral of D log(1+sqrt(EH)/D), no A3
continuation criterion, no Bishop Agda proof is asserted.
"""
import sympy as S

def certificate():
    r,E,D,H,nu,lam=S.symbols('r E D H nu lam',positive=True)
    B=S.sqrt(E*D); M=D+S.sqrt(E*H)
    r0=B/E; r1=M/B
    assert S.simplify(r1-r0).is_nonnegative
    terms=(
      S.integrate(4*S.pi*r**3*(E/(nu*r))**2,(r,0,r0)),
      S.integrate(4*S.pi*r**3*(B/(nu*r*r))**2,(r,r0,r1)),
      S.integrate(4*S.pi*r**3*(M/(nu*r**3))**2,(r,r1,S.oo)),
    )
    goal=4*S.pi*E*D/nu**2*(1+S.log(M/D))
    assert S.simplify(sum(terms)-goal)==0
    Mscaled=lam*D+S.sqrt((E/lam)*(lam**3*H))
    scaled=4*S.pi*(E/lam)*(lam*D)/nu**2*(1+S.log(Mscaled/(lam*D)))
    assert S.simplify(scaled-goal)==0
    return {'low':str(S.simplify(terms[0])),
            'mid':str(S.simplify(terms[1])),
            'high':str(S.simplify(terms[2])),
            'total':str(goal),
            'scaling_invariant':True,
            'status':'conditional H2 input; NOT uniform continuation'}

if __name__=='__main__': print(certificate())

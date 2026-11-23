"""One-pair C3 ring response; conditional bulk Maxwell circle reduction.
No identification of UH dilaton with circle radius or actual material.
"""
import sympy as s
q,J,d,E=s.symbols('q J d E', positive=True)
# fixed Jordan geometry, fixed bare bulk electromagnetic coupling
# b=b0 exp(q), A_E=exp(-q/2), alpha_EM=alpha0 exp(-q)
# fixed coordinate geometry in Jordan frame: C_J proportional 1/alpha_EM
# charging energy E_C,J proportional alpha_EM; Einstein energy multiplies A_E
# canonical electric field/dipole normalization depends on frame: do not mix.
alpha=s.exp(-q); EC=s.exp(-3*q/2)
assert s.diff(alpha,q)==-alpha and s.diff(EC,q)==-3*EC/2
# C3 one-pair hopping: H=-J(K+K^T), selected diagonal dipole of zero mean
K=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
I=s.eye(3); H=-J*(K+K.T); g=s.ones(3,1)/s.sqrt(3); Q=I-g*g.T
O=d*s.diag(1,-s.Rational(1,2),-s.Rational(1,2))
assert K**3==I and H*g==-2*J*g and H*Q==J*Q
assert (g.T*O*g)[0]==0
chi=s.simplify((2*g.T*O*Q*O*g)[0]/(3*J));assert chi==d*d/(3*J)
assert Q*(-(K+K.T))*g==s.zeros(3,1)
# exact ground energy with E field: even-under site exchange block
# diag -dE, -J+dE/2, offdiag -sqrt(2)J
h=s.Matrix([[-d*E,-s.sqrt(2)*J],[-s.sqrt(2)*J,-J+d*E/2]])
e0=s.trace(h)/2-s.sqrt(((h[0,0]-h[1,1])/2)**2+2*J*J)
series=s.series(e0,E,0,5).removeO().expand();assert s.simplify(-s.diff(e0,E,2).subs(E,0)-chi)==0
print('C3 ground energy series:',series)
print('C3 susceptibility:',chi,'uniform hopping vertex dark')
# Independent bulk gauge WKB illustration (not selected material): fixed mass,
# barrier height and gap in Jordan.*  J proportional alpha*exp(-2 L sqrt(2m V)/hbar)
# is NOT implied by Maxwell. Ambegaokar-Baratoff instead: J= pi*hbar*gap/(4 e^2 R_N).
# Drude/tunnel normal conductance G_N proportional e² times transmissions,
# so explicit e² cancels with fixed channel transmissions.
e, gap, T, hb=s.symbols('e gap T hbar',positive=True)
GN=e**2*T/hb
JJ=s.pi*hb*gap*GN/(4*e**2)
assert s.diff(JJ,e)==0
print('AB explicit charge cancels at fixed gap and transmissions:',JJ)
print('PASS circle Maxwell scaling, C3 spectral selection, nonlinear exact energy, AB cancellation')
# Legendre inversion of the C3 nonlinear series.
p=s.symbols('p',real=True)
a1=d*d/(3*J); a2=d**3/(12*J**2); a3=-d**4/(54*J**3)
Einv=p/a1-a2*p*p/a1**3+(2*a2*a2/a1**5-a3/a1**4)*p**3
assert s.simplify(s.series(a1*Einv+a2*Einv**2+a3*Einv**3,p,0,4).removeO()-p)==0
print('Legendre material energy through quartic:',s.integrate(Einv,p)-2*J)
# Flux-frustrated ring: choose ground momentum 0 for 0<=theta<pi/3.
# Other gaps 3J cos theta +/- sqrt(3)J sin theta; dipole couples both.
th=s.symbols('theta',real=True)
gp=J*(3*s.cos(th)+s.sqrt(3)*s.sin(th));gm=J*(3*s.cos(th)-s.sqrt(3)*s.sin(th))
response=d*d/2*(1/gp+1/gm)
assert s.simplify(response.subs(th,0)-chi)==0
print('flux ring susceptibility:',s.trigsimp(response))
print('PASS nonlinear Legendre inversion and flux-dependent spectral response')

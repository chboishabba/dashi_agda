#!/usr/bin/env python3
"""Exact three-channel complex C3 optical interference and sensitivity audit.

References: NS signed centering owner; Shor finite Born weights; Omar et al.,
Science Advances 2026, doi:10.1126/sciadv.aeg5281. Measured system figures
are source observations, not fitted model parameters.
"""
import sympy as s
I=s.I
ar,ai,br,bi,cr,ci=s.symbols("ar ai br bi cr ci",real=True)
z=[ar+I*ai,br+I*bi,cr+I*ci]
def work(u,v):return s.expand(s.expand_complex(u*s.conjugate(v)+v*s.conjugate(u)))
w=[work(z[0],z[1]),work(z[1],z[2]),work(z[2],z[0])]
total=s.expand(s.expand_complex(sum(z)*s.conjugate(sum(z))))
self_w=sum(s.expand(s.expand_complex(v*s.conjugate(v))) for v in z)
assert s.simplify(total-self_w-sum(w))==0
def rotate(v):return [v[2],v[0],v[1]]
assert rotate(rotate(rotate(z)))==z
assert s.simplify(total-s.expand(s.expand_complex(sum(rotate(z))*s.conjugate(sum(rotate(z)))))==0
assert all(s.simplify(a-b)==0 for a,b in zip([work(rotate(z)[0],rotate(z)[1]),work(rotate(z)[1],rotate(z)[2]),work(rotate(z)[2],rotate(z)[0])],rotate(w)))
r=s.symbols("r0:3",real=True)
lhs=s.expand(-3*sum(r[i]*w[i] for i in range(3))+sum(r)*sum(w))
rhs=-sum((r[i]-r[j])*(w[i]-w[j]) for i in range(3) for j in range(i+1,3))
assert s.simplify(lhs-rhs)==0
# Full width at half maximum GammaFWHM, rate R, contrast C, Hz/T gamma.
Gamma,R,C,gamma=s.symbols("Gamma R C gamma",positive=True,real=True)
delta=s.symbols("delta",real=True)
line=1/(1+(2*delta/Gamma)**2)
rate=R*(1-C*line)
slope=s.diff(rate,delta)
assert s.simplify(slope.subs(delta,Gamma/(2*s.sqrt(3)))-9*R*C/(4*s.sqrt(3)*Gamma))==0
# Conventional weak-contrast shot noise evaluated using off-resonance R.
eta=s.simplify(s.sqrt(R)/(gamma*slope.subs(delta,Gamma/(2*s.sqrt(3)))))
assert s.simplify(eta-4*s.sqrt(3)*Gamma/(9*gamma*C*s.sqrt(R)))==0
# Equality to the standard 4/(3 sqrt(3)) linewidth convention.
assert s.simplify(eta-4*Gamma/(3*s.sqrt(3)*gamma*C*s.sqrt(R)))==0
# No raw spectrum supplied: cannot derive R,C,Gamma or technical noise from eta.
observed={"ZAQuant_pT_per_rootHz":s.Integer(7),"QANT_pT_per_rootHz":s.Integer(26)}
assert observed["ZAQuant_pT_per_rootHz"]<observed["QANT_pT_per_rootHz"]
print("PASS exact complex conjugate C3 cross-work, Born decomposition, NS signed centering")
print("PASS Lorentzian FWHM slope and weak-contrast photon shot noise limit")
print("SOURCE observed system sensitivities (pT/sqrt(Hz)):",observed)
print("NOT IDENTIFIED: detector count rate, linewidth, contrast, tech-noise spectrum, raw cardiac field.")

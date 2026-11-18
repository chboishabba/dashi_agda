#!/usr/bin/env python3
"""KK geometric radion coupling and superconducting braking: exact checks.

Reuse PR #1239 KK reduced-action / 2026-10-24 KKSingleActionRadion
and Filsinger pump-source energy ledger. No physical screening claim.
"""
import sympy as s
def main():
 v,M,F2=s.symbols("v M F2",real=True,positive=True)
 Z=s.exp(s.sqrt(6)*v/M)
 A=s.exp(-v/(s.sqrt(6)*M))
 beta=s.simplify(M*s.diff(s.log(A),v))
 assert s.simplify(beta**2-s.Rational(1,6))==0
 assert s.simplify(2*beta**2-s.Rational(1,3))==0
 assert s.simplify(s.diff(-Z*F2/4,v).subs(v,0)+s.sqrt(6)*F2/(4*M))==0
 loss=s.Rational(2,100)/s.Rational(1,3)
 depth=-s.log(1-loss)
 assert loss==s.Rational(3,50)
 assert s.simplify(s.exp(-depth)-s.Rational(47,50))==0
 Of,Od,p,af,ad=s.symbols("Of Od p af ad",real=True)
 slip=Of-p*Od
 assert s.diff(slip,Of)*af+s.diff(slip,Od)*ad==af-p*ad
 I,L,R,P,theta,wf,wd=s.symbols("I L R P theta wf wd",real=True)
 dflux=-P*s.sin(theta)
 didt=(-R*I-dflux*(wf-p*wd))/L
 assert s.simplify(L*I*didt+R*I**2-I*dflux*p*wd+I*dflux*wf)==0
 q,a,eps0,c=s.symbols("q a eps0 c",positive=True)
 larmor=q*q*a*a/(6*s.pi*eps0*c**3)
 assert s.diff(larmor,a,2)==q*q/(3*s.pi*eps0*c**3)
 print("PASS geometric radion beta²=1/6, Maxwell scalar source, slip, source-work, Larmor")
 print("2% total weight requires attenuation of unscreened scalar fraction:",loss)
 print("Ideal one-branch decay optical depth:",s.N(depth,10))
 print("OPEN 5D matter stabilisation, Earth scalar BVP, fifth-force limits and YBCO response")
if __name__=="__main__":main()

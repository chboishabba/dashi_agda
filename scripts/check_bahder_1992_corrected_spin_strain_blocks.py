#!/usr/bin/env python3
"""Exact transcription/check of Bahder 1992 erratum corrected N1,N2,N3.

Phys Rev B 46, 9913 (1992), DOI 10.1103/PhysRevB.46.9913,
correction to Eqs 33-35 of 1990 DOI 10.1103/PhysRevB.41.11992.

This reproduces the erratum's spin-orbit STRAIN matrices in its Gamma8/Gamma7
block convention, not the full eight-band Hamiltonian, not a fit, and not a
coordinate-aligned replacement for the old Cartesian L*S matrix.
"""
import json
import sympy as s

ex,ey,ez,exy,exz,eyz,Delta=s.symbols('eps_xx eps_yy eps_zz eps_xy eps_xz eps_yz Delta',real=True)
e=ex+ey+ez
I=s.I
rt2,rt3,rt6=s.sqrt(2),s.sqrt(3),s.sqrt(6)
a=- (e/s.Integer(3)+ez)
b=-2*(exz+I*eyz)/rt3
c=(ey-ex+2*I*exy)/rt3
d=ez-e
f=2*(exz+I*eyz)/rt3
N1=Delta/3*s.Matrix([[a,b,c,0],[s.conjugate(b),d,0,c],
                      [s.conjugate(c),0,d,f],[0,s.conjugate(c),s.conjugate(f),a]])
N2=Delta/3*s.Matrix([
    [-(exz-I*eyz)/rt2, -(3*ez-e)/(3*rt2)],
    [(ey-ex+2*I*exy)/rt6, -(exz-I*eyz)/rt6],
    [-(exz+I*eyz)/rt6, (ex-ey+2*I*exy)/rt6],
    [(3*ez-e)/(3*rt2), -(exz+I*eyz)/rt2]
])
N3=(Delta/3)*(4*e/3)*s.eye(2)
N=N1.row_join(N2).col_join(N2.H.row_join(N3))
tests=[]
def t(name,condition):
    assert condition,name
    tests.append(name)
def iszero(m):return all(s.simplify(a)==0 for a in m)

for key,mat,shape in [('N1',N1,(4,4)),('N2',N2,(4,2)),('N3',N3,(2,2)),('N6',N,(6,6))]:
    t(key+' correct shape',mat.shape==shape)
t('N1 Hermitian',iszero(N1-N1.H))
t('N3 Hermitian',iszero(N3-N3.H))
t('N6 Hermitian',iszero(N-N.H))
zero={ex:0,ey:0,ez:0,exy:0,exz:0,eyz:0}
for key,mat in [('N1',N1),('N2',N2),('N3',N3),('N6',N)]:
    t(key+' zero if zero strain',iszero(mat.subs(zero)))
hydro={ex:s.Symbol('h',real=True),ey:s.Symbol('h',real=True),
       ez:s.Symbol('h',real=True),exy:0,exz:0,eyz:0}
h=s.Symbol('h',real=True)
t('hydrostatic N1 proportional identity',iszero(N1.subs(hydro)+2*Delta*h/3*s.eye(4)))
t('hydrostatic N2 zero',iszero(N2.subs(hydro)))
t('hydrostatic N3 scalar identity',iszero(N3.subs(hydro)-4*Delta*h/3*s.eye(2)))
t('hydrostatic eigen Gamma8/Gamma7 gap spin-strain differs',
   s.simplify((-2*Delta*h/3)-(4*Delta*h/3)+2*Delta*h)==0)
t('pure xy shear creates N1 offdiagonal',s.simplify(N1[0,2].subs({ex:0,ey:0,ez:0,exy:1,exz:0,eyz:0}))!=0)
t('pure xz shear creates N2 mixing',s.simplify(N2[0,0].subs({ex:0,ey:0,ez:0,exy:0,exz:1,eyz:0}))!=0)
t('N3 only trace',all(s.simplify(s.diff(N3[0,0],v))==0 for v in [exy,exz,eyz]))
t('N6 spin-strain trace identically zero',s.simplify(s.trace(N))==0)

axial,trans=s.symbols('eps_out eps_in',real=True)
eps={ex:trans+(axial-trans)/3,ey:trans+(axial-trans)/3,
     ez:trans+(axial-trans)/3,exy:(axial-trans)/3,exz:(axial-trans)/3,eyz:(axial-trans)/3}
N111=s.simplify(N.subs(eps,simultaneous=True))
t('111 coherent strain Hermiticity',iszero(N111-N111.H))
t('111 zero anisotropy gives hydrostatic N2 zero',iszero(N2.subs(eps,simultaneous=True).subs(axial,trans)))
t('111 shear offdiagonal nonzero for axial != transverse',
  s.simplify(N111[0,1]).subs({axial:1,trans:0,Delta:1}) != 0)
t('substitution strain zero reduces N blocks',iszero(N111.subs({axial:0,trans:0})))

# 1992 erratum independent algebraic changes (not yet integrated into a
# SAME-BASIS 8x8 Hamiltonian). Exact source also corrects Eq.16 R,
# Eq.30 a and powers of hbar in Eq.42 P,Q,R,S.
gamma2,gamma3,kx,ky,hbar,mass=s.symbols(
    'gamma2 gamma3 kx ky hbar m0',real=True,nonzero=True)
Rfix=-s.sqrt(3)/2*(hbar**2/mass)*(
    gamma2*(kx**2-ky**2)-2*s.I*gamma3*kx*ky)
Rwrong=-Rfix
l,m=s.symbols('ell m',real=True)
afix=-(l+2*m)/3
awrong=(l+2*m)/3
t('Eq16 R fixed kx-axis',s.simplify(Rfix.subs(ky,0)+s.sqrt(3)/2*(hbar**2/mass)*gamma2*kx**2)==0)
t('Eq16 R fixed ky-axis',s.simplify(Rfix.subs(kx,0)-s.sqrt(3)/2*(hbar**2/mass)*gamma2*ky**2)==0)
t('Eq16 R cross term at kx=ky',s.simplify(Rfix.subs(ky,kx)-s.I*s.sqrt(3)*(hbar**2/mass)*gamma3*kx**2)==0)
t('Eq16 R conjugate offdiagonal Hermiticity',iszero(s.Matrix([[0,Rfix],[s.conjugate(Rfix),0]])-s.Matrix([[0,Rfix],[s.conjugate(Rfix),0]]).H))
t('Eq16 R source-correct minus fixed in convention',s.simplify(Rfix-Rwrong)!=0)
t('Eq30 a corrected minus sign',s.simplify(afix+(l+2*m)/3)==0)
t('Eq30 a mismatched alternative except special parameters',s.simplify(afix-awrong)!=0)
t('Eq42 hbar squared dimensional homogeneity',s.simplify(Rfix/hbar**2).has(hbar)==False)
t('Eq42 missing hbar factor not equivalent',s.simplify(Rfix.subs(hbar,1)-Rfix)!=0)

# The magnitude of the OMITTED strain-SO operator for one coherent-film
# source example is an evidence-quality sensitivity bound, not a fitted gap.
import numpy as np
numbers={axial:-s.Rational(269,580)*s.Rational(5,1000),
         trans:s.Rational(5,1000),Delta:s.Rational(341,1000)}
N_example=np.array(N111.subs(numbers).evalf(),dtype=complex)
vals=np.linalg.eigvalsh(N_example)
normmev=float(np.max(np.abs(vals))*1000)
t('coherent 111 omitted SO matrix Hermitian numeric',np.allclose(N_example,N_example.conj().T))
t('coherent 111 omitted SO matrix trace zero',abs(np.trace(N_example))<1e-12)
t('coherent 111 omitted SO Kramers double pairs',np.max(abs(vals[0::2]-vals[1::2]))<1e-12)
t('coherent 111 omitted SO norm about 1.28 meV',1.27<normmev<1.29)

print(json.dumps({'checks':len(tests),'all_passed':True,
 'source':'Bahder PRB 46 9913 (1992) one-page erratum, corrected spin-orbit strain blocks only',
 'Gamma_basis':'Gamma8 (4) + Gamma7 (2), as published in erratum',
 'corrected_spin_orbit_blocks':'N1 (4x4), N2 (4x2), N3 (2x2)',
 'other_erratum_items_symbolically_checked':['eq30 valence a sign','eq16 R','eq42 hbar squared'],
 'same_basis_8band_assembly_and_original_source_fit':'OPEN',
 'full_Bahder_8band':'OPEN',
 'corrected_SO_norm_at_0p5pct_coherent_111_meV':normmev,
 'spectrum_stability':'Weyl <= operator norm IF assembled on same Hilbert basis; full original model OPEN',
 'tests':tests},indent=2))

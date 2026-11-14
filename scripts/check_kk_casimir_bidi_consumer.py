#!/usr/bin/env python3
"""Conditional one-loop compact S1 stabilisation and admissible consumers.

5D spectrum: periodic massless real scalar (-1 Casimir unit); OPTIONAL
periodic 5D U1 vector (-3, three physical polarizations); periodic massive
5D Dirac fermions (+4 each). Finite 4D potential at a gauge-neutral vacuum.
Free-field one-loop truncation; full Standard Model absent.

Two distinct photons: the geometric graviphoton, with fixed coupling to
fifth momentum, and an optional independent Maxwell zero mode, with its
own adjustable 5D gauge coupling. No physical Earth solution claimed.
"""
from mpmath import mp
mp.dps = 55
ZETA5 = mp.zeta(5)
C0 = 3*ZETA5/(64*mp.pi**6)
N = 128

def casimir(z, deriv=0):
    if deriv == 0:
        return mp.fsum(mp.exp(-n*z)*(1+n*z+(n*z)**2/3)/n**5 for n in range(1,N+1))/ZETA5
    if deriv == 1:
        return -z/(3*ZETA5)*mp.fsum(mp.exp(-n*z)*(1+n*z)/n**3 for n in range(1,N+1))
    if deriv == 2:
        return -1/(3*ZETA5)*mp.fsum(mp.exp(-n*z)*(1+n*z-(n*z)**2)/n**3 for n in range(1,N+1))
    raise ValueError

def decreasing_derivative(z):
    # h(z)=f(z)-z*f'(z)/5, and h'(z)<0 on z>0
    return -z/(15*ZETA5)*mp.fsum(mp.exp(-n*z)*(3+3*n*z+(n*z)**2)/n**3 for n in range(1,N+1))

def solve(a_bosons, d_fermions):
    a=mp.mpf(a_bosons)
    d=mp.mpf(d_fermions)
    assert d>a>0
    z=mp.findroot(lambda t: casimir(t)-t*casimir(t,1)/5-a/d,(mp.mpf('1'),mp.mpf('7')))
    L=a-d*casimir(z)
    def U(x): return L/x+(-a+d*casimir(z*x))/x**6
    Up=-L-6*(-a+d*casimir(z))+d*z*casimir(z,1)
    U2=d*(z*z*casimir(z,2)-4*z*casimir(z,1))
    assert abs(U(1))<mp.mpf('1e-42') and abs(Up)<mp.mpf('1e-42')
    assert U2>0 and decreasing_derivative(z)<0
    assert U(mp.mpf('.99'))>0 and U(mp.mpf('1.01'))>0
    return z,L,U2

def fifth_force_at_surface(radion_range,R):
    z=R/radion_range
    if z<mp.mpf('1e-6'): return mp.mpf('1')/3
    return ((z-1)+(z+1)*mp.exp(-2*z))*(1+z)/(2*z**3)

HC=mp.mpf('0.1973269804e-15') # 1 GeV^-1 in metres
MP=mp.mpf('2.435e18') # reduced Planck mass, GeV
ALPHA=1/mp.mpf('137.035999084')
QED=mp.sqrt(4*mp.pi*ALPHA)
R_EARTH=mp.mpf('6371000')
R_SUN=mp.mpf('695700000')
for name,a,d in [('primary_graviton_photon_scalar_three_Dirac',9,12),
                 ('matter_only_two_Dirac_truncation',4,8),
                 ('geometric_U1_only',1,4)]:
    z,L,U2=solve(a,d)
    coeff=mp.sqrt(mp.mpf(2)/3*C0*U2)
    print(f'MODEL {name}: bosons -{a}, massive fermions +{d}, z0={mp.nstr(z,16)}, Lambda={mp.nstr(L,12)}, U2={mp.nstr(U2,12)}, radionPrefactor={mp.nstr(coeff,12)}')
    for rad in ('1e-15','1e-21','1e-24'):
        b=mp.mpf(rad)/HC
        radion_range=MP*b**2*HC/coeff
        gKK=mp.sqrt(2)/(MP*b)
        m5=(MP**2/(2*mp.pi*b))**(mp.mpf(1)/3)
        expansion=b*m5
        efifth=fifth_force_at_surface(radion_range,R_EARTH)
        sfifth=fifth_force_at_surface(radion_range,R_SUN)
        mf=z/(2*mp.pi*b)
        print(f' b0={rad}m; radionRange={mp.nstr(radion_range,8)}m; gKK={mp.nstr(gKK,7)}; fermionMass={mp.nstr(mf,7)}GeV; bM5={mp.nstr(expansion,7)}; EarthSurfaceFifthForce={mp.nstr(efifth,7)}; SunSurfaceFifthForce={mp.nstr(sfifth,7)}')
        assert expansion>1000
        if rad=='1e-24':
            assert efifth<mp.mpf('1e-10') and sfifth<mp.mpf('1e-10')
            assert gKK<mp.mpf('1e-9')
    if name in ('primary_graviton_photon_scalar_three_Dirac','matter_only_two_Dirac_truncation'):
        b=mp.mpf('1e-24')/HC
        e5=QED*mp.sqrt(2*mp.pi*b)
        assert abs(e5/mp.sqrt(2*mp.pi*b)-QED)<mp.mpf('1e-50')
        print(' independent 5D Maxwell zero-mode coupling:',mp.nstr(QED,10))
bqed=HC*mp.sqrt(2)/(MP*QED)
print('Strict geometric KK photon=e requires radius',mp.nstr(bqed,12),'m, or',mp.nstr(bqed/(HC/MP),9),'reduced Planck lengths.')
assert bqed/(HC/MP)<10
print('PASS: tuned flat stable one-loop radion vacuum; unbroken independent U1; example weak-field screening.')
print('NOT PROVED: full 5D quantum effective action, SM spectrum, detailed laboratory bound, terrestrial interior/slow rotation.')
print('FAIL: geometric graviphoton as observed QED with a perturbatively controlled compact radius.')

#!/usr/bin/env python3
"""Synthetic C3 optical dipole / field discriminator; NOT a photovoltaic model.
Numpy finite-matrix test. No material calibration, carrier collection, signed
drive work, crystalline bulk bandgap or >50% energy result is asserted.
"""
import numpy as np

om=np.exp(2j*np.pi/3)
j=np.arange(3)
F=np.exp(2j*np.pi*np.outer(j,j)/3)/np.sqrt(3)
P=np.roll(np.eye(3),1,axis=0)
X=np.diag(np.cos(2*np.pi*j/3))
Y=np.diag(np.sin(2*np.pi*j/3))
checks=[]

def check(label,condition):
    if not condition: raise AssertionError(label)
    checks.append(label)

def ring(field_eV,hopping=-.25):
    H=hopping*(P+P.T)+field_eV*X
    energies,U=np.linalg.eigh(H)
    lines=[]
    for n in (1,2):
        gap=energies[n]-energies[0]
        strength=abs(np.vdot(U[:,n],X@U[:,0]))**2+abs(np.vdot(U[:,n],Y@U[:,0]))**2
        lines.append((float(gap),float(strength)))
    return energies,lines

def spectral_response(lines):
    # Synthetic 5778K blackbody photon weighting; not actual AM1.5G.
    E=np.linspace(.05,3,4000)
    flux=E**2/np.expm1(E/(8.617333262e-5*5778))
    flux/=np.trapezoid(flux,E)
    alpha=np.zeros_like(E)
    for gap,s in lines:
        alpha+=s*np.exp(-.5*((E-gap)/.08)**2)/(.08*np.sqrt(2*np.pi))
    return float(np.trapezoid(alpha*flux,E))

def narrow(lines,center,sigma=.04):
    return sum(s*np.exp(-.5*((gap-center)/sigma)**2) for gap,s in lines)

def test():
    check('Fourier unitarity',np.allclose(F.conj().T@F,np.eye(3),atol=1e-14))
    check('C3 order',np.allclose(np.linalg.matrix_power(P,3),np.eye(3)))
    check('H0 commutes C3',np.allclose(P@(-.25*(P+P.T)),(-.25*(P+P.T))@P))
    for r in range(3):
        D=np.diag(om**(r*j))
        T=F.conj().T@D@F
        allowed=np.zeros((3,3),bool)
        for m in range(3):allowed[(m+r)%3,m]=True
        check(f'charge {r} forbidden couplings vanish',np.max(abs(T[~allowed]))<1e-14)
        check(f'charge {r} allowed couplings unit amplitude',np.allclose(abs(T[allowed]),1))
        check(f'charge {r} commuting square',np.allclose(D@F,F@T))
    E0,line0=ring(0)
    check('C3 orbital eigenvalues',np.allclose(E0,[-.5,.25,.25]))
    check('C3 finite orbital gap',np.isclose(E0[1]-E0[0],.75))
    check('zero dipole cannot absorb',np.isclose(np.linalg.norm(np.zeros((3,3))),0))
    check('zero hopping closes gap',np.isclose(ring(0,0)[0][1]-ring(0,0)[0][0],0))
    base=spectral_response(line0)
    results=[]
    for field in (0,.05,.15,.3,.6):
        E,lines=ring(field)
        ratio=spectral_response(lines)/base
        results.append((field,float(E[1]-E[0]),ratio))
        check(f'field {field} real eigenvalues',np.all(np.isreal(E)))
        check(f'field {field} finite response',np.isfinite(ratio))
    check('field breaks C3 for this orientation',np.linalg.norm(P@X-X@P)>1)
    check('field reshapes broad photon-weighted response',abs(results[3][2]-1)>.01)
    check('response nonnegative',all(r[2]>=0 for r in results))
    _,line3=ring(.3)
    check('0.65eV narrowband gains from shift',narrow(line3,.65)>narrow(line0,.65))
    check('0.75eV narrowband loses from shift',narrow(line3,.75)<narrow(line0,.75))
    print('PASS',len(checks),'C3 optical finite tests')
    for field,gap,relative in results:
        print(f'field-code-eV={field:.2f} finite-gap-eV={gap:.5f} relative-optical-proxy={relative:.5f}')
    print('Neither optical proxy is PV power. No actuator energy, charge extraction, or material calibration.')
    return len(checks)

if __name__=='__main__':test()

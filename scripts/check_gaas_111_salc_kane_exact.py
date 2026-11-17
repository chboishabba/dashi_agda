#!/usr/bin/env python3
"""Exact GaAs [111] spinless SALC, dipole and Kane-mass discriminator.
Not an 8-band Hamiltonian, a photovoltaic measurement, or a 369 physical weld.
Sources: Vurgaftman et al. DOI 10.1063/1.1368156; Koster group compatibilities.
R|X>=|Y>, R|Y>=|Z>, R|Z>=|X>; U columns a1,e+,e-.
"""
import json
import sympy as sp

def simplify(x):
    return sp.simplify(sp.expand_complex(x))

def matrix_equal(a, b):
    return all(simplify(x)==0 for x in a-b)

def run():
    tests=[]
    def check(name, cond):
        assert bool(cond), name
        tests.append(name)

    omega=(-1+sp.sqrt(3)*sp.I)/2
    R=sp.Matrix([[0,0,1],[1,0,0],[0,1,0]])
    W=sp.Matrix([[1,0,0],[0,0,1],[0,1,0]])
    U=sp.Matrix([[1,1,1],[1,omega**2,omega],[1,omega,omega**2]])/sp.sqrt(3)
    D=sp.diag(1,omega,omega**2)
    eye=sp.eye(3)
    charge_step=R.copy()  # same permutation matrix in a DIFFERENT label basis

    check("omega cubed", simplify(omega**3-1)==0)
    check("omega roots sum", simplify(1+omega+omega**2)==0)
    check("R order three", matrix_equal(R**3,eye))
    check("mirror order two", matrix_equal(W**2,eye))
    check("C3v mirror conjugates", matrix_equal(W*R*W,R.T))
    check("U left unitary", matrix_equal(U.H*U,eye))
    check("U right unitary", matrix_equal(U*U.H,eye))
    check("correct SALC intertwiner", matrix_equal(R*U,U*D))
    check("correct diagonalization", matrix_equal(U.H*R*U,D))
    check("a1 mirror fixed", matrix_equal(W*U[:,0],U[:,0]))
    check("eplus mirror to eminus", matrix_equal(W*U[:,1],U[:,2]))
    check("eminus mirror to eplus", matrix_equal(W*U[:,2],U[:,1]))
    check("WRONG spatial-to-charge-label intertwiner rejected",
          not matrix_equal(R*U,U*charge_step))
    check("charge label permutation abstract spectrum",matrix_equal(U.H*charge_step*U,D))

    a,e=sp.symbols("epsilon_a epsilon_e",real=True)
    H=U*sp.diag(a,e,e)*U.H
    check("C3v spinless Hamiltonian shape",
          matrix_equal(H,e*eye+(a-e)*sp.ones(3)/3))
    check("C3 Hamiltonian commutes",matrix_equal(H*R,R*H))
    check("C3v mirror Hamiltonian commutes",matrix_equal(H*W,W*H))
    check("spinless E doublet forced",matrix_equal(U.H*H*U,sp.diag(a,e,e)))
    otherH=sp.diag(0,1,2)
    check("symmetry broken control",not matrix_equal(otherH*R,R*otherH))

    p=sp.symbols("p",real=True,positive=True)
    cart=p*eye
    trig=U.H*cart*U
    check("matched trigonal polarization tensor",matrix_equal(trig,p*eye))
    for i,name in enumerate(("a1","eplus","eminus")):
        check(name+" matched polarization |p|2",simplify(trig[i,i]**2-p**2)==0)
        x=(cart*U)[0,i]
        check(name+" fixed x strength p2/3",simplify(x*sp.conjugate(x)-p**2/3)==0)
        check(name+" sum over cartesian analyzer strengths",
              simplify(sum((cart*U)[j,i]*sp.conjugate((cart*U)[j,i])
                           for j in range(3))-p**2)==0)
    check("one fixed x summed over valence SALCs",
          simplify(sum((cart*U)[0,i]*sp.conjugate((cart*U)[0,i])
                       for i in range(3))-p**2)==0)
    check("all trigonal strength total 3p2",
          simplify(sum(trig[i,j]*sp.conjugate(trig[i,j])
                       for i in range(3) for j in range(3))-3*p**2)==0)

    Ep=sp.Rational(288,10); delta=sp.Rational(341,1000)
    F=sp.Rational(-194,100);Eg0=sp.Rational(1519,1000)
    Eg300=sp.Rational(1422,1000)
    def inverse_mass(g):
        return 1+2*F+(Ep/3)*(2/g+1/(g+delta))
    m0=1/inverse_mass(Eg0);m300=1/inverse_mass(Eg300)
    m2=1/(1+Ep/Eg300)
    check("0K inv mass 14.92118",abs(float(inverse_mass(Eg0))-14.92118)<1e-4)
    check("0K mass 0.06702",abs(float(m0)-.06702)<1e-4)
    check("300K inv mass 16.06737",abs(float(inverse_mass(Eg300))-16.06737)<1e-4)
    check("300K mass 0.06224",abs(float(m300)-.062238)<1e-4)
    check("0.0664 mismatch at 300K",abs(float(m300)-.0664)>.003)
    check("two-band m around .047",abs(float(m2)-.047)<.001)
    check("different temperature gaps",Eg0!=Eg300)

    free_e_mass=9.1093837139e-31
    electron_charge=1.602176634e-19
    p_si=(free_e_mass*float(Ep)*electron_charge/2)**.5
    check("Kane p momentum SI scale",1.449e-24<p_si<1.451e-24)

    report={
        "checks":len(tests),"all_passed":True,
        "basis":"X,Y,Z -> a1,eplus,eminus, spinless Td T2 down C3v A1+E",
        "U":str(U),"R":str(R),
        "correct_spatial_intertwiner":"R U = U diag(1,omega,omega**2)",
        "incorrect_original_weld":"R U != U chargePositiveStep",
        "spinless_eplus_eminus_degenerate_if_C3v":True,
        "full_matched_polarization_strength":"m0 Ep / 2",
        "fixed_lab_cartesian_single_SALC_strength":"m0 Ep / 6",
        "kane_p_SI_kg_m_s":p_si,
        "parameters":{"Ep_eV":float(Ep),"spinOrbit_eV":float(delta),"F":float(F)},
        "0K":{"Eg_eV":float(Eg0),"mass_over_m0":float(m0)},
        "300K":{"Eg_eV":float(Eg300),"mass_over_m0":float(m300)},
        "300K_two_band_m_over_m0":float(m2),
        "material_369_Bloch_weld":"OPEN","measured_PV_power_gain":"OPEN",
        "test_names":tests,
    }
    print(json.dumps(report,indent=2))
    return report

if __name__=="__main__":
    run()

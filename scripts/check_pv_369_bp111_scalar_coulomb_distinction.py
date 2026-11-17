#!/usr/bin/env python3
"""M3 SAME-MATERIAL Bir–Pikus [111] spinless orbital source discriminator.

Use EXACT original entry formula from
DASHI/Physics/Photovoltaic/GaAs111BirPikusC3vFiniteExact.agda,
not a newly invented three/six/nine "solar resonance".
H_BP^XYZ has diagonal D=av_eff Tr(eps), offdiagonal S =
d_deform (eps_parallel-eps_perpendicular)/sqrt(3) in that owner.

This 3x3 source block is covariant under physical C3v, with A1 energy
D+2S and doubly degenerate E energy D−S. A 369 label permutation,
basis transport, or addition of the source scalar Coulomb 21/128 I
does NOT split the E doublet or alter physical eigenvalues.

A genuinely new 369 mechanism needs an independently specified
new physical operator, not just changing D,S or coordinates without
a material/source control. Full spinful Kane/Bahder, excitons, absorption,
EQE and electrical gain remain UNPAID.
"""
import sympy as sp
import json

D,S,C=sp.symbols("D S C",real=True)
BASE=sp.Matrix([[D,S,S],[S,D,S],[S,S,D]])
ROT=sp.Matrix([[0,0,1],[1,0,0],[0,1,0]])
MIRROR=sp.Matrix([[1,0,0],[0,0,1],[0,1,0]])
A1=sp.Matrix([1,1,1])
E1=sp.Matrix([1,-1,0])
E2=sp.Matrix([1,1,-2])
SOURCE_SCALAR_COULOMB=sp.Rational(21,128)*sp.eye(3)

def theorem():
    tests=[]
    def ck(name,pred):
        assert bool(pred),name
        tests.append(name)
    ck("C3 order three",ROT**3==sp.eye(3))
    ck("mirror order two",MIRROR**2==sp.eye(3))
    ck("C3v mirror relation",MIRROR*ROT*MIRROR==ROT**2)
    ck("Bir-Pikus C3 covariant",BASE*ROT==ROT*BASE)
    ck("Bir-Pikus mirror covariant",BASE*MIRROR==MIRROR*BASE)
    ck("A1 exact eigenstate",BASE*A1==(D+2*S)*A1)
    ck("E1 exact eigenstate",BASE*E1==(D-S)*E1)
    ck("E2 exact eigenstate",BASE*E2==(D-S)*E2)
    ck("E degeneracy source",sp.simplify((BASE*E1)[0]+(BASE*E1)[1])==0)
    ck("selected source p2 Coulomb scalar",SOURCE_SCALAR_COULOMB==sp.diag(*([sp.Rational(21,128)]*3)))
    # The BP + scalar computation is ONLY an abstract 3x3 identity; P2
    # hydrogenic common-spin antisymmetric and GaAs XYZ Bloch sectors are
    # different physical Hilbert spaces and cannot be added as a GaAs
    # material Hamiltonian without a separately verified same-object weld.
    ck("scalar p2 preserves A1", (BASE+SOURCE_SCALAR_COULOMB)*A1==(D+2*S+sp.Rational(21,128))*A1)
    ck("scalar p2 preserves E1", (BASE+SOURCE_SCALAR_COULOMB)*E1==(D-S+sp.Rational(21,128))*E1)
    ck("scalar p2 preserves E2", (BASE+SOURCE_SCALAR_COULOMB)*E2==(D-S+sp.Rational(21,128))*E2)
    ck("scalar p2 commutes with C3",SOURCE_SCALAR_COULOMB*ROT==ROT*SOURCE_SCALAR_COULOMB)
    ck("scalar p2 commutes with mirror",SOURCE_SCALAR_COULOMB*MIRROR==MIRROR*SOURCE_SCALAR_COULOMB)
    ck("original spinless E cannot split under scalar Coulomb",((BASE+SOURCE_SCALAR_COULOMB)*E1)[0]==(D-S+sp.Rational(21,128)))
    # A DIFFERENT physical defect operator may split E, but it is a
    # generic physical perturbation, not unique to any 369 theory.
    DELTA=sp.symbols("Delta",real=True)
    DEFECT=sp.diag(DELTA,0,0)
    ck("physical anisotropic operator breaks C3v",DEFECT*ROT!=ROT*DEFECT)
    ck("zero physical perturbation has no new response",DEFECT.subs(DELTA,0)==sp.zeros(3))
    ck("source no-shear case triple degeneracy",BASE.subs(S,0)==D*sp.eye(3))
    return {"all_passed":True,"checks_passed":len(tests),
       "source":"Original DASHI GaAs111BirPikusC3vFiniteExact, Atom P2 Coulomb (21/128)I3",
       "exact_A1_eigenvalue":"D + 2*S",
       "exact_E_eigenvalue":"D - S (double)",
       "selected_p2_scalar_shift":"21/128 common abstract scalar illustration ONLY; physically different Hilbert sector",
       "forbid_importing_p2_scalar_as_measured_GaAs_BirPikus_energy":True,
       "source_C3v_BirPikus_and_scalar_p2_alone_369_specific_advantage":False,
       "new_physical_anisotropy_must_be_source_backed":True,
       "GaAs_full_spinful_8band_or_optical_response_certified":False,
       "measured_net_PCE_or_369_gain":False,
       "checks":tests}

if __name__=="__main__":print(json.dumps(theorem(),indent=2))

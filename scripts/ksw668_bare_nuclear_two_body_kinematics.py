#!/usr/bin/env python3
"""C1 physical *BARE nucleus* 14N+n -> 14C+p two-body kinematics.

Source inputs:
  2022 CODATA mp=1.0072764665789 u, me=0.0005485799090441 u,
  conversion 931.49410242 MeV/u.
  2022 CODATA neutron / NIST neutral isotopic AME masses as cited in prior
  KSW receipt, retaining their limited digits.
  2024 NIST ASD v5.12 DOI 10.18434/T4W30F successive ionizations:
  N total 1486.0578277 eV; C total 1030.10849879 eV;
  H I 13.598434599702 eV.

Use precision-limited atomic inputs for bare nuclear rest energies; exact
two-body COM energy and momentum conservation at zero target/neutron relative
motion (idealized threshold benchmark), not an observed neutron laboratory
energy spectrum or physical in-vivo reaction. Original nuclear excited-state,
gamma/electronic final-state branching must be separately measured.
"""
import json
from decimal import Decimal as D, getcontext
getcontext().prec=44
U=D("931.49410242")
ME=D("0.0005485799090441")
MP=D("1.0072764665789")
MN=D("1.00866491595")
N_ATOM=D("14.00307400443")
C_ATOM=D("14.0032419884")
H_ATOM=D("1.00782503223")
N_BIND_eV=D("1486.0578277")
C_BIND_eV=D("1030.10849879")
H_BIND_eV=D("13.598434599702")

def calculate():
    # Bare nuclear mass: neutral atom minus bound electron masses PLUS
    # electronic binding energy, with ordinary atomic isotope shifts ignored.
    N_bare_MeV=(N_ATOM-7*ME)*U+N_BIND_eV/D(1_000_000)
    C_bare_MeV=(C_ATOM-6*ME)*U+C_BIND_eV/D(1_000_000)
    proton_MeV=MP*U
    neutron_MeV=MN*U
    W=N_bare_MeV+neutron_MeV
    outgoing_rest=C_bare_MeV+proton_MeV
    Q_bare=W-outgoing_rest
    if Q_bare<=0:raise AssertionError("Original reaction is not exothermic")
    E_C=(W*W+C_bare_MeV*C_bare_MeV-proton_MeV*proton_MeV)/(2*W)
    E_p=(W*W+proton_MeV*proton_MeV-C_bare_MeV*C_bare_MeV)/(2*W)
    p2=E_C*E_C-C_bare_MeV*C_bare_MeV
    if p2<0:raise AssertionError("Kallen momentum squared negative")
    p=p2.sqrt()
    # Actual on-shell equal and opposite final momenta, NOT 2 neutral atoms.
    assert E_C+E_p==W
    assert E_C*E_C-p*p==C_bare_MeV*C_bare_MeV
    assert abs((E_p*E_p-p*p)-proton_MeV*proton_MeV)<D("1e-32")
    TC=E_C-C_bare_MeV
    Tp=E_p-proton_MeV
    assert abs(TC+Tp-Q_bare)<D("1e-32")
    Q_atomic=(N_ATOM+MN-C_ATOM-H_ATOM)*U
    Q_binding=Q_atomic+(N_BIND_eV-C_BIND_eV-H_BIND_eV)/D(1_000_000)
    # Independent proton/electron CODATA constants and rounded neutral mass
    # inputs disagree at sub-eV level. Reconciliation is an uncertainty gate.
    discrepancy_eV=(Q_bare-Q_binding)*D(1_000_000)
    assert abs(discrepancy_eV)<D(1)
    assert D(".626")<Q_bare<D(".627")
    return {
        "schema":"dashi.ksw668.bare-nucleus-two-body-kinematics-v1",
        "source_mass_precision":"Original independent AME/CODATA rounded values; uncertainty covariance not joined",
        "real_physical_final_state":"14C6+ bare nucleus + free proton",
        "initial_state":"14N7+ bare nucleus + free neutron, both COM at rest",
        "mass_MeV_c2":{k:str(v) for k,v in {
          "14N7+_bare":N_bare_MeV,"neutron":neutron_MeV,
          "14C6+_bare":C_bare_MeV,"proton":proton_MeV
        }.items()},
        "Q_bare_kinematics_MeV":str(Q_bare),
        "Q_from_neutral_atoms_plus_electron_binding_MeV":str(Q_binding),
        "independent_mass_constants_discrepancy_eV":str(discrepancy_eV),
        "final_center_of_mass":{
            "carbon_14_total_energy_MeV":str(E_C),
            "proton_total_energy_MeV":str(E_p),
            "carbon_14_kinetic_MeV":str(TC),
            "proton_kinetic_MeV":str(Tp),
            "opposed_3_momentum_magnitude_MeV_c":str(p)
        },
        "energy_conservation":"PASS Decimal",
        "three_momentum_conservation":"PASS +p and -p",
        "daughter_on_shell":"PASS",
        "physical_limitations":[
          "Real neutral N14 target has 7 bound electrons; this is not its immediate two-body final-state observable",
          "Any unchanged charge environment/photons/free electrons must be modelled explicitly",
          "Mass constants contain rounded old AME/CODATA values (sub-eV mismatch)",
          "No incident neutron kinetic distribution, angular cross-section or final-state branching measured here",
          "No actual biological reaction rate or same-body emotional intervention",
        ]
    }

if __name__=="__main__":
    print(json.dumps(calculate(),indent=2))

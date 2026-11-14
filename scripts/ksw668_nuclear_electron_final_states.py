#!/usr/bin/env python3
"""C1 original NIST neutral-atom/nuclear channel and ionization correction.

Sources:
- Original measured neutral atomic masses in u (AME/NIST used by KSW668).
- NIST ASD 5.12 ionization energies for N I--VII, C I--VI, H I
  DOI 10.18434/T4W30F, accessed Nov 2026.
- 2022 CODATA mass-to-energy conversion 931.49410242 MeV/u.
Atomic neutral Q does NOT describe a bare-nucleus 2-body final-state
with the electrons disappearing; bound/unbound electronic state changes
the photon/electron-inclusive final state.

Ground-state electron binding is sum of successive ionization energies.
Small differences between hydrogen electron affinity, vibrational/
recombination photon, ionic excitations and nuclear recoil are NOT
silently discarded. This comparison uses the listed NIST neutral
isotope masses with their *published truncated digits*; some 14N vs
14C electron binding levels are approximated by the corresponding
standard element ionization table (isotope shifts not calibrated).
"""
from decimal import Decimal,getcontext
import json

getcontext().prec=50
D=Decimal
M14N=D("14.00307400443")
MN=D("1.00866491595")
M14C=D("14.0032419884")
MH=D("1.00782503223")
U_TO_MEV=D("931.49410242")
N_ION_eV=list(map(D,["14.53413","29.60125","47.4453","77.4735",
                      "97.8901","552.06741","667.0461377"]))
C_ION_eV=list(map(D,["11.2602880","24.383143","47.88778",
                      "64.49352","392.09056","489.99320779"]))
H_ION_eV=[D("13.598434599702")]


def calculate():
    assert len(N_ION_eV)==7 and len(C_ION_eV)==6
    assert all(x>0 for x in N_ION_eV+C_ION_eV+H_ION_eV)
    B_N=sum(N_ION_eV)
    B_C=sum(C_ION_eV)
    B_H=sum(H_ION_eV)
    electron_binding_correction=B_N-B_C-B_H
    Qatomic=(M14N+MN-M14C-MH)*U_TO_MEV*D(1_000_000)
    # Fully stripped 14N(7+) + n -> 14C(6+) + p in two bodies.
    Qnuclear=Qatomic+electron_binding_correction
    # Electronic states matter: this is a *three body* channel after reaction:
    # 14N(neutral)+n -> 14C(neutral)+p(bare)+e-(free) [if kinematically allowed].
    Q_C_neutral_p_e_free=Qatomic-B_H
    # Full initial neutral nitrogen target, final bare C nucleus, p and 7e.
    Q_C_bare_p_7e_free=Qnuclear-B_N
    assert Qnuclear-Qatomic==electron_binding_correction
    assert Q_C_neutral_p_e_free+B_H==Qatomic
    assert Q_C_bare_p_7e_free+B_N==Qnuclear
    assert electron_binding_correction==D("442.350894310298")
    assert Qatomic==D("625870.654542472395")
    assert Qnuclear==D("626313.005436782693")
    assert Q_C_neutral_p_e_free==D("625857.056107872693")
    # Atomic neutral C+H two-body is asymptotic effective chemical channel,
    # not an instantaneous nuclear 2-body production proof.
    return {
       "schema":"dashi.ksw668.original-n14-np-ionization-reaction-ledger.v1",
       "status":"PASS exact decimal bookkeeping; NO final-state spectrum measured",
       "sources":{
          "NIST_ASD":"10.18434/T4W30F, N I-VII, C I-VI, H I",
          "CODATA_2022":"2022 recommended constants, u-to-MeV 931.49410242",
          "atomic_masses_source":"previous original KSW668 AME/NIST neutral ground state mass ledger"
       },
       "input_mass_u":{k:str(v) for k,v in {
         "14N_atom":M14N,"n":MN,"14C_atom":M14C,"1H_atom":MH
       }.items()},
       "nuclear_charge_protons":{"reactants":7,"products":6+1},
       "neutron_number":{"reactants":7+1,"products":8+0},
       "electron_inventory":{"initial_N_atom":7,
         "neutral_C_plus_neutral_H":6+1,
         "neutral_C_plus_bare_p_plus_free_e":6+0+1,
         "bare_C_plus_bare_p_plus_7free_e":0+0+7},
       "published_NIST_electronic_binding_eV":{
         "N_sum":str(B_N),"C_sum":str(B_C),"H_sum":str(B_H),
         "nuclear_minus_neutral_atomic_Q":str(electron_binding_correction)
       },
       "Q_reaction_eV":{
         "ground_neutral_atom_N_n_to_ground_neutral_atom_C_H":str(Qatomic),
         "bare_nuclei_N_n_to_C_p":str(Qnuclear),
         "N_neutral_n_to_C_neutral_p_bare_e_free":str(Q_C_neutral_p_e_free),
         "N_neutral_n_to_C_bare_p_bare_7e_free":str(Q_C_bare_p_7e_free)
       },
       "not_established":[
         "actual charged final state and molecular/ionic environmental channels",
         "three-body differential recoil/energy-angle distribution",
         "nuclear excited-state branching or gamma/electron radiation",
         "neutron fluence vs energy and true reaction rates",
         "time-dependent recombination, electron shake-off and recoil corrections",
         "joint original mass and ionization-energy uncertainty covariance"
       ]
    }


if __name__=="__main__":
    print(json.dumps(calculate(),indent=2))

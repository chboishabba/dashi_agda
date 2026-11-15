#!/usr/bin/env python3
"""Source-locked published nickel energy anchors, NOT reexecuted results.

Source: Provazza, Knitter et al. arXiv:2611.08129v1 §IV.2 Table 2.
Original 2025 DFT anchors: Zhao et al. arXiv:2506.22408 §VI.6.
Units: absolute Hartree / relative kcal mol^-1.
"""
import json

NICKEL={
 "ideal_upccd_afqmc":{"B":(-2739.081,.003),"BC":(-2738.982,.003),
                       "C":(-2739.073,.003),"barrier":(62.2,2.4),"reaction":(4.9,3.0)},
 "nqs_afqmc":{"B":(-2739.083,.002),"BC":(-2738.984,.003),
              "C":(-2739.076,.003),"barrier":(62.6,2.1),"reaction":(4.5,2.6)},
 "shadow_afqmc":{"B":(-2739.040,.004),"BC":(-2738.972,.003),
                 "C":(-2739.059,.003),"barrier":(43.,3.),"reaction":(-12.,3.)},
 "rhf_phafqmc":{"B":(-2739.074,.003),"BC":(-2738.975,.005),
                "C":(-2739.096,.005),"barrier":(62.,4.),"reaction":(-14.,4.)},
 "ccsdt":{"B":(-2739.081251,None),"BC":(-2738.996283,None),
          "C":(-2739.068637,None),"barrier":(53.3,None),"reaction":(7.9,None)}
}
def verify():
    from math import sqrt
    factor=627.5094740631
    cc=NICKEL["ccsdt"]
    for key,where in (("barrier","BC"),("reaction","C")):
        delta=(cc[where][0]-cc["B"][0])*factor
        assert abs(delta-cc[key][0])<.12
    for name,p in NICKEL.items():
        # Published absolute AFQMC energies are rounded to ~0.001 Eh,
        # which can shift relative energies by up to ~0.63 kcal/mol.
        for key,where in (("barrier","BC"),("reaction","C")):
            delta=(p[where][0]-p["B"][0])*factor
            assert abs(delta-p[key][0])<1.0,(name,key,delta)
    return {"source":"https://arxiv.org/html/2611.08129v1#S4.SS2",
            "reported_energies":NICKEL,
            "source_data_not_newly_simulated":True,
            "rounded_absolute_energy_deltas_checked":True}

if __name__=="__main__":
    print(json.dumps(verify(),indent=2))

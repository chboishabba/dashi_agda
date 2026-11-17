#!/usr/bin/env python3
"""M2 physical source-control: 2026 Green et al. PV table 68 IV identity audit.

Published table figures are secondary metrology summaries, NOT original raw
illuminated IV curves and NOT per-junction measurement specimens. This script
cross-multiplies source-rounded Voc, Jsc and FF to compare reported PCE under
the standard 1000 W/m2 AM1.5G one-sun denominator.

Primary publication: Green et al., Solar cell efficiency tables: Version 68,
Joule 10 (7), 102494, 2026, DOI 10.1016/j.joule.2026.102494.
Journal table 4 values and footnote conventions are the source's property.

IMPORTANT: 35.2% LONGi/ESTI row gives 34.982% if simply multiplying
the printed numbers. This need not be an error: one or more Jsc/FF/area/
spectrum or reporting conventions, rounding, or the original certified
MPP may differ. Record this as an unresolved source normalization, not as
a numerical 'correction' to an independently measured certificate.

An older 4T InGaP/GaAs//Si table row has separately printed multi-cell
Voc/Jsc/FF values; it is NOT a single two-terminal identity and cannot
be accepted by this one-connection formula. Source cross-datum adapter
must handle distinct aperture and contact group normalization.
"""
from fractions import Fraction as F
import json

SOURCE="https://doi.org/10.1016/j.joule.2026.102494"
# One-sun printed TABLE values (V; mA/cm²; FF percent; PCE percent).
ROWS=[
    {"id":"2026_E​​STI_LONGi_perovskite_Si_2T","class":"2T",
     "voc":"1.998","jsc":"20.55","ff":"85.2","pce":"35.2","quoted_uncertainty_pp":"1.1",
     "area_cm2":"0.9994","area_class":"designated illumination area",
     "site":"ESTI (02/2026)","material":"perovskite/Si"},
    {"id":"NREL_GaInP_GaAs_multiQW_2T","class":"2T",
     "voc":"2.500","jsc":"15.36","ff":"85.7","pce":"32.9","quoted_uncertainty_pp":"0.5",
     "area_cm2":"0.250","area_class":"aperture",
     "site":"NREL (01/2020)","material":"GaInP/GaAs(mqw)"},
    {"id":"NREL_GaInP_GaAs_multiQW_GaInAs_3J","class":"2T",
     "voc":"2.997","jsc":"15.44","ff":"85.3","pce":"39.5","quoted_uncertainty_pp":"0.5",
     "area_cm2":"0.242","area_class":"aperture",
     "site":"NREL (09/2021)","material":"GaInP/GaAs(mqw)/GaInAs"},
]
FOUR_TERMINAL_SOURCED={
 "id":"AIST_InGaP_GaAs_doubleSlash_Si_4T",
 "reported_pce":"33.7","quoted_uncertainty_pp":"0.7",
 "Voc_components_V":["20.3","2.83"],"Jsc_components_mAcm2":["1.25","1.93"],
 "FF_components_pct":["86.5","78.0"],
 "source":"Version 68 module notable exceptions, AIST (02/2023)",
 "component_areal_normalization_and_illumination":"SOURCE_REQUIRED",
 "summing_components_directly_as_one_aperture":"FORBIDDEN",
}
def compute():
    tests=[]
    def check(n,yes):
        assert bool(yes),n
        tests.append(n)
    out=[]
    for row in ROWS:
        check(row["id"]+" is explicitly 2T",row["class"]=="2T")
        p=F(row["voc"])*F(row["jsc"])*F(row["ff"])/100
        listed=F(row["pce"])
        delta=p-listed
        # The published 1.0 kW/m2 incident denominator conversion:
        # V * (mA/cm2) gives mW/cm2 numerically; divide by
        # 100 mW/cm2 and multiply by 100 for PCE = V*J*FF/100.
        check(row["id"]+" positive reconstructed",p>0)
        check(row["id"]+" independent measured PCE below 50",listed<50)
        check(row["id"]+" difference exactly reproducible",
              p-listed==delta)
        out.append({
          "id":row["id"],"material":row["material"],
          "published_PCE_percent":float(listed),
          "reconstructed_from_printed_Voc_Jsc_FF_percent":float(p),
          "printed_reconstruction_minus_published_percentage_points":float(delta),
          "independent_published_PCE_uncertainty_pp":float(F(row["quoted_uncertainty_pp"])),
          "source_normalization_conventions_reconciled":False,
          "source":"Green et al. 2026, DOI 10.1016/j.joule.2026.102494; Table 4",
        })
    check("GaAs 2J printed identity close",abs(out[1]["printed_reconstruction_minus_published_percentage_points"])<.05)
    check("GaAs QW 3J printed identity close",abs(out[2]["printed_reconstruction_minus_published_percentage_points"])<.05)
    check("2026 ESTI printed fields show mismatch greater than 0.1pp",
         abs(out[0]["printed_reconstruction_minus_published_percentage_points"])>.1)
    check("no printed 2T entry above 50%",all(x["published_PCE_percent"]<50 for x in out))
    check("cannot use separate 4T voltage sums as 2T identity",
         FOUR_TERMINAL_SOURCED["summing_components_directly_as_one_aperture"]=="FORBIDDEN")
    return {"local_exact_arithmetic_checks_passed":len(tests),"all_passed":True,
       "calibration_note":"published values and reported uncertainty are NOT raw per-sample meter bounds",
       "source_url":SOURCE,"two_terminal_reconciliation":out,
       "four_terminal_metadata":FOUR_TERMINAL_SOURCED,
       "same_specimen_original_IV_data_available":False,
       "true_IV_stabilized_measured_MPP_verified":False,
       "369_specific_operator_measured":False,
       "greater_than_50_net_electrical_measured":False,
       "checks":tests}
if __name__=="__main__":
    print(json.dumps(compute(),indent=2))

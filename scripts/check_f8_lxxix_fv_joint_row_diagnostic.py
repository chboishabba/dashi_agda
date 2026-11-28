"""Native finite-volume source against the idealized joint moment row.

This is a discrepancy diagnostic, not the certified rational Taylor weak-load
source of check_f8_lxxviii_joint_moments.py.  Execute locally.
"""
import numpy as np
from ksw668_f8_fv_source_flux import exact_cell_averages, total_scaled_moments

def check():
    eps = .04
    target = total_scaled_moments()
    for dr in (.008, .004, .002, .001):
        r = np.arange(round(.096 / dr) + 1) * dr
        src = exact_cell_averages(eps, r, dr)
        moments = []
        centred_second = []
        for q, d in enumerate((3, 7, 11)):
            low = np.maximum(0., r - dr/2)
            shell = ((r + dr/2)**d - low**d) / d
            b = src[q] * shell / eps**d
            moments.append(float(np.sum(b)))
            centred_second.append(float(np.dot((r/eps)**2, b)))
        discrepancy = 9 * centred_second[1] - 40 * moments[2]
        assert np.isfinite(src).all()
        assert abs(moments[0]) < 2e-10
        assert abs(moments[1]) < 2e-10
        assert abs(moments[2] - target["l4"]) < 2e-9
        print(f"dr={dr:g} masses={moments} "
              f"centred_second_l2={centred_second[1]:.15g} "
              f"joint_row_defect={discrepancy:.15g}", flush=True)

if __name__ == "__main__":
    check()

#!/usr/bin/env python3
"""Native J12/J16 restored-cycle wave absorption reverse solve (synthetic).

Exactly consumes the source-authored J12 finite switched circuit and its
seven-state storage / diode / spark / outgoing wave definitions.
No real Filsinger pin assignment, environmental source gain, or gravity result.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import sympy as S
from scipy.optimize import brentq
import check_smith_filsinger_j12_restored_cycles_20261122 as native

NATIVE_BLOB = "f5f66e343a979dfe2bc70f68e1e98fce75817653"
P = native.BASE | dict(Von=.003, Voff=.0009, source_amp=1.2)
KEYS = ("driver", "incident", "outgoing", "net_wave", "spark", "diode",
        "heat", "storage_delta", "closure", "residual", "switches", "cycles")


def git_blob(path):
    data = Path(path).read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\x00" + data).hexdigest()


def cycle(a=1.2, phase=.3, **parameters):
    r = native.periodic(P | dict(source_amp=a) | parameters, True, phase,
                        max_iter=18, tol=2e-6)
    assert abs(r["residual"]) < 1e-6
    assert abs(r["storage_delta"]) < 1e-5
    assert r["closure"] < 2e-6
    assert abs(r["incident"] - r["outgoing"] - r["net_wave"]) < 1e-7
    return r


def brief(r):
    return {k: float(r[k]) for k in KEYS}


def event_pair(**params):
    left, right = cycle(**params["minus"]), cycle(**params["plus"])
    el, er = left["event_log"], right["event_log"]
    matched = len(el) == len(er) and [x[1] for x in el] == [x[1] for x in er]
    max_shift = max((abs(x[0]-y[0]) for x,y in zip(el,er)), default=0.) if matched else None
    return {"minus_events": len(el), "plus_events": len(er),
            "same_labels_and_counts": matched, "max_event_time_shift": max_shift,
            "positive_work_both": bool(left["net_wave"] > 0 and right["net_wave"] > 0),
            "local_shift_below_0_1": bool(matched and max_shift is not None and max_shift < .1)}


def main():
    assert git_blob(native.__file__) == NATIVE_BLOB
    sr, si, q, z, h = S.symbols("sr si q z h", real=True)
    net = (sr*sr + si*si) - ((sr-h*q)**2 + (si-h*z)**2)
    assert S.simplify(net - (2*h*(sr*q+si*z) - h*h*(q*q+z*z))) == 0
    baseline = cycle(a=0.)
    positive = cycle(a=1.2)
    assert baseline["net_wave"] < 0 and positive["net_wave"] > 0
    assert positive["spark"] > 0
    root = brentq(lambda a: cycle(a=a)["net_wave"], .8, 1.2,
                  xtol=3e-4, rtol=1e-6, maxiter=14)
    near = cycle(a=root)
    assert abs(near["net_wave"]) < 1e-3
    scan = {
        "weak_coil_coupling": cycle(k=.08),
        "strong_coil_coupling": cycle(k=.25),
        "weak_radiative_coupling": cycle(gamma_rad=.04),
        "strong_radiative_coupling": cycle(gamma_rad=.16),
        "lower_diode_drop": cycle(Vd=.05),
        "higher_diode_drop": cycle(Vd=.15),
        "quarter_phase": cycle(phase=math.pi/2),
        "opposite_phase": cycle(phase=math.pi),
    }
    assert scan["weak_coil_coupling"]["net_wave"] > 0
    assert scan["strong_coil_coupling"]["net_wave"] < 0
    assert scan["weak_coil_coupling"]["spark"] < positive["spark"]
    assert scan["strong_coil_coupling"]["spark"] > positive["spark"]

    event_checks = {
        "incident_amplitude": event_pair(minus={"a":1.195}, plus={"a":1.205}),
        "source_phase": event_pair(minus={"phase":.295}, plus={"phase":.305}),
        "circuit_coupling": event_pair(minus={"k":.145}, plus={"k":.155}),
    }
    assert all(x["same_labels_and_counts"] and x["positive_work_both"]
               for x in event_checks.values())
    # Backwards-compatible new native J12 drive-amplitude parameter: original
    # driver remains amplitude 2 unless overridden; this is only a control.
    controls = {}
    for name, amp, driver in (("both_off",0.,0.), ("wave_only",1.2,0.),
                              ("drive_only",0.,2.), ("both_on",1.2,2.)):
        p = P | dict(source_amp=amp, drive_amp=driver)
        _, _, r = native.advance(p, bool(amp), .3, np.zeros(7), False, 0.)
        assert abs(r["residual"]) < 1e-6
        controls[name] = {k:float(r[k]) for k in ("driver","incident","outgoing",
                           "net_wave","spark","storage_delta","residual","switches")}
    assert all(controls["both_off"][k] == 0 for k in
               ("driver","incident","outgoing","spark","storage_delta"))
    assert controls["wave_only"]["driver"] == 0
    assert controls["wave_only"]["storage_delta"] != 0  # NOT restored source-only
    result = {
        "status": "PASS_LOCAL_SYNTHETIC_NATIVE_J12_J16",
        "native_blob": NATIVE_BLOB,
        "scope": "dimensionless model; no historical concurrent sources or experimental calibration",
        "restored_driver_only": brief(baseline),
        "restored_positive_absorber": brief(positive),
        "root_amplitude": root, "root_bracket": [.8,1.2],
        "root_work": brief(near), "phase_rad": .3, "thresholds": [.003,.0009],
        "tradeoff": {k:brief(v) for k,v in scan.items()},
        "local_event_pairs": event_checks,
        "one_interval_driver_source_controls": controls,
        "driver_off_restored_cycle_certified": False,
        "root_event_branch_globally_smooth": False,
        "physical_filsinger_input_output_measured": False,
        "agda_kernel_checked": False, "ci_used": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

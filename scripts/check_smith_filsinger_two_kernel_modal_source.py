#!/usr/bin/env python3
"""Same-original audio, two physically unassigned upper-band response kernels.

Requires: python scripts/check_smith_filsinger_two_kernel_modal_source.py ReelAudio-93787.mp3
Original source SHA256 in Docs/research/... roadmap. Does NOT measure real
electrical resonances, propagation time or Earth/ionosphere energy.
"""
import hashlib
import json
import sys

import numpy as np
import soundfile as sf
from scipy.signal import welch

# Fitted from the same-original upper-band shutdown acoustic envelope by
# fit_stable_causal_paths.py, recorded in source acceptance ledger.
FIT = {
    "common_trigger_s": 60.32281169246357,
    "first_peak_delay_s": 0.09146308900401089,
    "first_shape": 3.795431818713989,
    "second_path_onset_delay_s": 0.3032210634851742,
    "second_peak_delay_s": 0.09055531585985926,
    "second_shape": 1.4624564786113166,
}
WINDOWS = ((60.36, 60.46), (60.66, 60.76))
EXPECTED_SHA256 = "573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6"

def first_and_second_peak_times():
    f = FIT
    return (f["common_trigger_s"] + f["first_peak_delay_s"],
            f["common_trigger_s"] + f["second_path_onset_delay_s"]
              + f["second_peak_delay_s"])

def band_shape(x, fs, start, stop):
    segment = x[int(start*fs):int(stop*fs)]
    f, spectrum = welch(segment, fs, window="hann", nperseg=4096,
                        noverlap=2048)
    mask=(f >= 7950) & (f < 8400)
    f, p=f[mask], spectrum[mask]
    probabilities=p/p.sum()
    return {
      "window_s": [start,stop],
      "peak_hz":float(f[np.argmax(p)]),
      "centroid_hz":float(np.dot(f,probabilities)),
      "spectral_flatness":float(np.exp(np.mean(np.log(p + 1e-40)))/np.mean(p)),
      "normalised_entropy":float(-np.sum(probabilities*np.log(probabilities + 1e-30))/np.log(len(p))),
      "bin_width_hz":float(fs/4096)
    }

def main(filename):
    data=open(filename,"rb").read()
    sha=hashlib.sha256(data).hexdigest()
    if sha != EXPECTED_SHA256:
        raise ValueError("Original audio SHA256 mismatch; no cross-reel promotion")
    x,fs=sf.read(filename)
    assert fs==44100 and abs(len(x)/fs-105.795918)<1e-4
    x=x.mean(axis=1) if x.ndim>1 else x
    shapes=[band_shape(x,fs,*window) for window in WINDOWS]
    first,second=first_and_second_peak_times()
    f=FIT
    out={
      "source_sha256":sha,
      "common_trigger_s":f["common_trigger_s"],
      "path_peak_times_s":[first,second],
      "path_peak_separation_s":second-first,
      "conditional_late_envelope_decay_scales_s":[
        f["first_peak_delay_s"]/f["first_shape"],
        f["second_peak_delay_s"]/f["second_shape"]],
      "spectral_windows":shapes,
      "status":"Source-observed spectral difference and fitted acoustic kernels. NO physical mode IDs."
    }
    assert .29 < out["path_peak_separation_s"] < .31
    assert shapes[0]["normalised_entropy"] > shapes[1]["normalised_entropy"]
    assert shapes[0]["spectral_flatness"] > .4
    assert shapes[1]["spectral_flatness"] < .05
    assert abs(shapes[1]["peak_hz"]-8021)<20
    print(json.dumps(out,indent=2))
    print("PASS 5/5 original-acoustic two-kernel modal discrimination")

if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit("Usage: .../check_smith_filsinger_two_kernel_modal_source.py original.mp3")
    main(sys.argv[1])

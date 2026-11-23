#!/usr/bin/env python3
"""Duga 1984 historical audio provenance and conditional timing replay.

Original credited recording: Rolypolyman, 2 November 1984,
https://commons.wikimedia.org/wiki/File:Woodpecker.ogg
Independent archive republication 23 October 2026:
https://shortwavearchive.com/archive/russian-woodpecker-duga-1-heard-behind-wwvh-november-2-1984

Never infer absolute field, transmitting HF spectrum, carrier power or
biological effects from receiver-demodulated, compressed mixed WWVH audio.
No audio is embedded: if retrieval is blocked, only synthetic checks run.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import scipy.signal as signal
import soundfile as sf
import sympy as S

SOURCE = "https://commons.wikimedia.org/wiki/File:Woodpecker.ogg"

def peak_in_envelope(x, sample_rate, low=6, high=25):
    x=np.asarray(x,dtype=float)
    if len(x)<sample_rate or not np.all(np.isfinite(x)):
        raise ValueError("need >=1 second finite uncompressed audio samples")
    x=x-np.mean(x)
    envelope=np.abs(signal.hilbert(x))
    f,p=signal.periodogram(envelope-np.mean(envelope),fs=sample_rate)
    region=(f>=low)&(f<=high)
    if not region.any():
        raise ValueError("audio rate/duration cannot resolve requested band")
    return float(f[region][np.argmax(p[region])])

def synthetic_fixture():
    rate=2000
    t=np.arange(6000,dtype=float)/rate
    x=(1+0.45*np.cos(2*np.pi*10*t))*np.cos(2*np.pi*400*t)
    detected=peak_in_envelope(x,rate)
    assert abs(detected-10.0)<1e-9
    e,g,k=S.symbols('e gain k',nonzero=True,real=True)
    assert S.simplify((e*k)*(g/k)-e*g)==0
    assert S.simplify((e*k)**2-e**2)!=0
    return {"fixture":"PASS","synthetic_detected_envelope_hz":detected,
            "gain_field_nonidentifiability":"PASS","uses_original_audio":False}

def analyse(filename):
    filename=Path(filename)
    data=filename.read_bytes()
    if not data.startswith(b'OggS'):
        raise ValueError("Original archive is Ogg; refuse non-Ogg replacement without provenance review")
    x,fs=sf.read(filename,always_2d=True)
    mono=x.mean(axis=1)
    sha=hashlib.sha256(data).hexdigest()
    peak=peak_in_envelope(mono,fs)
    return {"status":"AUDIO_TIMING_ONLY_NOT_CALIBRATED_RF",
            "source":SOURCE,"original_file_sha256":sha,
            "compressed_audio_bytes":len(data),"audio_rate_hz":fs,
            "duration_s":len(mono)/fs,
            "detected_audio_envelope_peak_6_to_25_hz":peak,
            "HF_carrier_measured":False,"original_receiver_calibration_known":False,
            "biological_or_schumann_transfer_established":False,
            "warning":"A 6-25 Hz audio envelope peak is not calibrated emitted 6-25 Hz electromagnetic radiation."}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original-ogg',type=Path)
    args=parser.parse_args()
    outcome=analyse(args.original_ogg) if args.original_ogg else {
        "status":"NO_ORIGINAL_AUDIO_LOCAL_SYNTHETIC_ONLY",
        "source":SOURCE,
        "synthetic_acceptance":synthetic_fixture()}
    print(json.dumps(outcome,indent=2,sort_keys=True))

if __name__=="__main__":
    main()

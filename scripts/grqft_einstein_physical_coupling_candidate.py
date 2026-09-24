#!/usr/bin/env python3
"""Replay the vendored CODATA-G row into the physical Einstein coupling.

This is a diagnostic/value-candidate producer.  It does not create the typed
accepted measured-authority token required for physical promotion.
"""
from __future__ import annotations
import argparse, hashlib, json, math, re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
DEFAULT=ROOT/"data/authority/si_metrology_20260615/nist_constants_allascii_2022.txt"
EXPECTED_SHA="77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"
C=299792458.0

def parse_g(path:Path):
    raw=path.read_bytes()
    sha=hashlib.sha256(raw).hexdigest()
    text=raw.decode("utf-8",errors="replace")
    line=next(x for x in text.splitlines() if x.startswith("Newtonian constant of gravitation "))
    m=re.search(r"gravitation\s+([0-9. ]+e[-+][0-9]+)\s+([0-9. ]+e[-+][0-9]+)\s+(.*)$",line)
    if not m: raise RuntimeError("could not parse CODATA G row")
    def f(s): return float(s.replace(" ",""))
    return sha,line,f(m.group(1)),f(m.group(2)),m.group(3).strip()

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--source",type=Path,default=DEFAULT)
    p.add_argument("--output",type=Path,default=ROOT/"outputs/grqft_einstein_physical_coupling_candidate.json")
    a=p.parse_args()
    sha,line,G,uG,unit=parse_g(a.source)
    if a.source.resolve()==DEFAULT.resolve() and sha!=EXPECTED_SHA:
        raise AssertionError(f"CODATA artifact digest changed: {sha}")
    k8=8*math.pi*G
    uk8=8*math.pi*uG
    k=k8/C**4
    uk=uk8/C**4
    out={
      "artifactSchema":"dashi-grqft-einstein-physical-coupling-candidate-v1",
      "source":{"path":str(a.source.relative_to(ROOT) if a.source.is_relative_to(ROOT) else a.source),"sha256":sha,"row":line},
      "convention":"energy-density: G_mu_nu = (8*pi*G/c^4) T_mu_nu",
      "G":{"value":G,"standardUncertainty":uG,"unit":unit,"relativeStandardUncertainty":uG/G},
      "c":{"value":299792458,"unit":"m s^-1","exact":True},
      "eightPiG":{"value":k8,"standardUncertainty":uk8},
      "eightPiGOverC4":{"value":k,"standardUncertainty":uk,"unit":"m J^-1"},
      "typedAcceptedGAuthorityTokenPresent":False,
      "typedGNumericValueLoaded":False,
      "physicalCouplingPromoted":False
    }
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__": main()

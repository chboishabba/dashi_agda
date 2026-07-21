#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
from typing import Any
from ns_periodic_concrete_proof_program import far_high_scan
SCHEMA='ns_radius8_far_high_scan.v1'
def d(x:Any)->str:return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output-json',type=Path,required=True);ap.add_argument('--pretty',action='store_true');a=ap.parse_args();p={'schema':SCHEMA,'scan':far_high_scan(),'promotion':{'official_constants_identified':False,'universal_far_high':False}};p['sha256']=d(p);a.output_json.parent.mkdir(parents=True,exist_ok=True);t=json.dumps(p,sort_keys=True,indent=2 if a.pretty else None)+'\n';a.output_json.write_text(t);print(t,end='')
if __name__=='__main__':main()

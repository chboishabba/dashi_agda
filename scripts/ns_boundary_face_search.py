#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
from typing import Any
from ns_periodic_concrete_proof_program import boundary_ledgers
SCHEMA='ns_boundary_face_search.v1'
def d(x:Any)->str:return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output-json',type=Path,required=True);ap.add_argument('--pretty',action='store_true');a=ap.parse_args();p={'schema':SCHEMA,'faces':boundary_ledgers(),'promotion':{'pde_derivatives_identified':False,'strict_inwardness':False}};p['sha256']=d(p);a.output_json.parent.mkdir(parents=True,exist_ok=True);t=json.dumps(p,sort_keys=True,indent=2 if a.pretty else None)+'\n';a.output_json.write_text(t);print(t,end='')
if __name__=='__main__':main()

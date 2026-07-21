#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path
from typing import Any

def d(x:Any)->str:return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def verify(path:Path)->dict[str,Any]:
 p=json.loads(path.read_text()); supplied=p.pop('sha256',None); return {'file':path.name,'digest':supplied==d(p),'promotion_false':all(v is False for v in p['promotion'].values())}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inputs',type=Path,nargs='+',required=True);ap.add_argument('--output-json',type=Path,required=True);a=ap.parse_args();rows=[verify(x) for x in a.inputs];out={'schema':'check_ns_periodic_phase_receipts.v1','receipts':rows,'ok':all(r['digest'] and r['promotion_false'] for r in rows)};a.output_json.parent.mkdir(parents=True,exist_ok=True);a.output_json.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,sort_keys=True,indent=2));raise SystemExit(0 if out['ok'] else 1)
if __name__=='__main__':main()

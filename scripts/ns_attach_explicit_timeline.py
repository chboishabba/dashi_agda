#!/usr/bin/env python3
"""Attach a strict explicit physical timeline to legacy NS export receipts."""
from __future__ import annotations
import argparse,json,math,os,tempfile
from pathlib import Path
from typing import Any


def parse_times(raw:str)->tuple[float,...]:
    values=tuple(float(x.strip()) for x in raw.split(',') if x.strip())
    if not values or any(not math.isfinite(x) for x in values): raise ValueError('times must be finite')
    if any(b<=a for a,b in zip(values,values[1:])): raise ValueError('times must be strictly increasing')
    return values

def atomic(path:Path,payload:dict[str,Any],pretty:bool=False)->None:
    path.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.NamedTemporaryFile('w',encoding='utf-8',dir=path.parent,delete=False) as h:
        tmp=Path(h.name);json.dump(payload,h,indent=2 if pretty else None,sort_keys=True);h.write('\n');h.flush();os.fsync(h.fileno())
    try:os.replace(tmp,path)
    finally:
        if tmp.exists():tmp.unlink()

def attach(payload:dict[str,Any],times:tuple[float,...],trajectory_id:str)->dict[str,Any]:
    receipts=payload.get('export_receipts')
    if not isinstance(receipts,list) or not receipts:raise ValueError('input has no export_receipts')
    if len(receipts)!=len(times):raise ValueError('time count must equal receipt count')
    result=dict(payload);updated=[]
    for receipt,time in zip(receipts,times):
        row=dict(receipt);row['trajectory_id']=trajectory_id;row['time']=time;row.pop('duration',None);row.pop('parabolic_duration',None);updated.append(row)
    result['export_receipts']=updated;result['trajectory_id']=trajectory_id;result['timeline_receipt']={'explicit_physical_times':list(times),'strictly_increasing':True,'terminal_duration_assigned':False,'truth_authority':False,'theorem_authority':False,'promoted':False}
    return result

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input-json',type=Path,required=True);p.add_argument('--output-json',type=Path,required=True);p.add_argument('--times',required=True);p.add_argument('--trajectory-id',required=True);p.add_argument('--pretty',action='store_true');a=p.parse_args();result=attach(json.loads(a.input_json.read_text()),parse_times(a.times),a.trajectory_id);atomic(a.output_json,result,a.pretty);print(json.dumps({'output_json':str(a.output_json),'checkpoint_count':len(result['export_receipts'])},sort_keys=True))
if __name__=='__main__':main()

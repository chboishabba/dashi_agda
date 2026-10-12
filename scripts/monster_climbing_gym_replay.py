#!/usr/bin/env python3
"""Reproduce the JMD Monster Climbing Gym hole/mutual-pair table.

Diagnostic numerical producer, not a formal zeta-zero certificate. For wall
N=p**a, holes are h_m=2*pi*m/(N*log(p)) inside [t_1+1,t_849-1].
"""
from __future__ import annotations
import argparse, bisect, json, math
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_WALLS=((2,1),(3,1),(5,1),(7,1),(11,1),(2,2),(3,2),(2,3),(13,1),(71,1))
NON_OGG_CONTROLS=(37,43,53,61,67)
SOURCE_COUNTS={(2,1):(271,270),(3,1):(644,581),(5,1):(1571,820),(7,1):(2660,845),(11,1):(5151,849),(2,2):(542,513),(3,2):(1931,841),(2,3):(1083,773),(13,1):(6511,849),(71,1):(59099,849)}


def load_zero_cache(path:Path)->list[float]:
    p=json.loads(path.read_text())
    if "ordinates" in p: z=[float(x) for x in p["ordinates"]]
    else:
        scale=int(p["scale"]); enc=[int(x) for x in p["first_plus_deltas"]]; z=[]; cur=0
        for i,v in enumerate(enc): cur=v if i==0 else cur+v; z.append(cur/scale)
    if not z or any(x<=0 for x in z) or any(a>=b for a,b in zip(z,z[1:])): raise ValueError("invalid zero cache")
    return z


def generate_zeros(count:int)->list[float]:
    import mpmath as mp
    return [float(mp.im(mp.zetazero(k))) for k in range(1,count+1)]


def hole_spacing(prime:int,exponent:int)->float:
    if prime<=1 or exponent<1: raise ValueError("invalid wall")
    return 2.0*math.pi/((prime**exponent)*math.log(prime))


def hole_lattice(zeros:Sequence[float],prime:int,exponent:int,*,guard:float=1.0,lattice_shift:float=0.0)->list[float]:
    lo,hi=zeros[0]+guard,zeros[-1]-guard
    if lo>hi:return []
    s=hole_spacing(prime,exponent); first=math.ceil((lo-lattice_shift)/s); last=math.floor((hi-lattice_shift)/s)
    return [] if last<first else [s*m+lattice_shift for m in range(first,last+1)]


def nearest_index(xs:Sequence[float],x:float)->int:
    if not xs: raise ValueError("empty nearest set")
    j=bisect.bisect_left(xs,x); c=[]
    if j:c.append(j-1)
    if j<len(xs):c.append(j)
    return min(c,key=lambda k:(abs(xs[k]-x),k))


def mutual_nearest_count(zeros:Sequence[float],holes:Sequence[float])->int:
    if not zeros or not holes:return 0
    zh=[nearest_index(holes,z) for z in zeros]; hz=[nearest_index(zeros,h) for h in holes]
    return sum(1 for i,j in enumerate(zh) if hz[j]==i)


def replay_wall(zeros:Sequence[float],*,prime:int,exponent:int,guard:float=1.0,lattice_shift:float=0.0)->dict[str,object]:
    holes=hole_lattice(zeros,prime,exponent,guard=guard,lattice_shift=lattice_shift)
    return {"prime":prime,"exponent":exponent,"wall_N":prime**exponent,"guard":guard,"lattice_shift":lattice_shift,"spacing":hole_spacing(prime,exponent),"holes":len(holes),"mutual_pairs":mutual_nearest_count(zeros,holes)}


def replay_table(zeros:Sequence[float],*,guard:float=1.0,walls:Iterable[tuple[int,int]]=DEFAULT_WALLS)->list[dict[str,object]]:
    return [replay_wall(zeros,prime=p,exponent=a,guard=guard) for p,a in walls]


def replay_non_ogg_controls(zeros:Sequence[float],*,guard:float=1.0)->list[dict[str,object]]:
    return [replay_wall(zeros,prime=p,exponent=1,guard=guard) for p in NON_OGG_CONTROLS]


def source_count_match(row:dict[str,object])->bool:
    return (int(row["holes"]),int(row["mutual_pairs"]))==SOURCE_COUNTS.get((int(row["prime"]),int(row["exponent"])))


def shifted_control_counts(zeros:Sequence[float],*,prime:int,exponent:int,shifts:Sequence[float],guard:float=1.0)->list[int]:
    return [int(replay_wall(zeros,prime=prime,exponent=exponent,guard=guard,lattice_shift=s)["mutual_pairs"]) for s in shifts]


def main()->None:
    ap=argparse.ArgumentParser(); ap.add_argument("--zeros-json",type=Path); ap.add_argument("--generate-zeros",type=int,default=849); ap.add_argument("--guard",type=float,default=1.0); ap.add_argument("--output",type=Path); a=ap.parse_args()
    zeros=load_zero_cache(a.zeros_json) if a.zeros_json else generate_zeros(a.generate_zeros)
    table=replay_table(zeros,guard=a.guard); controls=replay_non_ogg_controls(zeros,guard=a.guard)
    payload={"contract":"monster_climbing_gym_replay","zero_count":len(zeros),"zero_first":zeros[0],"zero_last":zeros[-1],"guard":a.guard,"rows":[{**r,"matches_source_counts":source_count_match(r)} for r in table],"all_source_counts_match":all(source_count_match(r) for r in table),"non_ogg_controls":controls,"all_non_ogg_controls_saturate":all(int(r["mutual_pairs"])==len(zeros) for r in controls),"shift_control_boundary":"lattice-shift null supported; source shift list/seed not recovered","formal_promotion":False}
    text=json.dumps(payload,indent=2,sort_keys=True)+"\n"; a.output.write_text(text) if a.output else print(text,end="")

if __name__=="__main__":main()

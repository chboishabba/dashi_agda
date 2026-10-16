#!/usr/bin/env python3
"""Reproduce the JMD Monster Climbing Gym hole/mutual-pair table.

Diagnostic numerical producer, not a formal zeta-zero certificate. For wall
N=p**a, holes are h_m=2*pi*m/(N*log(p)) inside [t_1+1,t_849-1].
"""
from __future__ import annotations
import argparse, bisect, json, math, statistics
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_WALLS=((2,1),(3,1),(5,1),(7,1),(11,1),(2,2),(3,2),(2,3),(13,1),(71,1))
NON_OGG_CONTROLS=(37,43,53,61,67)
SOURCE_COUNTS={(2,1):(271,270),(3,1):(644,581),(5,1):(1571,820),(7,1):(2660,845),(11,1):(5151,849),(2,2):(542,513),(3,2):(1931,841),(2,3):(1083,773),(13,1):(6511,849),(71,1):(59099,849)}
SOURCE_SHIFT_SUMMARIES={(2,1):(270.3,0.9),(3,1):(594.0,8.4),(5,1):(825.4,3.2),(7,1):(845.7,0.9),(11,1):(848.5,0.6),(2,2):(519.3,4.3),(3,2):(837.4,2.5),(2,3):(771.3,3.9),(13,1):(848.7,0.5),(71,1):(849.0,0.0)}
CACHE_SCHEMA_VERSION="1.0.0"
CACHE_GENERATOR="mpmath.zetazero"


def load_zero_cache(path:Path)->list[float]:
    p=json.loads(path.read_text())
    if p.get("schema_version")!=CACHE_SCHEMA_VERSION: raise ValueError("unsupported zero-cache schema")
    if p.get("generator")!=CACHE_GENERATOR: raise ValueError("unexpected zero-cache generator label")
    scale=int(p["scale"])
    if scale<=0: raise ValueError("invalid zero-cache scale")
    if "ordinates" in p:
        z=[float(x) for x in p["ordinates"]]
    else:
        enc=[int(x) for x in p["first_plus_deltas"]]; z=[]; cur=0
        for i,v in enumerate(enc): cur=v if i==0 else cur+v; z.append(cur/scale)
    if int(p.get("count",-1))!=len(z): raise ValueError("zero-cache count metadata mismatch")
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


def mutual_nearest_count_for_shift(zeros:Sequence[float],*,prime:int,exponent:int,guard:float=1.0,lattice_shift:float=0.0)->int:
    """Same mutual count without materialising a potentially huge hole list.

    This is used by the deterministic phase-grid null.  The nearest lattice
    point to each zero is computed directly, clamped to the guarded hole-index
    interval, then checked for mutuality against the zero list.
    """
    if not zeros:return 0
    s=hole_spacing(prime,exponent); lo,hi=zeros[0]+guard,zeros[-1]-guard
    first=math.ceil((lo-lattice_shift)/s); last=math.floor((hi-lattice_shift)/s)
    if last<first:return 0
    mutual=0
    for zero_index,z in enumerate(zeros):
        q=(z-lattice_shift)/s; m0=math.floor(q); m1=m0+1
        candidates=(min(max(m0,first),last),min(max(m1,first),last))
        m=min(candidates,key=lambda k:(abs((s*k+lattice_shift)-z),k))
        h=s*m+lattice_shift
        if nearest_index(zeros,h)==zero_index: mutual+=1
    return mutual


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
    return [mutual_nearest_count_for_shift(zeros,prime=prime,exponent=exponent,guard=guard,lattice_shift=s) for s in shifts]


def phase_grid_control_summary(zeros:Sequence[float],*,prime:int,exponent:int,steps:int=720,guard:float=1.0)->dict[str,object]:
    """Deterministic no-RNG approximation to a uniform one-period shift null.

    The source panel reports rounded mean/SD values but not its sampled shifts
    or RNG seed.  Midpoint sampling over one exact lattice period therefore
    gives a replayable null-family diagnostic without pretending to recover the
    unrecoverable source sample.
    """
    if steps<=0: raise ValueError("steps must be positive")
    spacing=hole_spacing(prime,exponent)
    shifts=[spacing*(i+0.5)/steps for i in range(steps)]
    counts=shifted_control_counts(zeros,prime=prime,exponent=exponent,shifts=shifts,guard=guard)
    return {"prime":prime,"exponent":exponent,"steps":steps,"spacing":spacing,"mean":statistics.fmean(counts),"population_sd":statistics.pstdev(counts),"minimum":min(counts),"maximum":max(counts)}


def source_shift_summary_compatible(summary:dict[str,object],*,mean_tolerance:float=1.1,sd_tolerance:float=0.8)->bool:
    key=(int(summary["prime"]),int(summary["exponent"])); target=SOURCE_SHIFT_SUMMARIES.get(key)
    if target is None:return False
    return abs(float(summary["mean"])-target[0])<=mean_tolerance and abs(float(summary["population_sd"])-target[1])<=sd_tolerance


def main()->None:
    ap=argparse.ArgumentParser(); ap.add_argument("--zeros-json",type=Path); ap.add_argument("--generate-zeros",type=int,default=849); ap.add_argument("--guard",type=float,default=1.0); ap.add_argument("--phase-grid-steps",type=int,default=720); ap.add_argument("--output",type=Path); a=ap.parse_args()
    zeros=load_zero_cache(a.zeros_json) if a.zeros_json else generate_zeros(a.generate_zeros)
    table=replay_table(zeros,guard=a.guard); controls=replay_non_ogg_controls(zeros,guard=a.guard)
    shift_null=[phase_grid_control_summary(zeros,prime=p,exponent=e,steps=a.phase_grid_steps,guard=a.guard) for p,e in DEFAULT_WALLS]
    payload={"contract":"monster_climbing_gym_replay","zero_count":len(zeros),"zero_first":zeros[0],"zero_last":zeros[-1],"guard":a.guard,"rows":[{**r,"matches_source_counts":source_count_match(r)} for r in table],"all_source_counts_match":all(source_count_match(r) for r in table),"non_ogg_controls":controls,"all_non_ogg_controls_saturate":all(int(r["mutual_pairs"])==len(zeros) for r in controls),"deterministic_uniform_phase_shift_null":[{**r,"compatible_with_source_rounded_summary":source_shift_summary_compatible(r)} for r in shift_null],"all_shift_summaries_compatible":all(source_shift_summary_compatible(r) for r in shift_null),"shift_control_boundary":"uniform one-period phase-grid null reproduced; source finite random shift list/seed is not identifiable from rounded mean/SD summaries","formal_promotion":False}
    text=json.dumps(payload,indent=2,sort_keys=True)+"\n"; a.output.write_text(text) if a.output else print(text,end="")

if __name__=="__main__":main()

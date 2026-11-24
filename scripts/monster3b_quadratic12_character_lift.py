#!/usr/bin/env python3
"""M3B-L10A/B: exact Q(zeta3) degree12 character reconstruction from the
TWO marked source Monster MMV(31) 12D modular Hom vacuum block traces.

Mathematical theorem:
  chi=a+b*zeta in Z[zeta], |chi|<=12 (finite-group character).
  Norm chi = a*a-a*b+b*b <=144, hence |a|,|b|<=13.
  With zeta->5 or25 in F31, the two normalized traces determine the
  UNIQUE exact integer a,b, not merely a mod-p estimate.

The actual vacuum sandwich M(g)=k0(g)*L(g) carries UNKNOWN Weil scalar.
For order3 source inner words D and CDC^-1, find ALL scalar normalizations
k0 for which M(g)/k0 has cube I, paired field conjugate trace-squares,
and 12 eigenvalue multiplicities. NEVER select one merely because it
matches a bounded character: source group relators/Weil cocycle must
resolve remaining phase choices.

This method requires NO Steel source, NO Magma, and NO conversion of
GF3 quotient matrices into complex ordinary representations. It does
not claim char0 Hom identification from a single characteristic.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np

P=31
Z=5
ZI=25
BOUND=144

def mul(A,B):
    return (np.asarray(A,dtype=np.int64)@
            np.asarray(B,dtype=np.int64))%P

def trace(A):return int(np.trace(np.asarray(A,dtype=np.int64)))%P

def cube_scalar(A):
    A=np.asarray(A,dtype=np.int64)%P
    if A.shape!=(12,12):raise ValueError("source block must be 12x12")
    c=mul(mul(A,A),A)
    v=int(c[0,0])
    if not np.array_equal(c,(v*np.eye(12,dtype=np.int64))%P):
        return None
    return v

def centered(x,p=P):
    y=int(x)%p
    return y if y<=p//2 else y-p

def lift_character(t_plus,t_minus):
    b=((t_plus-t_minus)*pow((Z-ZI)%P,-1,P))%P
    a=(t_plus-Z*b)%P
    a,b=centered(a),centered(b)
    norm=a*a-a*b+b*b
    if norm>BOUND:return None
    if ((a+Z*b)%P!=t_plus%P or (a+ZI*b)%P!=t_minus%P):
        raise AssertionError("quadratic character F31 field descent mismatch")
    return {"a":a,"b":b,"norm":norm,
       "chi":"%s + (%s)*zeta3"%(a,b)}

def order_three_multiplicities(a,b):
    # For A^3=I and 31 not 3: eigenvalue counts (1,zeta,zeta²).
    if (12-a-b)%3:return None
    n2=(12-a-b)//3
    n0=n2+a
    n1=n2+b
    if min(n0,n1,n2)<0 or n0+n1+n2!=12:return None
    return {"n_1":n0,"n_zeta":n1,"n_zeta_squared":n2}

def all_lifts(Ap,Am):
    kp=cube_scalar(Ap)
    km=cube_scalar(Am)
    if kp is None or km is None:return {
        "status":"SOURCE_SANDWICH_NOT_CUBIC_SCALAR",
        "cubic_scalar_plus":kp,"cubic_scalar_minus":km,"candidates":[]}
    if kp==0 or km==0:return {
        "status":"SOURCE_SANDWICH_VACUUM_SCALAR_ZERO",
        "cubic_scalar_plus":kp,"cubic_scalar_minus":km,"candidates":[]}
    roots_plus=[x for x in range(1,P) if pow(x,3,P)==kp]
    roots_minus=[x for x in range(1,P) if pow(x,3,P)==km]
    tp=trace(Ap);tm=trace(Am)
    t2p=trace(mul(Ap,Ap));t2m=trace(mul(Am,Am))
    candidates=[]
    for u in roots_plus:
        for v in roots_minus:
            invu=pow(u,-1,P);invv=pow(v,-1,P)
            cplus=tp*invu%P
            cminus=tm*invv%P
            # For order3, g²=g^-1 and finite-group dual character
            # equals complex/Galois conjugate, in *coherently paired*
            # opposite-phase source representations.
            if (t2p*invu*invu)%P!=cminus:continue
            if (t2m*invv*invv)%P!=cplus:continue
            char=lift_character(cplus,cminus)
            if char is None:continue
            mult=order_three_multiplicities(char["a"],char["b"])
            if mult is None:continue
            candidates.append({"Weil_scalar_plus_mod31":u,
                "Weil_scalar_minus_mod31":v,
                "normalized_trace_zeta5":cplus,
                "normalized_trace_zeta25":cminus,
                "candidate_exact_character":char,
                "order3_eigen_multiplicities":mult,
                "source_group_word_gauge_fixed":False})
    return {
       "status":"ORDER3_CHARACTER_CANDIDATES_NOT_GLOBAL_GAUGE",
       "cubic_scalar_plus":kp,"cubic_scalar_minus":km,
       "unnormalized_trace_plus":tp,"unnormalized_trace_minus":tm,
       "Weil_scalar_cube_roots_plus":roots_plus,
       "Weil_scalar_cube_roots_minus":roots_minus,
       "candidates":candidates}

def load_phase(directory,root):
    folder=Path(directory)
    state=json.loads((folder/"mmv31_hom_status.json").read_text())
    if state.get("p")!=31 or state.get("zeta_mod_p")!=root:
        raise ValueError("source 3B centre phase mismatches +/- marked F31 roots")
    if state.get("number_independent_B_fixed_vectors")!=90:
        raise ValueError("original Monster modular vacuum was not full rank90")
    if state.get("selected_12_plus_78_dimensions_found") is not True:
        raise ValueError("actual C2 12/78 source eigenspaces not recovered")
    return state

def run(plus,minus):
    sp=load_phase(plus,Z)
    sm=load_phase(minus,ZI)
    if sp.get("source_manifest")!=sm.get("source_manifest"):
        raise ValueError("different Monster Heisenberg original source manifests")
    out={"schema":"monster3b-actual-MMV31-to-quadratic12-candidate-character-v1",
        "source":"original genuine MMV31 B-vacuum, two marked z3B eigenphases",
        "actual_Monster_mod31_both_phases":True,
        "ordinary_char0_Hom12_proven_from_mod31":False,
        "source_6Suz_generator_word_attached":False,
        "Weil_vacuum_scalar_global_cocycle_solved":False,
        "exact_single_prime_bound":"a*a-a*b+b*b <= 144; |a|,|b|<=13",
        "words":{}}
    files=[
        ("D","actual_D_12_78_vacuum_sandwich_mod31.npz","D12"),
        ("CDCinv","actual_CDCinv_12_78_vacuum_sandwich_mod31.npz","E12")
    ]
    for word,name,key in files:
        pfile=Path(plus)/name;mfile=Path(minus)/name
        if pfile.is_file() and mfile.is_file():
            with np.load(pfile) as p,np.load(mfile) as m:
                out["words"][word]=all_lifts(p[key],m[key])
        else:
            out["words"][word]={"status":"MISSING_BOTH_MARKED_SOURCE_12_BLOCKS",
                "plus_found":pfile.is_file(),"minus_found":mfile.is_file()}
    return out

def exhaustive_proof():
    # All 517 possible degree12 integer-ring values are recovered
    # uniquely from their two marked mod31 traces.
    pairs=[(a,b) for a in range(-13,14) for b in range(-13,14)
           if a*a-a*b+b*b<=BOUND]
    if len(pairs)!=517:raise AssertionError("degree12 norm enumeration incorrect")
    for a,b in pairs:
        actual=lift_character((a+Z*b)%P,(a+ZI*b)%P)
        if actual is None or (actual["a"],actual["b"])!=(a,b):
            raise AssertionError("bounded two-phase source collision")
    # A synthetic order3 12D matrix with multiplicities 5,4,3
    # has character 2+zeta; source projective vacuum scalars 7,9.
    # The local arithmetic must include the genuine choice, but must
    # NOT collapse its remaining cubic central-cover gauge to a guess.
    A=np.diag([1]*5+[Z]*4+[ZI]*3).astype(np.int64)
    B=np.diag([1]*5+[ZI]*4+[Z]*3).astype(np.int64)
    candidates=all_lifts((7*A)%P,(9*B)%P)
    if candidates["status"]!="ORDER3_CHARACTER_CANDIDATES_NOT_GLOBAL_GAUGE":
        raise AssertionError("order3 source normalization stage failed")
    choices=candidates["candidates"]
    if len(choices)!=3 or not any(
        v["candidate_exact_character"]["a"]==2 and
        v["candidate_exact_character"]["b"]==1 and
        v["Weil_scalar_plus_mod31"]==7 and
        v["Weil_scalar_minus_mod31"]==9 for v in choices):
        raise AssertionError("original-phase projective cubic scalar search incorrect")
    return {"exact_bounded_Qzeta3_values":len(pairs),
       "collisions":0,"phase_roots":[Z,ZI],
       "toy_order3_projective_scalar_candidates":len(choices),
       "actual_central_cover_gauge_selected":False,
       "derivation":"|chi|<=12, Norm chi=a²-ab+b²<=144",
       "actual_MM_source_executed":False}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--plus",type=Path)
    ap.add_argument("--minus",type=Path)
    ap.add_argument("--out",type=Path,default=Path(
        ".dashi/monster3b-mmgroup/quadratic12_phase_character_candidates.json"))
    ap.add_argument("--selftest",action="store_true")
    a=ap.parse_args()
    if a.selftest:result=exhaustive_proof()
    else:
        if a.plus is None or a.minus is None:ap.error("--plus and --minus needed")
        result=run(a.plus,a.minus)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=="__main__":main()

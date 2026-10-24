"""Same-physical-field exact signed R63/R236 classifier witness.

The compiler tests physical Leray/curl production; it does not assume the
mixed-helicity R685 source is identical, nor count the separate Com cell.
"""
import importlib.util
from pathlib import Path
import sympy as S
P=Path(__file__).resolve().parents[1]/"scripts/ns_physical_vorticity_partition.py"
spec=importlib.util.spec_from_file_location("ns_physical_partition",P)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def witness():
    p=(1,0,0); q=(0,1,2); k=(1,1,2)
    out={p:S.Matrix([0,1,1]),q:S.Matrix([1,0,0]),
         k:S.I*S.Matrix([1,-1,0])}
    out.update({mod.neg(m):S.conjugate(v) for m,v in list(out.items())})
    return out

def test_true_physical_production_equals_stretching():
    r=mod.budget(witness())
    assert r["production"]==r["stretch"]==8
    assert r["transport"]==r["energy"]==0
    assert r["bony"]=={"CC":8}
    assert r["r236"]=={"critical":8}

def test_authoritative_strict_three_shell_collar():
    p=(1,0,0);q=(0,0,8)
    assert mod.shell(p)==0 and mod.shell(q)==3
    assert mod.bony(p,q)==mod.bony(q,p)=="CC"
    assert mod.r236(p,q)=="critical"

def test_deep_LH_HL_HH_selected_complement_exact():
    p=(1,0,0);q=(0,1,64)
    a=mod.budget(mod.field(p,q))
    assert a["production"]==a["stretch"]==-16384
    assert a["bony"]=={"LH":4,"HL":-16392,"HH":4}
    assert a["r236"]=={"deep-LH":4,"deep-HL":-16392,"deep-HH":4}
    # Dropping either compensating signed class changes physical production.
    assert a["r236"]["deep-HL"]!=a["production"]
    flipped={m:S.conjugate(v) for m,v in mod.field(p,q).items()}
    assert mod.budget(flipped)["production"]==16384

def test_general_superposed_triads_and_zero_padding():
    p=(1,0,0)
    combined=mod.field(p,(0,1,64))
    for k,v in mod.field(p,(0,3,32)).items():
        combined[k]=combined.get(k,S.zeros(3,1))+v
    a=mod.budget(combined)
    assert a["production"]==a["stretch"]
    assert a["production"]==sum(a["bony"].values())
    assert a["production"]==sum(a["r236"].values())
    assert a["energy"]==a["transport"]==0
    padded={**combined,(100,0,0):S.zeros(3,1),
                        (-100,0,0):S.zeros(3,1)}
    assert mod.budget(padded)==a

def test_classwise_curl_and_transport_need_signed_compensation():
    r=mod.budget(mod.field((1,0,0),(0,1,64)))
    # (enstrophy production, vorticity transport, stretching, residual)
    assert r["class_correction"]=={
       "LH":(4,0,0,4),
       "HL":(-16392,-4,-16384,-4),
       "HH":(4,4,0,0)}
    assert sum(v[3] for v in r["class_correction"].values())==0
    assert sum(v[1] for v in r["class_correction"].values())==0
    assert sum(v[2] for v in r["class_correction"].values())==-16384
    # These are physical Bony classifier contributions, not R685's
    # separate mixed-helicity/commutator source.

#!/usr/bin/env python3
"""Local source-implementation smoke checks, NO Monster/GAP/Magma certification.

Run as:
  python3 scripts/test_monster3b_p5_endpoint_local.py

Exercises exactly the algorithmic pieces whose source inputs have not
yet been transferred to this environment. Real source results still require
the workstation with Magma, GAP/CTblLib and mmgroup.
"""
from __future__ import annotations
import ast
import importlib.util
import json
from pathlib import Path
import tempfile

HERE=Path(__file__).resolve().parent
SCRIPTS=[
 "monster3b_mmgroup_canonical_cover_words.py",
 "monster3b_steel_magma_export.py",
 "monster3b_gap_ordinary12_class_fingerprint.py",
 "monster3b_ordinary12_hom_outer_weld.py",
 "monster3b_steel_ordinary12_to90.py",
 "monster3b_actual_mmv31_hom_projector.py",
 "monster3b_literal_mm_4d_character_class.py",
 "monster3b_quadratic12_character_lift.py",
 "monster3b_mm31_outer_phase_pair.py",
 "run_monster3b_p5_endpoint.py",
]
def load(filename):
    spec=importlib.util.spec_from_file_location(
       "monster3b_"+filename.replace(".py",""),HERE/filename)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod
def main():
    for name in SCRIPTS:
        ast.parse((HERE/name).read_text(),filename=name)
    group=load(SCRIPTS[0])
    assert group.selftest()["pure_F3_linear_affine_section"]=="PASS"
    assert len(group.signed_relator_rephase())==9
    # Regress the report's nontrivial Hom orientation bug. For an actual
    # noncommuting conjugate pair (B,D)=(T^-1 C T,T^-1 D T),
    # the source intertwiner must solve C*T = T*B, not T*C = B*T.
    atlas=load("monster3b_atlas_mmgroup_cross_source_intertwiner_gate.py")
    C,D=atlas.atlas(HERE.parent)
    shift=[[int(j==(i+1)%12) for j in range(12)] for i in range(12)]
    shift_inv=atlas.inverse(shift)
    B=atlas.mul(atlas.mul(shift_inv,C),shift)
    Dprime=atlas.mul(atlas.mul(shift_inv,D),shift)
    result=atlas.check_pair((C,D),(B,Dprime))
    assert result["status"]=="ALGEBRAIC_CANDIDATE_ONLY"
    assert result["invertible_basis_witness"]
    T=result["T_rows_F3"]
    assert atlas.mul(C,T)==atlas.mul(T,B)
    assert atlas.mul(D,T)==atlas.mul(T,Dprime)

    homo=load(SCRIPTS[3])
    assert homo.selftest()["toy_GL2_noncommuting_unique_Hom"]=="PASS"
    builder=load(SCRIPTS[4])
    literal=load("monster3b_literal_mm_4d_character_class.py")
    gap_src=literal.gap_source(123,456,Path("/tmp/monster3b-class4D.json"))
    assert "chi[j]=123" in gap_src and "chi[pow2[j]]=456" in gap_src
    assert '\\\"schema\\\"' in gap_src and "classes[10]" in gap_src
    lift=load("monster3b_quadratic12_character_lift.py")
    bounded=lift.exhaustive_proof()
    assert bounded["exact_bounded_Qzeta3_values"]==517
    assert bounded["collisions"]==0
    assert bounded["toy_order3_projective_scalar_candidates"]==3
    mm31=load("monster3b_actual_mmv31_hom_projector.py")
    import numpy as np
    assert mm31.rank31(np.eye(4,dtype=np.int16))==4
    assert mm31.rank31(np.zeros((4,4),dtype=np.int16))==0
    null=mm31.nullspace31(np.array([[1,0,0],[0,1,0]],dtype=np.int16))
    assert null.shape==(3,1) and null[2,0]==1
    B=np.array([[1,0],[0,1],[1,1]],dtype=np.int16)
    D=np.array([[5,7],[1,3]],dtype=np.int16)
    assert np.array_equal(mm31.coordinates_in_columns(B,
        mm31.matmul31(B,D)),D%31)

    assert np.array_equal(mm31.matmul31(np.eye(2,dtype=np.int16),
                   np.array([[5,27],[12,2]],dtype=np.int16)),
                   np.array([[5,27],[12,2]],dtype=np.int16))
    magma=load(SCRIPTS[1])
    # The actual primitive ζ3 scalar central action is preserved on
    # dual Sym² of a faithful12; none of these are Steel group generators.
    zeta=["0","1"]
    zero=["0","0"]
    source_mat=[
      [zeta if i==j else zero for j in range(12)]
      for i in range(12)]
    packet={
      "schema":builder.SCHEMA,
      "source":{"url":builder.URL,"sha256":"0"*64},
      "field_polynomial":[1,1,1],
      "matrix_convention":"left_action_column_vectors",
      "selected_6Suz_12_irr_position":None,
      "generators":{"TOY_SCALAR_C3":source_mat}}
    with tempfile.TemporaryDirectory() as t:
        loc=Path(t)
        output=builder.build(packet,loc/"derived.json")
        actual=output["generators"]["TOY_SCALAR_C3"]
        assert actual["trace_12"]==["0","12"]
        assert actual["trace_78"]==["0","78"]
        assert actual["trace_90"]==["0","90"]
        code=magma.build_code(loc/"Steel.M",loc/"export.json","M","0"*64)
        assert "ActionGenerator" not in code or "Representation(" in code
        assert "Monster3BWordPairs" in code
        assert "PrintFile(" in code and "Group(" in code
        fingerprint=load(SCRIPTS[2])
        stage=fingerprint.generate({
           "schema":fingerprint.SCHEMA,
           "fingerprints":[{"word":"G.1","group_order":3,
                "trace":["0","12"],"trace_square":["-12","-12"]}]},
           loc/"gapsource.json")
        assert "irr[153]" in stage and "irr[154]" in stage
        assert "square[k]" in stage and "PrintTo(" in stage
    print(json.dumps({
      "status":"PASS_LOCAL_PURE_ALGORITHMS",
      "python_syntax_modules":SCRIPTS,
      "GF3_canonical_E_correction":"PASS",
      "GF3_nontrivial_conjugate_intertwiner_orientation":"PASS",
      "signed_outer_C3_relator_rephasing_9_cases":"PASS",
      "Qzeta3_noncommuting_Hom_GL2":"PASS",
      "derived_90_same_C3_scalar_trace":"PASS",
      "Magma_original_source_export_staging":"PASS",
      "GAP_210_class_fingerprint_staging":"PASS",
      "actual_MMV31_rank_algorithms":"PASS_LOCAL_F31_ONLY",
      "literal_Monster_4D_GAP_character_script_staging":"PASS",
      "bounded_Qzeta12_character_lift_517_of_517":"PASS",
      "Weil_order3_scalar_ambiguity_correctly_retained":"PASS",

      "actual_Steel_Magma_GModule_executed":False,
      "actual_GAP_CTBLib_executed":False,
      "actual_Monster_mmgroup_word_executed":False,
      "actual_char0_Monster_Hom12_supplied":False
    },indent=2))
if __name__=="__main__":main()

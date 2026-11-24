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
    homo=load(SCRIPTS[3])
    assert homo.selftest()["toy_GL2_noncommuting_unique_Hom"]=="PASS"
    builder=load(SCRIPTS[4])
    mm31=load("monster3b_actual_mmv31_hom_projector.py")
    import numpy as np
    assert mm31.rank31(np.eye(4,dtype=np.int16))==4
    assert mm31.rank31(np.zeros((4,4),dtype=np.int16))==0
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
      "Qzeta3_noncommuting_Hom_GL2":"PASS",
      "derived_90_same_C3_scalar_trace":"PASS",
      "Magma_original_source_export_staging":"PASS",
      "GAP_210_class_fingerprint_staging":"PASS",
      "actual_MMV31_rank_algorithms":"PASS_LOCAL_F31_ONLY",
      "actual_Steel_Magma_GModule_executed":False,
      "actual_GAP_CTBLib_executed":False,
      "actual_Monster_mmgroup_word_executed":False,
      "actual_char0_Monster_Hom12_supplied":False
    },indent=2))
if __name__=="__main__":main()

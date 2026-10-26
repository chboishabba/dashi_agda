#!/usr/bin/env python3
"""Adversarial source-join interface regression.

These are intentionally SYNTHETIC rows with a TEST DOUBLE for the
heavy full-character audit; their passing does not imply any authentic
6.Suz/Monster character is known. The production CLI invokes both
original existing checkers and recomputes the full class comparison.
"""
import copy
import json
import sys
import types
from fractions import Fraction

import monster_3b_suzuki_selected_character_join as join

class FakeCyc:
    def __init__(self,a,b=0):self.a,self.b=Fraction(a),Fraction(b)
    @classmethod
    def scalar(cls,x):return cls(x)
    @classmethod
    def from_coeffs(cls,n,coeff):
        assert n==3
        return cls(Fraction(coeff[0])-Fraction(coeff[2]),
                   Fraction(coeff[1])-Fraction(coeff[2]))
    @classmethod
    def wire(cls,rec):return cls.from_coeffs(3,rec["coefficients"])
    def __eq__(self,other):
        if not isinstance(other,FakeCyc):other=FakeCyc(other)
        return self.a==other.a and self.b==other.b
    def __mul__(self,other):
        if not isinstance(other,FakeCyc):other=FakeCyc(other)
        return FakeCyc(self.a*other.a-self.b*other.b,
                       self.a*other.b+self.b*other.a-self.b*other.b)
    __rmul__=__mul__
    def __neg__(self):return FakeCyc(-self.a,-self.b)

# Inject only the algebra needed for the synthetic join interface check.
sys.modules["monster_3b_suzuki_all_conductors_character_audit"]=types.SimpleNamespace(Cyc=FakeCyc)

def wire(n,k):
    coord={0:[n,0,0],1:[0,n,0],2:[0,0,n]}
    return {"conductor":3,"coefficients":coord[k]}

def case(positive):
    sign=1 if positive else -1
    source={"table_id":"6.Suz","central_c2_zero_based":1,
       "central_c3_zero_based":2,
       "group_order":6,"class_orders":[1,2,3,6,3,2],
       "degree12":[{"label":label,"source_irreducible_position_1_based":i,
                    "values":[wire(12,0),wire(-12,0),wire(12,k)]}
                   for i,(label,k) in enumerate((("12a",1),("12b",2)),1)],
       "degree78":[{"label":label,"source_irreducible_position_1_based":i+2,
                    "values":[wire(78,0),wire(78*sign,0),wire(78,k)]}
                   for i,(label,k) in enumerate((("78a",1),("78b",2)),1)]}
    selected={"six_suz_table":"6.Suz",
        "six_suz_group_order":6,"six_suz_class_count":6,
        "six_suz_degree12_positions":[1,2],
        "six_suz_degree78_positions":[3,4],
        "suzuki_central_involution_class_position":2,
        "suzuki_central_order_three_class_position":3,
        "common_729_necessary_equal_C3_phase_pair_count":2,
        "source_selected_S90_central_C2_trace":-12+78*sign,
        "source_selected_degree_78_faithful_to_6Suz":not positive,
        "selected_78_direct_sym2_full_character_pair_count":2 if positive else 0,
        "selected_78_dual_sym2_full_character_pair_count":2 if positive else 0,
        "selected_78_is_nebe_sym2_family_full_character_equal":positive,
        "degree_12_atlas_labels":["12a","12b"],
        "degree_78_atlas_labels":["78a","78b"]}
    return source,selected

def fake_audit(source):
    matched=FakeCyc.wire(source["degree78"][0]["values"][1])==78
    return {"orthogonality_executed":True,
        "matches":[{"12":a,"78":b,"mode":mode}
          for a,b in (("12a","78a"),("12b","78b"))
          for mode in ("Sym2","dualSym2")] if matched else []}

def fake_validate(x):
    return dict(labels12=x["degree_12_atlas_labels"],labels78=x["degree_78_atlas_labels"],
        common729_pairs=x["common_729_necessary_equal_C3_phase_pair_count"],
        source_trace=x["source_selected_S90_central_C2_trace"],
        full_direct=x["selected_78_direct_sym2_full_character_pair_count"],
        full_dual=x["selected_78_dual_sym2_full_character_pair_count"],
        full_nebe=x["selected_78_is_nebe_sym2_family_full_character_equal"],
        selected_faithful=x["source_selected_degree_78_faithful_to_6Suz"],
        source_order=x["six_suz_group_order"],
        source_classes=x["six_suz_class_count"],
        positions12=x["six_suz_degree12_positions"],
        positions78=x["six_suz_degree78_positions"])

def run():
    for positive in (True,False):
        a,b=case(positive)
        res=join.check(a,b,audit_fn=fake_audit,selected_validate_fn=fake_validate)
        assert res["central_C2_trace"]==(66 if positive else -90)
        assert res["selected_Nebe_family_full_class_equal"]==positive
    a,b=case(True)
    negatives=[]
    def fails(name,change):
        aa,bb=copy.deepcopy(a),copy.deepcopy(b)
        change(aa,bb)
        try:join.check(aa,bb,audit_fn=fake_audit,selected_validate_fn=fake_validate)
        except (ValueError,KeyError,TypeError):negatives.append(name)
        else:raise AssertionError("accepted invalid evidence: "+name)
    fails("wrong_table",lambda a,b:a.update(table_id="Other"))
    fails("wrong_c2_class",lambda a,b:b.update(suzuki_central_involution_class_position=3))
    fails("wrong_c3_class",lambda a,b:b.update(suzuki_central_order_three_class_position=2))
    fails("absent_selected_78",lambda a,b:b.update(degree_78_atlas_labels=["78a","78c"]))
    fails("absent_selected_12",lambda a,b:b.update(degree_12_atlas_labels=["12a","12c"]))
    fails("wrong_c3_pair_count",lambda a,b:b.update(common_729_necessary_equal_C3_phase_pair_count=0))
    fails("wrong_c2_trace",lambda a,b:b.update(source_selected_S90_central_C2_trace=-90))
    fails("false_faithful_claim",lambda a,b:b.update(source_selected_degree_78_faithful_to_6Suz=True))
    fails("false_sym2_count",lambda a,b:b.update(selected_78_direct_sym2_full_character_pair_count=0))
    fails("false_nebe_claim",lambda a,b:b.update(selected_78_is_nebe_sym2_family_full_character_equal=False))
    fails("non_scalar_c2",lambda a,b:a["degree78"][1]["values"].__setitem__(1,wire(3,0)))
    fails("different_c2_signs",lambda a,b:a["degree78"][1]["values"].__setitem__(1,wire(-78,0)))
    fails("stale_12_Irr_position",lambda a,b:b.update(six_suz_degree12_positions=[2,1]))
    fails("stale_78_Irr_position",lambda a,b:b.update(six_suz_degree78_positions=[4,3]))
    fails("source_group_order_drift",lambda a,b:b.update(six_suz_group_order=7))
    fails("source_class_count_drift",lambda a,b:b.update(six_suz_class_count=7))
    fails("duplicate_exported_Irr_position",lambda a,b:a["degree78"][0].update(source_irreducible_position_1_based=2))
    fails("missing_exported_Irr_position",lambda a,b:a["degree78"][1].pop("source_irreducible_position_1_based"))
    assert len(negatives)==18
    return {"status":"PASS_SYNTHETIC_JOIN_INTERFACE",
       "coherent_synthetic_branches":2,"rejected_false_joins":negatives,
       "original_6Suz_data_used":False,"full_class_auditor_executed":False,
       "GAP_or_Agda_executed":False,"Monster_family_identified":False}

if __name__=="__main__":print(json.dumps(run(),indent=2))

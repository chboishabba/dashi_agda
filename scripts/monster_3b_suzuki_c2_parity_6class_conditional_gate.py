#!/usr/bin/env python3
"""Exact conditional Monster 3B central-2B/order-6/729-parity gate.

Independent source: Norton--Wilson, Anatomy of the Monster II (2002),
Proc London Math Soc 84 581-598, 3B-centralizer central involution in 2B.
Other source: Monster ATLAS classes, Conway--Norton McKay--Thompson values.
Premises MUST be externally certified in the same actual quotient:
  - central 2.Suz involution acts by -I on the six-trit Schrödinger fibre;
  - that specific lift has Monster class 2B;
  - its product with chosen 3B generator lies in 6B or 6E.
No class word or selected source 78 family is established by this local test.
"""
import json,itertools
import argparse

# ORIGINAL SOURCE: ATLAS Monster power-up tables,
# https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/
# Contains only the relevant order-4, order-12, and order-6 class
# intersections (not a fabricated full class fusion).
# The 2B central involution is from Norton--Wilson (2002).
ATLAS_SOURCE_FOUR_TO_TWELVE={
  "4A":{"12B":"6E"},
  "4C":{"12H":"6E","12I":"6E"},
  "4D":{"12F":"6B"},
}
ATLAS_THREE_B_POWERUPS_12={"12B","12F","12G","12H","12I"}
ATLAS_TWO_B_POWERUPS_4={"4A","4C","4D"}
ATLAS_FOUR_B_SQUARES_TO="2A"
ATLAS_SIX_POWERUPS_12={
  "6B":{"12F"},
  "6E":{"12B","12H","12I"},
}
def atlas_class_sieve():
    # Section of primary Atlas class power-up source, NOT independently
    # re-derived from original group generators or CTblLib this run.
    classes=[]
    for cls,options in ATLAS_SOURCE_FOUR_TO_TWELVE.items():
        assert cls in ATLAS_TWO_B_POWERUPS_4
        for twelve,six in options.items():
            assert twelve in ATLAS_THREE_B_POWERUPS_12
            assert twelve in ATLAS_SIX_POWERUPS_12[six]
            classes.append({"source_rotation_class":cls,
                            "source_z_times_rotation_class":twelve,
                            "source_z_times_halfturn_class":six})
    assert len(classes)==4
    assert "4B" not in ATLAS_TWO_B_POWERUPS_4
    assert ATLAS_FOUR_B_SQUARES_TO=="2A"
    return classes
def select_rotation_class(rotation_class=None):
    options=atlas_class_sieve()
    if rotation_class is not None:
        if rotation_class not in ATLAS_SOURCE_FOUR_TO_TWELVE:
            raise ValueError(
              "source rotation must be 4A/4C/4D after NW 2B fusion; "
              "the actual class is not yet authenticated")
        options=[x for x in options if x["source_rotation_class"]==rotation_class]
    return options


def check(rotation_class=None):
    points=itertools.product(range(3),repeat=6)
    fix=sum(tuple(u)==tuple((-x)%3 for x in u) for u in points)
    assert fix==1 # inversion u -> -u on F3^6 fixes only origin
    # Ordinary Monster first nontrivial character at 2B/6B/6E.
    classes={"6B":77,"6E":5}
    traces={key:(275-ordinary)//3 for key,ordinary in classes.items()}
    assert traces=={"6B":66,"6E":90}
    solutions=[]
    for source_family,c2 in (("faithful78",-90),("nonfaithful78_C2plus",66)):
        for parity_sign in (-1,1):
            pred=c2*parity_sign
            possible=[k for k,v in traces.items() if v==pred]
            solutions.append(dict(family=source_family,source_C2_trace=c2,
                Schroedinger_inversion_lift_trace=parity_sign,
                predicted_selected_phase_trace=pred,
                compatible_monster_order6_classes=possible))
    allowed=[x for x in solutions if x['compatible_monster_order6_classes']]
    assert {(x['family'],x['Schroedinger_inversion_lift_trace'],
             tuple(x['compatible_monster_order6_classes']))
            for x in allowed}=={
      ('faithful78',-1,('6E',)),
      ('nonfaithful78_C2plus',1,('6B',))}
    all_sieved=[]
    for source in select_rotation_class(rotation_class):
        compatible=[
            a for a in allowed if source['source_z_times_halfturn_class']
            in a['compatible_monster_order6_classes']
        ]
        assert len(compatible)==1
        all_sieved.append(dict(**source,
            source_family=compatible[0]['family'],
            source_C2_trace=compatible[0]['source_C2_trace'],
            Schroedinger_inversion_lift_trace=compatible[0]['Schroedinger_inversion_lift_trace'],
            predicted_selected_phase_trace=compatible[0]['predicted_selected_phase_trace']))
    assert {(p["source_rotation_class"],p["source_z_times_rotation_class"],
             p["source_z_times_halfturn_class"],p["predicted_selected_phase_trace"])
            for p in atlas_class_sieve()}=={
             ("4A","12B","6E",90),("4C","12H","6E",90),
             ("4C","12I","6E",90),("4D","12F","6B",66)}
    return {'status':'PASS_CONDITIONAL_MATHEMATICAL_GATE',
      'source_rotation_class_filter':rotation_class,
      'atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6':all_sieved,
      'fourB_2A_old_steelman_applies_to_this_actual_2B_source_D4':False,
      'original_source_attributions':[
       'ATLAS Monster 3B,2B,4A/4C/4D,6B/6E and 12B/F/H/I power-ups',
       'Norton-Wilson 2002 central 2.Suz involution -> Monster 2B',
       'Barraclough-Wilson 2007 normalizer and standard generators',
       'Conway-Norton and Ford-McKay-Norton original McKay-Thompson series'],
      'conditional_c3_inverting_mirror_conjugacy_used':True,
      'source_rotation_4A_4C_4D_literal_class_selected':False,
      'real_selected_6Suz_degree78_character_verified':False,
      'fibre_dimension':729,'inversion_fixed_points':fix,
      'source_class_2B_character':275,
      'source_order6_characters':classes,
      'possible_source_zeta_traces':traces,
      'compatible_cases':allowed,
      'excluded_sign_family_combinations':[v for v in solutions
        if not v['compatible_monster_order6_classes']],
      'actual_source_c2_lift_is_inversion_certified_here':False,
      'actual_monster_z_product_class_certified_here':False,
      'GAP_executed':False,'claim_of_selected_78_identity':False}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--rotation-class",choices=("4A","4C","4D"))
    p.add_argument("--out",type=__import__('pathlib').Path)
    a=p.parse_args()
    result=json.dumps(check(a.rotation_class),indent=2)+"\\n"
    if a.out:a.out.write_text(result)
    print(result,end="")

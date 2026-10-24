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

def check():
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
    return {'status':'PASS_CONDITIONAL_MATHEMATICAL_GATE',
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
if __name__=='__main__':print(json.dumps(check(),indent=2))

#!/usr/bin/env python3
"""Conditional full-D4 source-character veto for the JFine oriented C4/H4 model.

ORIGINAL AUTHORITY: Barraclough--Wilson 2007; ATLAS Monster class powers;
Breuer/CTblLib. PR #1250 owns r=4B, r²=2A source-class restriction.
PR #1148 owns the MODIFIED eight-trit D4 model V=A1+A2+2B1+2B2+E,
its centre multiplier and source fixed-space dimensions (8,6,2,4,4).

This checks a specific 10-marker × centre × F3^8 product-action
representation as a D4-stable bulk summand with 53D residual; not
arbitrary Monster normalizer actions, non-factorized fibres, or GSp models.
"""
import json

CLASSES=('one','half','quarter','axis','diagonal')
SIZES=(1,1,2,2,2)
IRREPS={'A1':(1,1,1,1,1), 'A2':(1,1,1,-1,-1),
        'B1':(1,1,-1,1,-1),'B2':(1,1,-1,-1,1),
        'E':(2,-2,0,0,0)}
DIM={'A1':1,'A2':1,'B1':1,'B2':1,'E':2}
MONSTER_INVOLUTION_CHI={'2A':4371,'2B':275}
FULL_FIXED_SHELL={'one':8,'half':6,'quarter':2,'axis':4,'diagonal':4}

def decompose(character):
    numerator={n:sum(w*a*b for w,a,b in zip(SIZES,character,t))
               for n,t in IRREPS.items()}
    assert all(x%8==0 for x in numerator.values()),numerator
    return {k:v//8 for k,v in numerator.items()}

def audit():
    assert sum(SIZES)==8
    # A 10D involution always has even integer trace tau in [-10,10].
    survivors=[]
    for monster_cls,chi in MONSTER_INVOLUTION_CHI.items():
        for tau in range(-10,11,2):
            residual=chi-3**FULL_FIXED_SHELL['axis']*tau
            if abs(residual)<=53:
                survivors.append((monster_cls,tau,residual))
    assert survivors==[('2B',4,-49)],survivors
    # Source nontrivial C4 phase trace [65610,18,1458,18] is NOT a
    # certificate that the whole 196830 = 10*3^9 module embeds.
    # Quarter and half turn centre-fixed: 3 possible centre trits.
    bulk=(10*3**9, 2*3*3**6, 2*3*3**2, 4*3**4, 4*3**4)
    # Source Monster class fusion required by PR #1250: 4B and 2A,
    # and 2B for each inverted-centre reflection (forced above).
    actual=(196883,4371,51,275,275)
    assert bulk==(196830,4374,54,324,324)
    residual=tuple(a-b for a,b in zip(actual,bulk))
    assert residual==(53,-3,-3,-49,-49)
    actual_irr=decompose(actual)
    bulk_irr=decompose(bulk)
    residual_irr=decompose(residual)
    assert residual_irr=={'A1':-19,'A2':30,'B1':7,'B2':7,'E':14}
    assert actual_irr['A1']==25307
    assert bulk_irr['A1']==25326
    assert sum(DIM[k]*v for k,v in residual_irr.items())==53
    assert all(v>=0 for v in actual_irr.values())
    assert all(v>=0 for v in bulk_irr.values())
    return {
      'schema':'jfine-3b-oriented-h4-d4-residual-no-go-v1',
      'reference_sources':['Barraclough--Wilson 2007','ATLAS Monster classes',
                           'Breuer/CTblLib','DASHI PR #1250 source class screen',
                           'DASHI PR #1148 oriented eight-trit fixed spaces'],
      'assumptions':['actual 4B quarter and 2A half classes',
                     '10D marker tensor factor independent of the 8D shell',
                     'original nine-trit centre-inverting D4 source model',
                     'D4-equivariant injection of entire 196830-dimensional bulk',
                     'genuine D4-stable complementary 53D module'],
      'forced_inverting_reflection_Monster_class':'2B',
      'unique_admissible_marker_involution_trace':4,
      'full_character':dict(zip(CLASSES,actual)),
      'pointed_bulk_character':dict(zip(CLASSES,bulk)),
      'putative_residual_character':dict(zip(CLASSES,residual)),
      'full_irreducible_multiplicities':actual_irr,
      'bulk_irreducible_multiplicities':bulk_irr,
      'residual_irreducible_multiplicities':residual_irr,
      'negative_trivial_multiplicity':-19,
      'direct_product_bulk_plus_53_split_possible':False,
      'C4_phase_trace_compatibility_remains_true':True,
      'all_possible_nonproduct_Monster_actions_ruled_out':False,
      'actual_Monster_action_or_group_words_observed':False,
      'GAP_or_Agda_execution_receipt':False,
    }
if __name__=='__main__':
    print(json.dumps(audit(),indent=2,sort_keys=True))

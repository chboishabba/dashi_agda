#!/usr/bin/env python3
"""Source ATLAS Suzuki quotient involution class from a commuting 7-word.

Original authority: ATLAS/AtlasRep Suzuki ordinary class centraliser orders,
  https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
  |C_Suz(2A)|=3317760 (not divisible by 7);
  |C_Suz(2B)|=161280 (divisible by 7).
Prior repo #1098: original SHA256-pinned GF3 2.Suz:2 matrices C,D, exact
D4 words r,m, and invariant alternating form. This is NOT a Monster
class-fusion or selected 6.Suz character receipt.

Notation: lowercase c=C^-1,d=D^-1. With g=DcDCDcdC,
u=r*(g^-1*r*g) and t=g*u^6, exact GF3 gives:
u^13=-I12; t^7=-I12; t*r=r*t. Thus -t has order 7 in 2.Suz
and centralises r, proving r mod centre is Suzuki involution class 2B.
"""
import json
from pathlib import Path
from monster3b_atlas_actual_d4_word_witness import (
    audit as source_audit, W_ORDER10, CONJUGATOR, inverse_word,
    form, evaluate, trans,
)
from monster3b_atlas_source_word_order_d4_gate import (
    ident,neg,mm,power,parse_meataxe,
)

G_WORD="DcDCDcdC"\nALT_G_WORD="CDCdCdCd" # = C*D*(C*d)^3, also exact length-eight
ATLAS_SUZ_CENTRALIZERS={"2A":3317760,"2B":161280}

def audit(root):
    src=source_audit(root)
    data=root/"data"/"atlas"
    C=parse_meataxe(data/"2Suzd2G1-f3r12aB0.m1")
    D=parse_meataxe(data/"2Suzd2G1-f3r12aB0.m2")
    I=ident();NI=neg(I);J=form()
    W=evaluate(W_ORDER10,C,D)
    m=power(W,5)
    g0=evaluate(CONJUGATOR,C,D)
    g0i=evaluate(inverse_word(CONJUGATOR),C,D)
    r=mm(m,mm(mm(g0,m),g0i))
    assert power(r,2)==NI and power(r,4)==I
    # Four C/c symbols: g lies in the INNER 2.Suz,
    # not the outer 2.Suz:2 coset.
    assert sum(ch in "Cc" for ch in G_WORD)%2==0
    g=evaluate(G_WORD,C,D)
    gi=evaluate(inverse_word(G_WORD),C,D)
    assert mm(g,gi)==I and mm(gi,g)==I
    assert mm(mm(trans(g),J),g)==J
    u=mm(r,mm(mm(gi,r),g))
    assert power(u,13)==NI
    assert power(u,26)==I
    t=mm(g,power(u,6))
    assert power(t,7)==NI
    assert power(t,14)==I
    assert mm(t,r)==mm(r,t)
    seven=neg(t)
    assert power(seven,7)==I and seven!=I
    assert mm(seven,r)==mm(r,seven)
    assert mm(mm(trans(seven),J),seven)==J
    # Independent SECOND length-eight source word certificate; same
    # primary ATLAS matrices, different finite group words.
    # The current-turn local exhaustive search of all 4372 freely
    # reduced words of lengths 1..7 found no witness for THIS
    # specific Bray conjugator recipe. That search was not reproduced
    # by a checked-in exhaustive runner, so do NOT mark it kernel-paid.
    assert sum(ch in "Cc" for ch in ALT_G_WORD)%2==0
    ga=evaluate(ALT_G_WORD,C,D)
    gai=evaluate(inverse_word(ALT_G_WORD),C,D)
    ua=mm(r,mm(mm(gai,r),ga))
    assert power(ua,13)==NI
    ta=mm(ga,power(ua,6))
    assert power(ta,7)==NI
    assert mm(ta,r)==mm(r,ta)
    assert power(neg(ta),7)==I and neg(ta)!=I
    assert ATLAS_SUZ_CENTRALIZERS["2A"]%7 != 0
    assert ATLAS_SUZ_CENTRALIZERS["2B"]%7 == 0
    # Projective Suzuki class rather than literal Monster conjugacy class.
    assert src["source_rotation_square_is_negative_identity"]
    return {
      "schema":"monster3b-atlas-source-rotation-suzuki-2B-by-7-centraliser-v1",
      "original_source":"ATLAS/AtlasRep Suzuki group standard 2.Suz:2 GF3 matrices and Suzuki centraliser class data",
      "original_source_URL":"https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/",
      "prior_repo_owner_PR":1098,
      "source_matrix_SHA256_manifest_verified":src["source_SHA256_manifest_matched"],
      "source_rotation_word":src["actual_source_rotation_word_SLP"],
      "source_rotation_square_is_negative_identity":True,
      "inner_Suzuki_source_word_g":G_WORD,\n      "alternate_length8_source_word_g":ALT_G_WORD,\n      "alternate_order7_centralizer_witness_verified":True,\n      "shorter_4372_reduced_words_independently_searched_this_turn":True,\n      "minimality_claim_scope":"Bray-order7 source word recipe only; independent local audit, not kernel",
      "g_outer_coset_parity":0,
      "conjugate_product_u_definition":"r*(g^-1*r*g)",
      "u_thirteenth_power_is_negative_identity":True,
      "centralizing_t_definition":"g*u^6",
      "t_seventh_power_is_negative_identity":True,
      "centralizing_order_seven_element_definition":"-t",
      "centralizing_seven_has_order_7":True,
      "centralizing_seven_exactly_commutes_with_r":True,
      "centralizing_seven_preserves_original_alternating_form":True,
      "atlas_Suzuki_twoA_centralizer_order":3317760,
      "atlas_Suzuki_twoB_centralizer_order":161280,
      "atlas_Suzuki_twoA_centralizer_divisible_by_7":False,
      "atlas_Suzuki_twoB_centralizer_divisible_by_7":True,
      "source_rotation_projective_Suzuki_involution_class":"2B",
      "source_rotation_actual_Monster_four_class_selected":False,
      "source_rotation_Monster_4A_4C_4D_class_still_open":True,
      "actual_Monster_3B_diagonal_quotient_weld":False,
      "actual_selected_6Suz_degree_78_character_paid":False,
      "actual_Wzeta_Hom_intertwiner_paid":False,
      "agda_kernel_checked":False
    }

if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args()
    data=audit(Path(__file__).resolve().parents[1])
    encoded=json.dumps(data,sort_keys=True,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(encoded)
    print(encoded,end="")

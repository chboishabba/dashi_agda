#!/usr/bin/env python3
"""Explicit D4 inside the ORIGINAL ATLAS 2.Suz:2 GF(3) matrix generators.

ORIGINAL MATHEMATICAL AND MATRIX AUTHORS: ATLAS/AtlasRep contributors,
Suzuki standard-generator semipresentation at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
Historical Monster H/X and selected diagonal H/D_i are distinct: original
Breuer--Magaard--Wilson Monster character-table verification.
PR #1098 previously vendored the source bytes, SHA256 manifest, selected GF729
and H6 lift; PR #1148 owns the non-geometric 8-trit A2 D4 model.
This is a NEW exact finite word witness, NOT an actual selected Monster D4.

C,D denote original GF3 12D matrices; c=C^-1, d=D^-1.
W = CDCDCDCDCDCdCd   has order10, and m = W^5 has order2.
g = CdCdCDCd, r = m*(g*m*g^-1).
Exact result: m^2=I, r^2=-I, m*r*m=r^-1.
Outer m is anti-symplectic and inner r symplectic on the ORIGINAL
1-dimensional invariant alternating-form line.
"""
import hashlib
from math import gcd
import json
from pathlib import Path
from monster3b_atlas_source_word_order_d4_gate import (
    ident, neg, mm, diff, rank, parse_meataxe, power
)

N=12
SOURCE_DIGESTS={
 "2Suzd2G1-f3r12aB0.m1":"ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2",
 "2Suzd2G1-f3r12aB0.m2":"433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f"
}
# Explicit witness derived by solving the F3 alternating-invariant equations
# C^T J C=-J and D^T J D=J; independently checked nondegenerate.
FORM_ROWS="""002122102121
001121022112
120000021212
220000201221
110000221021
120000212120
200111002221
011012002111
112221110201
221102121020
122111120101
211220222020"""
W_ORDER10="CDCDCDCDCDCdCd"
CONJUGATOR="CdCdCDCd"

def trans(a):return [list(col) for col in zip(*a)]
def evaluate(w,c,d):
    letters={'C':c,'D':d,'c':power(c,3),'d':power(d,2)}
    x=ident()
    for symbol in w:
        if symbol not in letters:raise ValueError("unknown ATLAS generator letter")
        x=mm(x,letters[symbol])
    return x
def inverse_word(w):
    invert={'C':'c','c':'C','D':'d','d':'D'}
    return ''.join(invert[x] for x in reversed(w))
def form():
    j=[[int(ch) for ch in line] for line in FORM_ROWS.splitlines()]
    assert len(j)==N and all(len(row)==N for row in j)
    return j

def audit(root):
    data=root/'data'/'atlas'
    for filename,want in SOURCE_DIGESTS.items():
        blob=(data/filename).read_bytes()
        if hashlib.sha256(blob).hexdigest()!=want:
            raise ValueError("original ATLAS source SHA256 mismatch: "+filename)
    C=parse_meataxe(data/'2Suzd2G1-f3r12aB0.m1')
    D=parse_meataxe(data/'2Suzd2G1-f3r12aB0.m2')
    I=ident();NI=neg(I);J=form()
    assert power(C,2)==NI and power(C,4)==I
    assert power(D,3)==I and D!=I
    assert mm(trans(J),I)==neg(J) and rank(J)==12
    assert mm(mm(trans(C),J),C)==neg(J)
    assert mm(mm(trans(D),J),D)==J
    # Original Suzuki quotient semipresentation, not new source labels.
    CD=mm(C,D)
    assert power(CD,28)==NI and power(CD,56)==I
    assert all(power(CD,k)!=I and power(CD,k)!=NI for k in (1,2,4,7,14))
    s=evaluate('cdcdcddcdd',C,D)
    assert power(s,7)==I and s!=I

    W=evaluate(W_ORDER10,C,D)
    assert power(W,10)==I and power(W,5)!=I and power(W,2)!=I
    m=power(W,5)
    assert mm(m,m)==I and m!=I
    g=evaluate(CONJUGATOR,C,D)
    gi=evaluate(inverse_word(CONJUGATOR),C,D)
    assert mm(g,gi)==I and mm(gi,g)==I
    m2=mm(mm(g,m),gi)
    assert mm(m2,m2)==I
    r=mm(m,m2)
    assert mm(r,r)==NI and power(r,4)==I
    assert mm(mm(m,r),m)==power(r,3)
    assert mm(mm(trans(m),J),m)==neg(J)
    assert mm(mm(trans(r),J),r)==J
    # This specific D4 does not contain the earlier A2 steelman's
    # six-dimensional r^2 fixed submodule: here r^2=-I12.
    assert rank(diff(mm(r,r),I))==12
    # m*r is the other reflection type and has +1-eigenspace dimension 6.
    # All 12 source vectors lie in the E-isotypic D4 component:
    # r^2=-I rules out ANY one-dimensional D4 irreducible constituent
    # (on every 1D D4 character r^2 acts as +I).
    mr=mm(m,r)
    assert mm(mr,mr)==I and rank(diff(mr,I))==6
    assert sum(r[i][i] for i in range(N))%3==0

    assert rank(diff(m,I))==6
    assert gcd(3**13,8)==1  # Schur-Zassenhaus normal-Hall hypothesis, not theorem runtime proof.
    return {
      "schema":"monster3b-atlas-2suz2-exact-source-d4-word-v1",
      "source_original_authority":"ATLAS/AtlasRep original 2.Suz:2 GF3 generators",
      "source_SHA256_manifest_matched":True,
      "source_projective_CD_order":28,"source_linear_CD_order":56,
      "source_semipresentation_relation_order":7,
      "source_word_order10":W_ORDER10,"source_word_order10_verified":True,
      "actual_source_reflection_word_SLP":"("+W_ORDER10+")^5",
      "actual_source_conjugator_word":CONJUGATOR,
      "actual_source_rotation_word_SLP":"m*g*m*g^-1 (m=(W)^5)",
      "source_mirror_order":2,"source_rotation_order":4,
      "source_rotation_square_is_negative_identity":True,
      "D4_presentation_verified":True,
      "invariant_alternating_form_rank":12,
      "source_mirror_similitude_multiplier":2,
      "source_rotation_similitude_multiplier":1,
      "source_mirror_fixed_dimension":6,
      "source_half_turn_fixed_dimension":0,
      "source_other_reflection_fixed_dimension":6,
      "source_D4_module_irrep_decomposition":"6 E (12D, characteristic 3)",
      "source_D4_no_one_dimensional_irrep_summands":True,
      "old_A2_eight_shell_half_turn_fixed_dimension":6,
      "old_A2_eight_shell_equivariant_injective_into_this_D4":False,
      "actual_ATLAS_2Suz2_source_word_membership":True,
      "actual_Monster_3B_selected_diagonal_quotient_weld":False,
      "actual_Monster_involution_class_fusion":False,
      "actual_Monster_source_selected_78_character":False,
      "full_Monster_Schrodinger_Hom_action":False,
      "normal_3B_extraspecial_kernel_order_if_source_structure_admitted":3**13,
      "source_D4_quotient_order":8,
      "Schur_Zassenhaus_coprime_Hall_hypothesis":True,
      "actual_N3B_D4_complement_exists_by_classical_theorem_given_BW_quotient":True,
      "explicit_Monster_group_generator_words_produced":False,
      "agda_kernel_checked":False,
    }
if __name__=="__main__":
    print(json.dumps(audit(Path(__file__).resolve().parents[1]),sort_keys=True,indent=2))

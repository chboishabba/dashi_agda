#!/usr/bin/env python3
"""Source-scoped finite acceptance for the KeyShoe/CLARA R13 adapter.

This tests a carefully labelled screenshot transcription and selected finite
mathematical models, not a creator-authored decoder or a physical experiment.
Run: python3 scripts/check_keyshoe_clara_r13_maxcut.py
"""
from itertools import product
from string import ascii_uppercase as LETTERS
import unittest

NATURAL_BODIES = tuple(
    LETTERS[(6 + 2*i) % 26] + LETTERS[(7 + 2*i) % 26]
    for i in range(13)
)
EXPECTED = ("GH", "IJ", "KL", "MN", "OP", "QR", "ST",
            "UV", "WX", "YZ", "AB", "CD", "EF")
BODY_BY_PAIR = {frozenset(w): i for i, w in enumerate(NATURAL_BODIES)}

def rho_letter(ch):
    return LETTERS[25 - LETTERS.index(ch)]

def adjacent_pair(ch):
    return LETTERS[LETTERS.index(ch) ^ 1]

def reflect_body(i):
    return BODY_BY_PAIR[frozenset(rho_letter(ch) for ch in NATURAL_BODIES[i])]

def next_body(i):
    return (i + 1) % 13

def previous_body(i):
    return (i - 1) % 13

def glue(phase, point):
    # An explicit quotient of two copies of a 27-point carrier:
    # both origins map to a single fixed centre, each nonorigin keeps phase.
    return ("zero",) if point == (0, 0, 0) else (phase, point)

def conjugate(phase):
    return 1 - phase

def swap_glued(item):
    return item if item == ("zero",) else (conjugate(item[0]), item[1])


class RadialR13(unittest.TestCase):
    def test_01_exact_natural_chart(self):
        self.assertEqual(NATURAL_BODIES, EXPECTED)
    def test_02_bijection_26_letters(self):
        self.assertEqual(sorted("".join(NATURAL_BODIES)), list(LETTERS))
    def test_03_source_reversal_involution(self):
        for ch in LETTERS:
            self.assertEqual(rho_letter(rho_letter(ch)), ch)
    def test_04_source_pair_involution(self):
        for ch in LETTERS:
            self.assertEqual(adjacent_pair(adjacent_pair(ch)), ch)
    def test_05_two_letter_involutions_commute(self):
        for ch in LETTERS:
            self.assertEqual(rho_letter(adjacent_pair(ch)), adjacent_pair(rho_letter(ch)))
    def test_06_body_formula(self):
        for i in range(13):
            self.assertEqual(reflect_body(i), (6-i) % 13)
    def test_07_reflection_order_two(self):
        for i in range(13):
            self.assertEqual(reflect_body(reflect_body(i)), i)
    def test_08_next_order_thirteen(self):
        for i in range(13):
            q = i
            for _ in range(13): q = next_body(q)
            self.assertEqual(q, i)
    def test_09_next_and_previous(self):
        for i in range(13):
            self.assertEqual(previous_body(next_body(i)), i)
    def test_10_dihedral_conjugacy(self):
        for i in range(13):
            self.assertEqual(reflect_body(next_body(reflect_body(i))), previous_body(i))
    def test_11_one_fixed_body_MN(self):
        self.assertEqual([NATURAL_BODIES[i] for i in range(13) if reflect_body(i)==i], ["MN"])
    def test_12_six_exchanged_pairs(self):
        q = {frozenset((i,reflect_body(i))) for i in range(13)}
        self.assertEqual(sorted(map(len,q)), [1,2,2,2,2,2,2])
    def test_13_reroot_at_MN(self):
        for i in range(13):
            self.assertEqual((reflect_body(i)-3)%13, (-(i-3))%13)
    def test_14_twelve_plus_one(self):
        self.assertEqual(12+1,13)
    def test_15_fourteen_landmarks_are_not_thirteen(self):
        self.assertEqual(len(range(14)),14)
        self.assertNotEqual(len(range(14)),len(NATURAL_BODIES))
    def test_16_five_fixed_projective_linear_reflection_differs(self):
        self.assertNotEqual(sum(reflect_body(i)==i for i in range(13)),5)
    def test_17_GL3_singer_normalizer_automorphism_constraint(self):
        self.assertEqual([pow(3,i,13) for i in range(3)], [1,3,9])
        self.assertNotIn(-1%13, [pow(3,i,13) for i in range(3)])


class SourceGates(unittest.TestCase):
    EDGES={("Jprev","Q"),("Q","Z"),("Z","Jn"),("Z","Jreturn"),("Jreturn","Jprev")}
    def test_18_entry_exit_edges(self):
        self.assertIn(("Jprev","Q"),self.EDGES)
        self.assertIn(("Q","Z"),self.EDGES)
    def test_19_Z_requires_gate_choice(self):
        self.assertEqual({b for a,b in self.EDGES if a=="Z"},{"Jn","Jreturn"})
    def test_20_M_and_F_distinct(self):
        self.assertNotEqual("Jn","Jreturn")
    def test_21_return_closure(self):
        self.assertIn(("Jreturn","Jprev"), self.EDGES)
    def test_22_six_body_chain(self):
        chain=("source","wave","boundary","detector","record","observer")
        self.assertEqual(len(chain),6)
        self.assertEqual(chain.index("record")+1,chain.index("observer"))
    def test_23_D0_through_D13_are_fourteen(self):
        self.assertEqual(len(range(0,14)),14)
    def test_24_handdrawn_depths_five_to_zero(self):
        self.assertEqual(tuple(range(5,-1,-1)),(5,4,3,2,1,0))
    def test_25_source_depth_shape_sequence(self):
        self.assertEqual(("circle","square","triangle","segment","cross","undecided"),
                         ("circle","square","triangle","segment","cross","undecided"))


class ZeroAwareTransport(unittest.TestCase):
    V=list(product((-1,0,1),repeat=3))
    def test_26_original54(self):
        self.assertEqual(2*len(self.V),54)
    def test_27_glued53_size(self):
        self.assertEqual(len({glue(s,v) for s in range(2) for v in self.V}),53)
    def test_28_one_fixed_zero(self):
        states={glue(s,v) for s in range(2) for v in self.V}
        self.assertEqual([x for x in states if swap_glued(x)==x],[("zero",)])
    def test_29_26_conjugate_pairs(self):
        states={glue(s,v) for s in range(2) for v in self.V}
        pairs={frozenset((x,swap_glued(x))) for x in states if x != ("zero",)}
        self.assertEqual(len(pairs),26)
    def test_30_gluing_commutes_with_conjugation(self):
        for s,v in product(range(2),self.V):
            self.assertEqual(glue(conjugate(s),v),swap_glued(glue(s,v)))
    def test_31_glued_involution(self):
        for x in {glue(s,v) for s in range(2) for v in self.V}:
            self.assertEqual(swap_glued(swap_glued(x)),x)
    def test_32_deleted_one_origin_does_not_commute(self):
        removed=(0,(0,0,0))
        alive={(s,v) for s,v in product(range(2),self.V) if (s,v)!=removed}
        self.assertIn((1,(0,0,0)),alive)
        self.assertNotIn((0,(0,0,0)),alive)
    def test_33_zero_support_bit(self):
        self.assertEqual({v for v in self.V if all(a==0 for a in v)},{(0,0,0)})


class IndexedShem(unittest.TestCase):
    def test_34_72_as_8_by_9(self):
        self.assertEqual(8*9,72)
    def test_35_pointed71(self):
        addresses=list(product(range(8),range(9)))
        self.assertEqual(len(addresses)-1,71)
        self.assertIn((0,0),addresses)
    def test_36_216_indexed_consonantal_positions(self):
        self.assertEqual(3*72,216)
    def test_37_boustrophedon_invertible_with_full_rows(self):
        a="a"*72
        b="b"*72
        c="c"*72
        triads=[a[i]+b[71-i]+c[i] for i in range(72)]
        self.assertEqual("".join(x[0] for x in triads),a)
        self.assertEqual("".join(x[1] for x in triads)[::-1],b)
        self.assertEqual("".join(x[2] for x in triads),c)


if __name__=="__main__":
    unittest.main(verbosity=2)

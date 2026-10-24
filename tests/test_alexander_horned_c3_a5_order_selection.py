"""Regression for deterministic A5 commutator root selection.

Original sources: Hatcher, Algebraic Topology Ex 2B.2;
Riebe (1968) on related horned-sphere group representations.
DASHI tests the chosen *finite nonabelian quotient*, not the geometric pi1.

The original generating-pair-only predicate chose an order-three
root and contradicted the VOA script's asserted order FIVE.  This
test prevents that selection ambiguity from silently recurring.
"""
import sys
from pathlib import Path
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import alexander_horned_c3_a5_probe as A5
import alexander_horned_c3_voa_a5_action_probe as VOA


class HornA5RootOrderTests(unittest.TestCase):
    def test_old_unconstrained_first_generating_commutator_is_order_three(self):
        first=None
        for a in A5.A5:
            for b in A5.A5:
                g=A5.commutator(a,b)
                if g!=A5.ID and A5.generated_order((a,b))==60:
                    first=(g,a,b)
                    break
            if first:
                break
        self.assertEqual(A5.permutation_order(first[0]),3)

    def test_chosen_A5_root_is_five_and_both_probes_agree(self):
        _,root=A5.build_witnesses()
        _,voa_root=VOA.exhaustive_commutator_section()
        self.assertEqual(root,voa_root)
        g,a,b=root
        self.assertEqual(A5.commutator(a,b),g)
        self.assertEqual(A5.generated_order((a,b)),60)
        self.assertEqual(A5.permutation_order(g),5)
        self.assertEqual(VOA.order(g),5)
        self.assertEqual(g,A5.compose(g,A5.ID))

    def test_selected_finite_image_kills_fifth_meridian_power(self):
        _,(g,_,_)=A5.build_witnesses()
        power=A5.ID
        for _ in range(5):
            power=A5.compose(power,g)
        self.assertEqual(power,A5.ID)
        self.assertNotEqual(g,A5.ID)
        # This is a property of the A5 quotient, not the source G.
        # Hatcher's injective free-group tower is needed for m^5 != 1.

    def test_order_three_ambient_rotation_is_a_distinct_element(self):
        _,(g,_,_)=A5.build_witnesses()
        slot=A5.in_factor(g,0)
        self.assertNotEqual(slot,A5.in_factor(g,1))
        self.assertEqual(A5.c3_rotate(A5.c3_rotate(A5.c3_rotate(slot))),slot)
        self.assertEqual(A5.c3_rotate(slot),A5.in_factor(g,1))


if __name__=="__main__":
    unittest.main()

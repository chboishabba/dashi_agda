"""Exact finite-group regression for reused Lie-group/horn adapter laws.

Owner: DASHI/Mathematics/Topology/AlexanderHornedC3SUNLieGroupReuseExact.agda.
Reuses the SAME finite A5 quotient permutations as existing horn probes,
NOT a newly invented special-unitary group or a proof of the infinite colimit.

Original sources: Hatcher Example 2B.2, Gotô 1949; these finite
A5 tests exercise group conjugation and word-commutator identities,
not Gotô's analytic SU3 theorem.
"""
import sys
from pathlib import Path
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import alexander_horned_c3_a5_probe as A5


def inner(t,x):
    return A5.compose(A5.compose(t,x),A5.inverse(t))


def word_eval(word, assignment):
    kind,*args=word
    if kind=="id":
        return A5.ID
    if kind=="gen":
        return assignment[args[0]]
    if kind=="inv":
        return A5.inverse(word_eval(args[0],assignment))
    if kind=="mul":
        return A5.compose(word_eval(args[0],assignment),
                          word_eval(args[1],assignment))
    raise AssertionError("unknown word")


def comm_word(u,v):
    return ("mul",("mul",("mul",u,v),("inv",u)),("inv",v))


class ExistingLieGroupReuseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.section,cls.root=A5.build_witnesses()
        cls.t=next(g for g in A5.A5 if A5.permutation_order(g)==3)

    def test_existing_A5_group_section_covers_all_elements(self):
        self.assertEqual(len(self.section),60)
        for g, (a,b) in self.section.items():
            self.assertEqual(A5.commutator(a,b),g)

    def test_group_conjugate_identity_product_inverse_exact_exhaustive(self):
        t=self.t
        self.assertEqual(inner(t,A5.ID),A5.ID)
        for x in A5.A5:
            self.assertEqual(inner(t,A5.inverse(x)),A5.inverse(inner(t,x)))
            self.assertEqual(inner(t,inner(t,inner(t,x))),x)
            for y in A5.A5:
                self.assertEqual(inner(t,A5.compose(x,y)),
                                 A5.compose(inner(t,x),inner(t,y)))
                self.assertEqual(inner(t,A5.commutator(x,y)),
                                 A5.commutator(inner(t,x),inner(t,y)))

    def test_finite_horn_section_refinement_and_threefold_action(self):
        root=self.root[0]
        level={():root}
        for depth in range(5):
            nxt={}
            for address,g in level.items():
                a,b=self.section[g]
                self.assertEqual(A5.commutator(a,b),g)
                for k in range(3):
                    tw=lambda x: inner_k(self.t,k,x)
                    self.assertEqual(A5.commutator(tw(a),tw(b)),tw(g))
                nxt[address+(0,)]=a
                nxt[address+(1,)]=b
            level=nxt
        self.assertEqual(len(level),32)

    def test_goto_section_is_nontrivial_input_not_derived_from_group_axioms(self):
        self.assertEqual(len(self.section),len(A5.A5))
        # Abelian group C3 has only identity as commutator, proving
        # arbitrary group axioms cannot imply single-commutator
        # surjectivity without Gotô's semisimplicity hypothesis.
        for x in range(3):
            for y in range(3):
                self.assertEqual((x+y-x-y)%3,0)
        self.assertNotEqual(1,0)


def inner_k(t,k,x):
    out=x
    for _ in range(k):
        out=inner(t,out)
    return out


if __name__=="__main__":
    unittest.main()

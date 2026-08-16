module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlDiagonalAtomsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact

flatDiagonal0 : ∀ a b c d →
  wilsonAtomContribution
    (factorSecond (flatExponentialJet a) *q
      orderedValueProduct
        (flatExponentialJet b ∷ flatExponentialJet (negV c) ∷
          flatExponentialJet (negV d) ∷ []))
  ≡ vectorDot a a
flatDiagonal0 a b c d =
  trans
    (cong wilsonAtomContribution
      (trans
        (cong (factorSecond (flatExponentialJet a) *q_)
          (flatTailValueThree b (negV c) (negV d)))
        (oneQMultiplyRight (factorSecond (flatExponentialJet a)))))
    (pureSquareScalar a)

flatDiagonal1 : ∀ b c d →
  wilsonAtomContribution
    (factorSecond (flatExponentialJet b) *q
      orderedValueProduct
        (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ []))
  ≡ vectorDot b b
flatDiagonal1 b c d =
  trans
    (cong wilsonAtomContribution
      (trans
        (cong (factorSecond (flatExponentialJet b) *q_)
          (flatTailValueTwo (negV c) (negV d)))
        (oneQMultiplyRight (factorSecond (flatExponentialJet b)))))
    (pureSquareScalar b)

flatDiagonal2 : ∀ c d →
  wilsonAtomContribution
    (factorSecond (flatExponentialJet (negV c)) *q
      orderedValueProduct (flatExponentialJet (negV d) ∷ []))
  ≡ vectorDot c c
flatDiagonal2 c d =
  trans
    (cong wilsonAtomContribution
      (trans
        (cong (factorSecond (flatExponentialJet (negV c)) *q_)
          (flatTailValueOne (negV d)))
        (oneQMultiplyRight
          (factorSecond (flatExponentialJet (negV c))))))
    (trans
      (pureSquareScalar (negV c))
      (vectorDotNegBoth c c))

flatDiagonal3 : ∀ d →
  wilsonAtomContribution
    (factorSecond (flatExponentialJet (negV d)) *q orderedValueProduct [])
  ≡ vectorDot d d
flatDiagonal3 d =
  trans
    (cong wilsonAtomContribution
      (oneQMultiplyRight
        (factorSecond (flatExponentialJet (negV d)))))
    (trans
      (pureSquareScalar (negV d))
      (vectorDotNegBoth d d))

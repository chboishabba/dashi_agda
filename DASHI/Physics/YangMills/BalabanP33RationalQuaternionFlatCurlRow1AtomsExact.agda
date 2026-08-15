module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlRow1AtomsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using (_+_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact

row1PairBC : ∀ b c d →
  wilsonAtomContribution
    (pureQuaternion b *q
      (pureQuaternion (negV c) *q
        orderedValueProduct (flatExponentialJet (negV d) ∷ [])))
  ≡ - vectorDot b c
row1PairBC b c d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion b *q_)
        (trans
          (cong (pureQuaternion (negV c) *q_)
            (flatTailValueOne (negV d)))
          (oneQMultiplyRight (pureQuaternion (negV c))))))
    (pureNegRightScalar b c)

row1PairBD : ∀ b d →
  wilsonAtomContribution
    (pureQuaternion b *q
      (pureQuaternion (negV d) *q orderedValueProduct []))
  ≡ - vectorDot b d
row1PairBD b d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion b *q_)
        (oneQMultiplyRight (pureQuaternion (negV d)))))
    (pureNegRightScalar b d)

row1OneOrderedCopy : ∀ b c d →
  pairAtomSum (pureQuaternion b)
    (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ [])
  ≡ (- vectorDot b c) + (- vectorDot b d)
row1OneOrderedCopy b c d
  rewrite pairAtomSumFlatCons
      (pureQuaternion b)
      (pureQuaternion (negV c))
      (pureQuaternion (negV c) *q pureQuaternion (negV c))
      (flatExponentialJet (negV d) ∷ [])
    | pairAtomSumFlatCons
      (pureQuaternion b)
      (pureQuaternion (negV d))
      (pureQuaternion (negV d) *q pureQuaternion (negV d))
      []
    | row1PairBC b c d
    | row1PairBD b d
    | ℚP.+-identityʳ (- vectorDot b d) = refl

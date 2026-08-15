module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlRow0AtomsExact where

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
open import Data.Rational.Base as ℚ using (_+_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact

row0PairAB : ∀ a b c d →
  wilsonAtomContribution
    (pureQuaternion a *q
      (pureQuaternion b *q
        orderedValueProduct
          (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ [])))
  ≡ vectorDot a b
row0PairAB a b c d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion a *q_)
        (trans
          (cong (pureQuaternion b *q_)
            (flatTailValueTwo (negV c) (negV d)))
          (oneQMultiplyRight (pureQuaternion b)))))
    (pureProductScalar a b)

row0PairAC : ∀ a c d →
  wilsonAtomContribution
    (pureQuaternion a *q
      (pureQuaternion (negV c) *q
        orderedValueProduct (flatExponentialJet (negV d) ∷ [])))
  ≡ - vectorDot a c
row0PairAC a c d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion a *q_)
        (trans
          (cong (pureQuaternion (negV c) *q_)
            (flatTailValueOne (negV d)))
          (oneQMultiplyRight (pureQuaternion (negV c))))))
    (pureNegRightScalar a c)

row0PairAD : ∀ a d →
  wilsonAtomContribution
    (pureQuaternion a *q
      (pureQuaternion (negV d) *q orderedValueProduct []))
  ≡ - vectorDot a d
row0PairAD a d =
  trans
    (cong wilsonAtomContribution
      (cong (pureQuaternion a *q_)
        (oneQMultiplyRight (pureQuaternion (negV d)))))
    (pureNegRightScalar a d)

row0OneOrderedCopy : ∀ a b c d →
  pairAtomSum (pureQuaternion a)
    (flatExponentialJet b ∷ flatExponentialJet (negV c) ∷
      flatExponentialJet (negV d) ∷ [])
  ≡ vectorDot a b + ((- vectorDot a c) + (- vectorDot a d))
row0OneOrderedCopy a b c d =
  trans
    (pairAtomSumFlatCons
      (pureQuaternion a)
      (pureQuaternion b)
      (pureQuaternion b *q pureQuaternion b)
      (flatExponentialJet (negV c) ∷ flatExponentialJet (negV d) ∷ []))
    (trans
      (cong (row0PairAB a b c d |>left_) -- placeholder removed below
        (pairAtomSumFlatCons
          (pureQuaternion a)
          (pureQuaternion (negV c))
          (pureQuaternion (negV c) *q pureQuaternion (negV c))
          (flatExponentialJet (negV d) ∷ [])))
      (trans
        (cong
          (λ selected →
            wilsonAtomContribution
              (pureQuaternion a *q
                (pureQuaternion b *q
                  orderedValueProduct
                    (flatExponentialJet (negV c) ∷
                      flatExponentialJet (negV d) ∷ [])))
            + (wilsonAtomContribution
                (pureQuaternion a *q
                  (pureQuaternion (negV c) *q
                    orderedValueProduct (flatExponentialJet (negV d) ∷ [])))
              + selected))
          (pairAtomSumFlatCons
            (pureQuaternion a)
            (pureQuaternion (negV d))
            (pureQuaternion (negV d) *q pureQuaternion (negV d))
            []))
        (trans
          (cong
            (λ selected →
              wilsonAtomContribution
                (pureQuaternion a *q
                  (pureQuaternion b *q
                    orderedValueProduct
                      (flatExponentialJet (negV c) ∷
                        flatExponentialJet (negV d) ∷ [])))
              + (wilsonAtomContribution
                  (pureQuaternion a *q
                    (pureQuaternion (negV c) *q
                      orderedValueProduct (flatExponentialJet (negV d) ∷ [])))
                + selected))
            (trans
              (cong (_+ pairAtomSum (pureQuaternion a) [])
                (row0PairAD a d))
              (ℚP.+-identityʳ (- vectorDot a d))))
          (cong₂ _+_
            (row0PairAB a b c d)
            (cong₂ _+_ (row0PairAC a c d) refl)))))
  where
    infix 0 _|>left_
    _|>left_ : ∀ {x y z : ℚ.ℚ} → x ≡ y → z ≡ z
    _|>left_ proof = refl

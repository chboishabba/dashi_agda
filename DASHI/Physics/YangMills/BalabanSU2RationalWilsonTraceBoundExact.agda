{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact as Pos

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

chordalDistanceNonnegative :
  ∀ q → 0ℚ ≤ SU2.literalChordalDistanceSq q
chordalDistanceNonnegative q =
  ℚP.+-mono-≤
    (Pos.squareNonnegative (SU2.realPart q - 1ℚ))
    (ℚP.+-mono-≤
      (Pos.squareNonnegative (SU2.imagI q))
      (ℚP.+-mono-≤
        (Pos.squareNonnegative (SU2.imagJ q))
        (Pos.squareNonnegative (SU2.imagK q))))

wilsonTraceDeficitNonnegative :
  ∀ q → 0ℚ ≤ SU2.wilsonTraceDeficit q
wilsonTraceDeficitNonnegative q =
  ℚP.*-cancelˡ-≤-pos twoℚ
    (subst
      (λ right → 0ℚ ≤ right)
      (sym (SU2.unitChordalEqualsTwiceTraceDeficit q))
      (chordalDistanceNonnegative q))

normalizedTraceUpperBound :
  ∀ q → SU2.realPart q ≤ 1ℚ
normalizedTraceUpperBound q =
  let d = wilsonTraceDeficitNonnegative q
  in
  ℚP.≤-trans
    (subst
      (λ x → SU2.realPart q ≤ x)
      (sym (ℚP.+-identityʳ (SU2.realPart q)))
      (ℚP.+-mono-≤
        (ℚP.≤-refl {x = SU2.realPart q})
        d))
    (subst
      (λ x → SU2.realPart q ≤ x)
      (regroup (SU2.realPart q))
      (ℚP.≤-refl {x = 1ℚ}))
  where
  regroup : ∀ a → a + (1ℚ - a) ≡ 1ℚ
  regroup a = trans
    (sym (ℚP.+-assoc a 1ℚ (- a)))
    (trans
      (cong (a +_) (ℚP.+-comm 1ℚ (- a)))
      (trans
        (ℚP.+-assoc a (- a) 1ℚ)
        (trans
          (cong (_+ 1ℚ) (ℚP.+-inverseʳ a))
          (ℚP.+-identityˡ 1ℚ))))

negateQuaternion :
  SU2.RationalUnitQuaternion → SU2.RationalUnitQuaternion
negateQuaternion q =
  SU2.rationalUnitQuaternion
    (- SU2.realPart q)
    (- SU2.imagI q)
    (- SU2.imagJ q)
    (- SU2.imagK q)
    (trans
      (cong
        (λ a → a
          + (- SU2.imagI q) * (- SU2.imagI q)
          + (- SU2.imagJ q) * (- SU2.imagJ q)
          + (- SU2.imagK q) * (- SU2.imagK q))
        (Pos.negSquare (SU2.realPart q)))
      (trans
        (cong
          (λ b → SU2.realPart q * SU2.realPart q
            + b
            + (- SU2.imagJ q) * (- SU2.imagJ q)
            + (- SU2.imagK q) * (- SU2.imagK q))
          (Pos.negSquare (SU2.imagI q)))
        (trans
          (cong
            (λ c → SU2.realPart q * SU2.realPart q
              + SU2.imagI q * SU2.imagI q
              + c
              + (- SU2.imagK q) * (- SU2.imagK q))
            (Pos.negSquare (SU2.imagJ q)))
          (trans
            (cong
              (λ d → SU2.realPart q * SU2.realPart q
                + SU2.imagI q * SU2.imagI q
                + SU2.imagJ q * SU2.imagJ q
                + d)
              (Pos.negSquare (SU2.imagK q)))
            (SU2.unitNormExact q)))))

normalizedTraceLowerBound :
  ∀ q → - 1ℚ ≤ SU2.realPart q
normalizedTraceLowerBound q =
  ℚP.neg-antimono-≤
    (normalizedTraceUpperBound (negateQuaternion q))

record RationalSU2NormalizedTraceBound (q : SU2.RationalUnitQuaternion) : Set where
  constructor traceBound
  field
    lower : - 1ℚ ≤ SU2.realPart q
    upper : SU2.realPart q ≤ 1ℚ

normalizedTraceBound :
  ∀ q → RationalSU2NormalizedTraceBound q
normalizedTraceBound q =
  traceBound (normalizedTraceLowerBound q) (normalizedTraceUpperBound q)

rationalSU2NormalizedTraceBoundLevel : ProofLevel
rationalSU2NormalizedTraceBoundLevel = machineChecked

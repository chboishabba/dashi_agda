module DASHI.Physics.YangMills.BalabanSU2PolarizationWardDerived where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ; 0ℝ; _+ℝ_; _-ℝ_; subSelf; +-identityˡ )

finitePolarization :
  ∀ {b d : Level}
  {Background : Set b} {Direction : Set d} →
  (Background → ℝ) →
  (Background → Direction → Background) →
  (Direction → Direction → Direction) →
  Background → Direction → Direction → ℝ
finitePolarization effectiveAction shift addDirection zeroBackground left right =
  (effectiveAction (shift zeroBackground (addDirection left right))
    -ℝ effectiveAction (shift zeroBackground left))
  +ℝ
  (effectiveAction zeroBackground
    -ℝ effectiveAction (shift zeroBackground right))

-- Gauge invariance after an arbitrary physical displacement and at the origin
-- forces the mixed second variation with a gauge direction to vanish.  Thus the
-- Ward identity is derived from invariance rather than stored in the
-- polarization record.
polarizationWardRight :
  ∀ {b d : Level}
  {Background : Set b} {Direction : Set d}
  (effectiveAction : Background → ℝ)
  (shift : Background → Direction → Background)
  (addDirection : Direction → Direction → Direction)
  (zeroBackground : Background)
  (gaugeDirection : Direction) →
  (∀ direction →
    effectiveAction
      (shift zeroBackground (addDirection direction gaugeDirection))
      ≡ effectiveAction (shift zeroBackground direction)) →
  effectiveAction (shift zeroBackground gaugeDirection)
    ≡ effectiveAction zeroBackground →
  ∀ direction →
  finitePolarization
    effectiveAction shift addDirection zeroBackground
    direction gaugeDirection
    ≡ 0ℝ
polarizationWardRight
  effectiveAction shift addDirection zeroBackground gaugeDirection
  invariantAfter invariantAtZero direction =
  trans
    (cong₂ _+ℝ_
      (cong₂ _-ℝ_
        (invariantAfter direction)
        refl)
      (cong₂ _-ℝ_
        refl
        invariantAtZero))
    (trans
      (cong₂ _+ℝ_
        (subSelf (effectiveAction (shift zeroBackground direction)))
        (subSelf (effectiveAction zeroBackground)))
      (+-identityˡ 0ℝ))

polarizationSymmetric :
  ∀ {b d : Level}
  {Background : Set b} {Direction : Set d}
  (effectiveAction : Background → ℝ)
  (shift : Background → Direction → Background)
  (addDirection : Direction → Direction → Direction)
  (zeroBackground : Background) →
  (∀ left right → addDirection left right ≡ addDirection right left) →
  (∀ left right →
    (effectiveAction (shift zeroBackground left)
      -ℝ effectiveAction (shift zeroBackground right))
    ≡
    (effectiveAction (shift zeroBackground right)
      -ℝ effectiveAction (shift zeroBackground left))) →
  ∀ left right →
  finitePolarization effectiveAction shift addDirection zeroBackground left right
    ≡
  finitePolarization effectiveAction shift addDirection zeroBackground right left
polarizationSymmetric
  effectiveAction shift addDirection zeroBackground
  addCommutative differenceSymmetric left right =
  cong₂ _+ℝ_
    (trans
      (cong
        (λ background →
          effectiveAction (shift zeroBackground background)
            -ℝ effectiveAction (shift zeroBackground left))
        (addCommutative left right))
      (differenceSymmetric right left))
    (differenceSymmetric left right)

polarizationWardLeftFromSymmetry :
  ∀ {d : Level} {Direction : Set d}
  (polarization : Direction → Direction → ℝ)
  (gaugeDirection : Direction) →
  (∀ left right → polarization left right ≡ polarization right left) →
  (∀ direction → polarization direction gaugeDirection ≡ 0ℝ) →
  ∀ direction → polarization gaugeDirection direction ≡ 0ℝ
polarizationWardLeftFromSymmetry
  polarization gaugeDirection symmetric wardRight direction =
  trans (symmetric gaugeDirection direction) (wardRight direction)

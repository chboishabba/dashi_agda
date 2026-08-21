module DASHI.Physics.Closure.NSAncientBlowupOscillationNormalizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- Authors: Zhen Lei; Qi S. Zhang; Na Zhao.
-- Title: "Improved Liouville theorems for axially symmetric Navier-Stokes
--         equations".
-- DOI: 10.1360/N012016-00149.
-- arXiv: 1701.00868.
--
-- SOURCE FACT BEING SHARPENED
-- The standard maximum-amplitude blow-up extraction gives a bounded ancient
-- mild limit normalized by |v(0,0)| = 1.  That point normalization does not
-- exclude a nonzero constant ancient solution.  The logically sufficient
-- replacement is a spatial oscillation witness: two spatial points at one
-- time whose values differ.  Such a witness is invariant under adding a
-- common Galilean velocity and directly contradicts spatial constancy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; -_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
open import Relation.Nullary.Negation.Core using (¬_)

SpatiallyConstant : {X V : Set} → (X → V) → Set
SpatiallyConstant u = (x y : X) → u x ≡ u y

record SpatialOscillationWitness {X V : Set} (u : X → V) : Set where
  field
    leftPoint rightPoint : X
    separated : ¬ (u leftPoint ≡ u rightPoint)

open SpatialOscillationWitness public

oscillationRulesOutSpatialConstancy :
  {X V : Set} {u : X → V} →
  SpatialOscillationWitness u →
  ¬ SpatiallyConstant u
oscillationRulesOutSpatialConstancy witness constant =
  separated witness (constant (leftPoint witness) (rightPoint witness))

addCommonVelocity : {X : Set} → (X → ℚ) → ℚ → X → ℚ
addCommonVelocity u c x = u x + c

translateEqualityCancels :
  (a b c : ℚ) →
  a + c ≡ b + c →
  a ≡ b
translateEqualityCancels a b c eq =
  let
    leftMeaning : (a + c) + (- c) ≡ a
    leftMeaning =
      trans
        (sym (ℚP.+-assoc a c (- c)))
        (trans
          (cong (a +_) (ℚP.+-inverseʳ c))
          (ℚP.+-identityʳ a))

    rightMeaning : (b + c) + (- c) ≡ b
    rightMeaning =
      trans
        (sym (ℚP.+-assoc b c (- c)))
        (trans
          (cong (b +_) (ℚP.+-inverseʳ c))
          (ℚP.+-identityʳ b))
  in
  trans
    (sym leftMeaning)
    (trans (cong (_+ (- c)) eq) rightMeaning)

commonVelocityPreservesSeparation :
  {X : Set} {u : X → ℚ} →
  (c : ℚ) →
  (witness : SpatialOscillationWitness u) →
  SpatialOscillationWitness (addCommonVelocity u c)
commonVelocityPreservesSeparation c witness = record
  { leftPoint = leftPoint witness
  ; rightPoint = rightPoint witness
  ; separated = λ shiftedEqual →
      separated witness
        (translateEqualityCancels
          (u (leftPoint witness))
          (u (rightPoint witness))
          c shiftedEqual)
  }

-- Concrete counterexample to using only a point normalization such as
-- |U(0,0)| = 1 to infer spatial nonconstancy.
constantOne : Bool → ℚ
constantOne _ = 1ℚ

constantOnePointNormalized : constantOne false ≡ 1ℚ
constantOnePointNormalized = refl

constantOneSpatiallyConstant : SpatiallyConstant constantOne
constantOneSpatiallyConstant x y = refl

pointNormalizationAloneDoesNotExcludeAConstant :
  constantOne false ≡ 1ℚ
pointNormalizationAloneDoesNotExcludeAConstant = constantOnePointNormalized

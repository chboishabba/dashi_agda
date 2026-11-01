module DASHI.Physics.Closure.NSTriadKNHHBadCeilingExistenceIffStrictTargetsRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Close the numerical quantifier elimination exactly. For nonnegative
-- C0,alpha,beta and alpha<1, the following proof-relevant packages are
-- interconvertible:
--
--   exists M<T with C0<=M and beta<=(1-alpha)M;
--
--   C0<T and beta<(1-alpha)T.
--
-- The reverse direction uses the explicit division-free minimum-slack
-- construction from Round 49. M is not an independent PDE parameter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Closure.NSTriadKNHHBadStrictTargetInterpolationRound49Exact as Interp

record AdmissibleCeilingBelowTarget : Set where
  field
    base alpha beta target ceiling : ℚ
    baseNonnegative : 0ℚ ≤ base
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ
    ceilingNonnegative : 0ℚ ≤ ceiling
    ceilingStrict : ceiling < target
    baseBelowCeiling : base ≤ ceiling
    forcingFitsCeiling : beta ≤ (1ℚ - alpha) * ceiling

open AdmissibleCeilingBelowTarget public

gapPositiveFromAlphaStrict : ∀ a → a < 1ℚ → 0ℚ < 1ℚ - a
gapPositiveFromAlphaStrict a aStrict =
  let
    shifted = ℚP.+-monoʳ-< (- a) aStrict
    leftMeaning : a + (- a) ≡ 0ℚ
    leftMeaning = solve (a ∷ [])
    rightMeaning : 1ℚ + (- a) ≡ 1ℚ - a
    rightMeaning = solve (a ∷ [])
  in subst₂ _<_ leftMeaning rightMeaning shifted

admissibleCeilingGivesStrictTargets :
  AdmissibleCeilingBelowTarget → Interp.StrictHHBadTarget
admissibleCeilingGivesStrictTargets witness = record
  { base = base witness
  ; alpha = alpha witness
  ; beta = beta witness
  ; target = target witness
  ; baseNonnegative = baseNonnegative witness
  ; alphaNonnegative = alphaNonnegative witness
  ; betaNonnegative = betaNonnegative witness
  ; alphaStrict = alphaStrict witness
  ; baseStrict = ℚP.≤-<-trans (baseBelowCeiling witness) (ceilingStrict witness)
  ; forcingStrict = forcingStrictTarget
  }
  where
  gap = 1ℚ - alpha witness

  scaledCeilingStrict :
    gap * ceiling witness < gap * target witness
  scaledCeilingStrict =
    let instance gapPosI = positive
          (gapPositiveFromAlphaStrict (alpha witness) (alphaStrict witness))
    in ℚP.*-monoʳ-<-pos gap (ceilingStrict witness)

  forcingStrictTarget :
    beta witness < (1ℚ - alpha witness) * target witness
  forcingStrictTarget =
    ℚP.≤-<-trans (forcingFitsCeiling witness) scaledCeilingStrict

strictTargetsGiveAdmissibleCeiling :
  Interp.StrictHHBadTarget → AdmissibleCeilingBelowTarget
strictTargetsGiveAdmissibleCeiling data = record
  { base = Interp.base data
  ; alpha = Interp.alpha data
  ; beta = Interp.beta data
  ; target = Interp.target data
  ; ceiling = Interp.derivedCeiling data
  ; baseNonnegative = Interp.baseNonnegative data
  ; alphaNonnegative = Interp.alphaNonnegative data
  ; betaNonnegative = Interp.betaNonnegative data
  ; alphaStrict = Interp.alphaStrict data
  ; ceilingNonnegative = Interp.derivedCeilingNonnegative data
  ; ceilingStrict = Interp.derivedCeilingStrict data
  ; baseBelowCeiling = Interp.baseBelowDerivedCeiling data
  ; forcingFitsCeiling = Interp.forcingBelowDerivedCeiling data
  }

ceilingExistenceEliminatedByStrictTargets : Bool
ceilingExistenceEliminatedByStrictTargets = true

ceilingExistenceEliminatedByStrictTargetsIsTrue :
  ceilingExistenceEliminatedByStrictTargets ≡ true
ceilingExistenceEliminatedByStrictTargetsIsTrue = refl

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
-- Close the numerical quantifier elimination exactly.  For nonnegative
-- C0,alpha,beta and alpha<1, the following two proof-relevant packages are
-- interconvertible:
--
--   exists M<T with C0<=M and beta<=(1-alpha)M;
--
--   C0<T and beta<(1-alpha)T.
--
-- The forward direction is monotonicity.  The reverse direction uses the
-- explicit division-free minimum-slack construction from Round 49.  Thus M is
-- not an independent PDE parameter and need not appear in the physical gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP

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
  strictDataForGap : Interp.StrictHHBadTarget
  strictDataForGap = record
    { base = base witness
    ; alpha = alpha witness
    ; beta = beta witness
    ; target = target witness
    ; baseNonnegative = baseNonnegative witness
    ; alphaNonnegative = alphaNonnegative witness
    ; betaNonnegative = betaNonnegative witness
    ; alphaStrict = alphaStrict witness
    ; baseStrict = ℚP.≤-<-trans (baseBelowCeiling witness) (ceilingStrict witness)
    ; forcingStrict = forcingPlaceholder
    }
    where
    forcingPlaceholder : beta witness < (1ℚ - alpha witness) * target witness
    forcingPlaceholder =
      let
        gap = 1ℚ - alpha witness
        gapPositive : 0ℚ < gap
        gapPositive =
          let open import Agda.Builtin.List using ([]; _∷_)
              open import Data.Rational.Tactic.RingSolver using (solve)
              open import Relation.Binary.PropositionalEquality using (subst₂)
          in
          subst₂ _<_
            (solve (alpha witness ∷ []))
            (solve (alpha witness ∷ []))
            (ℚP.+-monoʳ-< (- alpha witness) (alphaStrict witness))

        scaled : gap * ceiling witness < gap * target witness
        scaled =
          let instance gapPosI = positive gapPositive
          in ℚP.*-monoʳ-<-pos gap (ceilingStrict witness)
      in
      ℚP.≤-<-trans (forcingFitsCeiling witness) scaled

  forcingStrictTarget : beta witness < (1ℚ - alpha witness) * target witness
  forcingStrictTarget = Interp.forcingStrict strictDataForGap

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

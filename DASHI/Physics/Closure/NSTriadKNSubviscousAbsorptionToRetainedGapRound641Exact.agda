{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSubviscousAbsorptionToRetainedGapRound641Exact where

------------------------------------------------------------------------
-- ROUND641 / OPTIONAL SUBVISCOUS ABSORPTION -> POSITIVE RETAINED GAP
--
-- R639 fixes the physical viscous coefficient in the R414 slice to 2*nu and
-- keeps the genuinely necessary receipt
--
--   0 < 2*nu - a.
--
-- This owner records one sufficient (NOT mandatory) way to discharge it:
--
--   0 < nu   and   a <= nu
--   ----------------------
--        0 < 2*nu - a.
--
-- The canonical C2 theorem is NOT strengthened to require a <= nu.  A direct
-- proof of the retained gap may bypass this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; _+_; _*_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCriticalSliceRound639Exact as R639

subviscousAbsorptionGivesRetainedGap :
  ∀ {nu absorbed : ℚ} →
  Positive nu →
  absorbed ≤ nu →
  0ℚ < Fold.two * nu - absorbed
subviscousAbsorptionGivesRetainedGap {nu} {absorbed}
    nuPositive absorbedBelowNu =
  let
    nuStrict : 0ℚ < nu
    nuStrict = ℚP.positive⁻¹ nu

    addBound :
      nu + absorbed ≤ nu + nu
    addBound =
      ℚP.+-mono-≤ ℚP.≤-refl absorbedBelowNu

    shifted :
      (nu + absorbed) + (- absorbed)
      ≤ (nu + nu) + (- absorbed)
    shifted =
      ℚP.+-mono-≤ addBound ℚP.≤-refl

    normalized :
      nu ≤ Fold.two * nu - absorbed
    normalized =
      subst
        (λ left → left ≤ Fold.two * nu - absorbed)
        (solve (nu ∷ absorbed ∷ []))
        (subst
          (λ right → (nu + absorbed) + (- absorbed) ≤ right)
          (solve (nu ∷ absorbed ∷ []))
          shifted)
  in
  ℚP.<-≤-trans nuStrict normalized

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round641SubviscousAbsorptionCompilerClosed : Bool
round641SubviscousAbsorptionCompilerClosed = true

round641SubviscousAbsorptionMandatory : Bool
round641SubviscousAbsorptionMandatory = false

round641DirectRetainedGapProofMayBypassCompiler : Bool
round641DirectRetainedGapProofMayBypassCompiler = true

round641IntroducesNewNSEstimate : Bool
round641IntroducesNewNSEstimate = false

round641PositiveRetainedViscosityUnconditionallyClosed : Bool
round641PositiveRetainedViscosityUnconditionallyClosed = false

round641ClayPromotion : Bool
round641ClayPromotion = false

round641SubviscousAbsorptionCompilerClosedIsTrue :
  round641SubviscousAbsorptionCompilerClosed ≡ true
round641SubviscousAbsorptionCompilerClosedIsTrue = refl

round641SubviscousAbsorptionMandatoryIsFalse :
  round641SubviscousAbsorptionMandatory ≡ false
round641SubviscousAbsorptionMandatoryIsFalse = refl

round641DirectRetainedGapProofMayBypassCompilerIsTrue :
  round641DirectRetainedGapProofMayBypassCompiler ≡ true
round641DirectRetainedGapProofMayBypassCompilerIsTrue = refl

round641IntroducesNewNSEstimateIsFalse :
  round641IntroducesNewNSEstimate ≡ false
round641IntroducesNewNSEstimateIsFalse = refl

round641PositiveRetainedViscosityUnconditionallyClosedIsFalse :
  round641PositiveRetainedViscosityUnconditionallyClosed ≡ false
round641PositiveRetainedViscosityUnconditionallyClosedIsFalse = refl

round641ClayPromotionIsFalse :
  round641ClayPromotion ≡ false
round641ClayPromotionIsFalse = refl

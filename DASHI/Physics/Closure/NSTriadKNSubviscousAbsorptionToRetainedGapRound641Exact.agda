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
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy

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
-- Same-object adapter into the actual R639 retained-viscosity receipt.
------------------------------------------------------------------------

module TypedReceipt
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.Complex3
        DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField) →
      (Time → DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.Complex3
        DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Physical = R639.PhysicalSlice
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  subviscousBuildsTypedRetainedViscosity :
    ∀ {D C R cutoff terminal}
      (P : Physical.PhysicalCriticalSliceData D C R cutoff terminal) →
    Physical.absorbedCoefficient P
      ≤ Live.physicalViscosity (Live.support D) →
    Physical.PositiveRetainedViscosityReceipt P
  subviscousBuildsTypedRetainedViscosity {D} {R = R} P absorbedBelowNu =
    record
      { Physical.retainedViscosityPositive =
          subviscousAbsorptionGivesRetainedGap
            (Support.physicalViscosityPositive R)
            absorbedBelowNu
      }

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round641SubviscousAbsorptionCompilerClosed : Bool
round641SubviscousAbsorptionCompilerClosed = true

round641TypedR639RetainedViscosityAdapterClosed : Bool
round641TypedR639RetainedViscosityAdapterClosed = true

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

round641TypedR639RetainedViscosityAdapterClosedIsTrue :
  round641TypedR639RetainedViscosityAdapterClosed ≡ true
round641TypedR639RetainedViscosityAdapterClosedIsTrue = refl

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

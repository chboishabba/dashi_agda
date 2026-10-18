{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact where

------------------------------------------------------------------------
-- ROUND645 / STRICT-MARGIN C2 NORMAL FORM -> R639 SLICE + C5 GAP
--
-- R639 leaves the absorbed coefficient a as analytic data and separately asks
-- for the retained-viscosity receipt
--
--   0 < 2*nu - a.
--
-- For proof search it is often cleaner to state the nonlinear theorem directly
-- with a positive retained margin delta:
--
--   P_N(T)
--     <= (2*nu - delta_N) D_N(T)
--        + integral_0^T R406_N(t) dt,
--
--   0 < delta_N.
--
-- This file proves that such a theorem simultaneously:
--
--   * constructs the literal R639 PhysicalCriticalSliceData with
--       absorbedCoefficient = 2*nu - delta_N;
--   * constructs its PositiveRetainedViscosityReceipt;
--   * identifies the retained gap definitionally/algebraically with delta_N.
--
-- Hence C5 need not remain an independent mathematical theorem when C2 is
-- proved in strict-margin form.  No Navier--Stokes estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCriticalSliceRound639Exact as R639
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414

F : C3.RealField _
F = Rational.rationalRealField

retainedGapExactlyMargin :
  (nu margin : ℚ) →
  (Fold.two * nu) - ((Fold.two * nu) - margin) ≡ margin
retainedGapExactlyMargin nu margin = solve (nu ∷ margin ∷ [])

module StrictMargin
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
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
  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo DerivativeOf
  module Physical = R639.PhysicalSlice
    Time initialTime integrateTo DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record StrictMarginPhysicalProductionData
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      strictMarginProductionEstimate :
        Obs.integratedCriticalProduction
            (Live.literalPhysicalTrajectory D) cutoff terminal
        ≤
          ( (Fold.two * Live.physicalViscosity (Live.support D))
              - retainedMargin)
            * Obs.integratedCriticalDissipation
                (Live.literalPhysicalTrajectory D) cutoff terminal
          + Unified.literalRemainderIntegral
              (Live.literalPhysicalTrajectory D) R cutoff terminal

  open StrictMarginPhysicalProductionData public

  toPhysicalCriticalSliceData :
    ∀ {D C R cutoff terminal} →
    StrictMarginPhysicalProductionData D C R cutoff terminal →
    Physical.PhysicalCriticalSliceData D C R cutoff terminal
  toPhysicalCriticalSliceData {D} P = record
    { Physical.absorbedCoefficient =
        (Fold.two * Live.physicalViscosity (Live.support D))
          - retainedMargin P
    ; Physical.phaseSensitiveProductionEstimate =
        strictMarginProductionEstimate P
    }

  strictMarginBuildsPositiveRetainedViscosity :
    ∀ {D C R cutoff terminal}
      (P : StrictMarginPhysicalProductionData D C R cutoff terminal) →
    Physical.PositiveRetainedViscosityReceipt
      (toPhysicalCriticalSliceData P)
  strictMarginBuildsPositiveRetainedViscosity {D} P = record
    { Physical.retainedViscosityPositive =
        subst
          (λ gap → 0ℚ < gap)
          (sym
            (retainedGapExactlyMargin
              (Live.physicalViscosity (Live.support D))
              (retainedMargin P)))
          (retainedMarginPositive P)
    }

  retainedGapOfCompiledSliceExactlyMargin :
    ∀ {D C R cutoff terminal}
      (P : StrictMarginPhysicalProductionData D C R cutoff terminal) →
    (Fold.two * Live.physicalViscosity (Live.support D))
      - Physical.absorbedCoefficient (toPhysicalCriticalSliceData P)
    ≡ retainedMargin P
  retainedGapOfCompiledSliceExactlyMargin {D} P =
    retainedGapExactlyMargin
      (Live.physicalViscosity (Live.support D))
      (retainedMargin P)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round645StrictMarginC2NormalFormTyped : Bool
round645StrictMarginC2NormalFormTyped = true

round645StrictMarginCompilesToLiteralR639Slice : Bool
round645StrictMarginCompilesToLiteralR639Slice = true

round645StrictMarginSimultaneouslyPaysC5 : Bool
round645StrictMarginSimultaneouslyPaysC5 = true

round645C5IndependentWhenC2ProvedWithPositiveMargin : Bool
round645C5IndependentWhenC2ProvedWithPositiveMargin = false

round645SubviscousAAtMostNuRequired : Bool
round645SubviscousAAtMostNuRequired = false

round645IntroducesNewNSEstimate : Bool
round645IntroducesNewNSEstimate = false

round645ClayPromotion : Bool
round645ClayPromotion = false

round645StrictMarginC2NormalFormTypedIsTrue :
  round645StrictMarginC2NormalFormTyped ≡ true
round645StrictMarginC2NormalFormTypedIsTrue = refl

round645StrictMarginCompilesToLiteralR639SliceIsTrue :
  round645StrictMarginCompilesToLiteralR639Slice ≡ true
round645StrictMarginCompilesToLiteralR639SliceIsTrue = refl

round645StrictMarginSimultaneouslyPaysC5IsTrue :
  round645StrictMarginSimultaneouslyPaysC5 ≡ true
round645StrictMarginSimultaneouslyPaysC5IsTrue = refl

round645C5IndependentWhenC2ProvedWithPositiveMarginIsFalse :
  round645C5IndependentWhenC2ProvedWithPositiveMargin ≡ false
round645C5IndependentWhenC2ProvedWithPositiveMarginIsFalse = refl

round645SubviscousAAtMostNuRequiredIsFalse :
  round645SubviscousAAtMostNuRequired ≡ false
round645SubviscousAAtMostNuRequiredIsFalse = refl

round645IntroducesNewNSEstimateIsFalse :
  round645IntroducesNewNSEstimate ≡ false
round645IntroducesNewNSEstimateIsFalse = refl

round645ClayPromotionIsFalse :
  round645ClayPromotion ≡ false
round645ClayPromotionIsFalse = refl

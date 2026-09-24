{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLivePhysicalPacketStrictSurplusRound648Exact where

------------------------------------------------------------------------
-- ROUND648 / LIVE R646 SURPLUS -> PHYSICAL R98 UPPER-SHELL PACKET SURPLUS
--
-- R647 closes the finite conservative radial-transfer -> physical upper-shell
-- layer-cake bridge.  This owner transports that theorem onto the literal R408
-- trajectory using the already-owned fixed canonical mode list.
--
-- The only structural receipts required at each time are the standard physical
-- facts needed by the existing R39/R98 cancellation machinery:
--
--   reality, divergence-free, and unweighted nonlinear-energy conservation
--   on the canonical nonzero cutoff carrier.
--
-- No quantitative packet/R406 inequality is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNR104GlobalLayerCakePhysicalPacketWeldExact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Canonical
import DASHI.Physics.Closure.NSTriadKNRadialConservationToPhysicalLayerCakeRound647Exact as R647
import DASHI.Physics.Closure.NSTriadKNLiteralStrictMarginRadialSurplusRound646Exact as R646
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact as R645

F : C3.RealField _
F = Rational.rationalRealField

module LivePacketSurplus
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
  module Radial = R646.RadialSurplus
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Strict = R645.StrictMargin
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  systemAt :
    (D : Live.LiteralRHSTrajectoryData) →
    Nat → Time →
    Audit.FiniteComplex3GalerkinSystem F
      (Live.Base.E (Live.stateTrajectory (Live.support D)))
      (Live.Base.I (Live.stateTrajectory (Live.support D)))
  systemAt D cutoff time =
    Live.Base.systemAt (Live.stateTrajectory (Live.support D)) cutoff time

  record LivePhysicalPacketStructure
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat) : Set₁ where
    field
      realityAt :
        (time : Time) →
        Reality.RealityCondition (Audit.velocity (systemAt D cutoff time))

      divergenceFreeAt :
        (time : Time) →
        Reality.DivergenceFreeCondition
          (Live.Base.E (Live.stateTrajectory (Live.support D)))
          (Audit.velocity (systemAt D cutoff time))

      canonicalNonlinearConservationAt :
        (time : Time) →
        Canonical.rawProjectedPairing
          (systemAt D cutoff time)
          (R34.nonzeroCutoffModes cutoff)
        ≡ 0ℚ

  open LivePhysicalPacketStructure public

  physicalPacketLayerCakeRate :
    Live.LiteralRHSTrajectoryData → Nat → Time → ℚ
  physicalPacketLayerCakeRate D cutoff time =
    Packet.physicalUpperShellLayerCake
      (systemAt D cutoff time)
      (Packet.canonicalSortedModes (systemAt D cutoff time))

  radialTransferIsPhysicalPacketRate :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier
      (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    LivePhysicalPacketStructure D C cutoff →
    (time : Time) →
    Fold.two *
      DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact.weightedTransfer
        (DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact.radialBandTransfers
          (systemAt D cutoff time)
          (Audit.modes (systemAt D cutoff time)))
    ≡ Fold.two * physicalPacketLayerCakeRate D cutoff time
  radialTransferIsPhysicalPacketRate D C cutoff S time
    rewrite Modes.retainedModesExact C cutoff time =
    cong (Fold.two *_)
      (R647.canonicalRadialWeightedTransferIsPhysicalUpperShellLayerCake
        (systemAt D cutoff time)
        (realityAt S time)
        (divergenceFreeAt S time)
        (canonicalNonlinearConservationAt S time))

  physicalPacketStrictSurplusRate :
    Live.LiteralRHSTrajectoryData →
    Nat → ℚ → Time → ℚ
  physicalPacketStrictSurplusRate D cutoff margin time =
    Fold.two * physicalPacketLayerCakeRate D cutoff time
      - ((Fold.two * Live.physicalViscosity (Live.support D)) - margin)
          * Obs.dissipationRateAt
              (Live.literalPhysicalTrajectory D) cutoff time

  radialStrictSurplusIsPhysicalPacketStrictSurplus :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier
      (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    (S : LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    Radial.strictRadialSurplusRate D cutoff margin time
    ≡ physicalPacketStrictSurplusRate D cutoff margin time
  radialStrictSurplusIsPhysicalPacketStrictSurplus D C cutoff S margin time
    rewrite radialTransferIsPhysicalPacketRate D C cutoff S time = refl

  integratedPhysicalPacketStrictSurplus :
    Live.LiteralRHSTrajectoryData →
    Nat → ℚ → Time → ℚ
  integratedPhysicalPacketStrictSurplus D cutoff margin terminal =
    integrateTo (physicalPacketStrictSurplusRate D cutoff margin) terminal

  integratedRadialSurplusIsPhysicalPacketSurplus :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier
      (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    (S : LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (terminal : Time) →
    Radial.integratedRadialSurplus D cutoff margin terminal
    ≡ integratedPhysicalPacketStrictSurplus D cutoff margin terminal
  integratedRadialSurplusIsPhysicalPacketSurplus
      D C cutoff S margin terminal =
    Energy.integrationCongruent integrationLinearity
      (radialStrictSurplusIsPhysicalPacketStrictSurplus
        D C cutoff S margin)
      terminal

  record PhysicalPacketSurplusPayment
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure : LivePhysicalPacketStructure D C cutoff

      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      physicalPacketSurplusPaidByLiteralR406 :
        integratedPhysicalPacketStrictSurplus
          D cutoff retainedMargin terminal
        ≤ Unified.literalRemainderIntegral
            (Live.literalPhysicalTrajectory D) R cutoff terminal

  open PhysicalPacketSurplusPayment public

  physicalPacketPaymentBuildsRadialPayment :
    ∀ {D C R cutoff terminal} →
    PhysicalPacketSurplusPayment D C R cutoff terminal →
    Radial.RadialSurplusPayment D C R cutoff terminal
  physicalPacketPaymentBuildsRadialPayment
      {D} {C} {R} {cutoff} {terminal} P =
    record
      { Radial.retainedMargin = retainedMargin P
      ; Radial.retainedMarginPositive = retainedMarginPositive P
      ; Radial.radialSurplusPaidByLiteralR406 =
          transportBound
      }
    where
    margin = retainedMargin P
    remainder =
      Unified.literalRemainderIntegral
        (Live.literalPhysicalTrajectory D) R cutoff terminal

    transportBound :
      Radial.integratedRadialSurplus D cutoff margin terminal ≤ remainder
    transportBound =
      subst
        (λ value → value ≤ remainder)
        (sym
          (integratedRadialSurplusIsPhysicalPacketSurplus
            D C cutoff (structure P) margin terminal))
        (physicalPacketSurplusPaidByLiteralR406 P)

  physicalPacketPaymentBuildsStrictMarginC2 :
    ∀ {D C R cutoff terminal} →
    PhysicalPacketSurplusPayment D C R cutoff terminal →
    Strict.StrictMarginPhysicalProductionData D C R cutoff terminal
  physicalPacketPaymentBuildsStrictMarginC2 P =
    Radial.radialSurplusPaymentBuildsStrictMarginC2
      (physicalPacketPaymentBuildsRadialPayment P)

round648LiveRadialToPhysicalPacketSurplusCompilerClosed : Bool
round648LiveRadialToPhysicalPacketSurplusCompilerClosed = true

round648PhysicalPacketPaymentCompilesToStrictMarginC2 : Bool
round648PhysicalPacketPaymentCompilesToStrictMarginC2 = true

round648RemainingQuantitativeLeafIsPacketSurplusR406 : Bool
round648RemainingQuantitativeLeafIsPacketSurplusR406 = true

round648IntroducesNewEstimate : Bool
round648IntroducesNewEstimate = false

round648ClayPromotion : Bool
round648ClayPromotion = false

round648LiveRadialToPhysicalPacketSurplusCompilerClosedIsTrue :
  round648LiveRadialToPhysicalPacketSurplusCompilerClosed ≡ true
round648LiveRadialToPhysicalPacketSurplusCompilerClosedIsTrue = refl

round648PhysicalPacketPaymentCompilesToStrictMarginC2IsTrue :
  round648PhysicalPacketPaymentCompilesToStrictMarginC2 ≡ true
round648PhysicalPacketPaymentCompilesToStrictMarginC2IsTrue = refl

round648RemainingQuantitativeLeafIsPacketSurplusR406IsTrue :
  round648RemainingQuantitativeLeafIsPacketSurplusR406 ≡ true
round648RemainingQuantitativeLeafIsPacketSurplusR406IsTrue = refl

round648IntroducesNewEstimateIsFalse :
  round648IntroducesNewEstimate ≡ false
round648IntroducesNewEstimateIsFalse = refl

round648ClayPromotionIsFalse :
  round648ClayPromotion ≡ false
round648ClayPromotionIsFalse = refl

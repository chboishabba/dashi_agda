{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedC1C2CriticalBarrierRound727Exact where

------------------------------------------------------------------------
-- ROUND727 / CURRENT PERIODIC MAX-CUT ENDGAME
--
-- Consume exactly the current live ingredients:
--
--   C1a  R723 cutoff-uniform combined/global-commutator payment,
--   C1b  R726 transport of literal R406 below that combined payment,
--   C2   R645 strict-margin phase-sensitive production on every cutoff,
--   C4   standard cutoff-uniform initial-critical realization.
--
-- R645/R639 already turn C2 into the SAME R414 literal critical slice and make
-- the retained viscosity gap equal to the positive C2 margin.
-- R726 turns C1a+C1b into the existing R410 cancellation object.
-- R414 then constructs the uniform signed critical family and barrier.
--
-- No R568 forcing-square identification is used.  No separate self/external
-- payment reappears.  This owner is a compiler only: it leaves C1a, C1b and C2
-- visibly proof-bearing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCriticalSliceRound639Exact as R639
import DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact as R645
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNInitialCriticalRealizationToR421Round512Exact as R512
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact as R726

F : C3.RealField _
F = Rational.rationalRealField

module Endgame
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module Strict = R645.StrictMargin
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module Physical = R639.PhysicalSlice
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Bridge = R726.CombinedToR406
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Unified = R414.Unified
    Time initialTime integrateTo VectorDerivativeOf

  module Initial = R512.InitialCritical
    Time initialTime integrateTo VectorDerivativeOf

  T = Live.literalPhysicalTrajectory D

  c2Slice :
    (terminal : Time) →
    ((cutoff : Nat) →
      Strict.StrictMarginPhysicalProductionData
        D C R cutoff terminal) →
    (cutoff : Nat) →
    Unified.CriticalSliceOnLiteralR406 T R terminal cutoff
  c2Slice terminal P cutoff =
    Physical.canonicalPhysicalCriticalSlice
      (Strict.toPhysicalCriticalSliceData (P cutoff))

  record CombinedC1C2Inputs (terminal : Time) : Set₁ where
    field
      combinedPayment :
        Combined.CutoffUniformCombinedSelfExternalPayment

      combinedToR406 :
        Bridge.CombinedR406Transport R

      strictMarginC2 :
        (cutoff : Nat) →
        Strict.StrictMarginPhysicalProductionData
          D C R cutoff terminal

      initialCritical :
        Initial.InitialCriticalRealization
          T R terminal (c2Slice terminal strictMarginC2)

  open CombinedC1C2Inputs public

  r410Cancellation :
    (terminal : Time) →
    CombinedC1C2Inputs terminal →
    Unified.Cancel.SignedCriticalCancellation T R
  r410Cancellation terminal I =
    Bridge.combinedPaymentAndR406TransportBuildCancellation
      R (combinedPayment I) (combinedToR406 I)

  unifiedCriticalData :
    (terminal : Time) →
    (I : CombinedC1C2Inputs terminal) →
    Unified.UnifiedCancellationCriticalData T R terminal
  unifiedCriticalData terminal I = record
    { Unified.cancellation = r410Cancellation terminal I
    ; Unified.sliceData = c2Slice terminal (strictMarginC2 I)
    ; Unified.uniformInitialCeiling =
        Initial.cutoffIndependentInitialCeiling (initialCritical I)
    ; Unified.uniformInitialCritical =
        Initial.realizationPaysUniformInitialCritical (initialCritical I)
    }

  uniformCriticalFamily :
    (terminal : Time) →
    CombinedC1C2Inputs terminal →
    Signed.UniformSignedCriticalProductionFamily
  uniformCriticalFamily terminal I =
    Unified.toUniformSignedCriticalProductionFamily
      (unifiedCriticalData terminal I)

  uniformCriticalBarrier :
    (terminal : Time) →
    (I : CombinedC1C2Inputs terminal) →
    (cutoff : Nat) →
    let family = uniformCriticalFamily terminal I
    in
    Signed.terminalCritical (Signed.slice family cutoff)
      + Signed.retainedViscosity (Signed.slice family cutoff)
          * Signed.criticalDissipation (Signed.slice family cutoff)
    ≤ Signed.uniformCriticalCeiling family
  uniformCriticalBarrier terminal I cutoff =
    Unified.oneCancellationBuildsUniformCriticalBarrier
      (unifiedCriticalData terminal I) cutoff

  c2RetainedMarginPositive :
    (terminal : Time) →
    (I : CombinedC1C2Inputs terminal) →
    (cutoff : Nat) →
    0ℚ <
      Unified.viscousCoefficient
        (c2Slice terminal (strictMarginC2 I) cutoff)
      -
      Unified.absorbedCoefficient
        (c2Slice terminal (strictMarginC2 I) cutoff)
  c2RetainedMarginPositive terminal I cutoff =
    let
      P = strictMarginC2 I cutoff
      compiled = Strict.toPhysicalCriticalSliceData P
      receipt = Strict.strictMarginBuildsPositiveRetainedViscosity P
    in
    Physical.PositiveRetainedViscosityReceipt.retainedViscosityPositive
      receipt

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round727R723R726BuildExistingR410Cancellation : Bool
round727R723R726BuildExistingR410Cancellation = true

round727C2BuildsExactR414CriticalSlice : Bool
round727C2BuildsExactR414CriticalSlice = true

round727C2PositiveMarginIsRetainedViscosityGap : Bool
round727C2PositiveMarginIsRetainedViscosityGap = true

round727CombinedC1C2PlusInitialSourceBuildUniformCriticalBarrier : Bool
round727CombinedC1C2PlusInitialSourceBuildUniformCriticalBarrier = true

round727SeparateSelfPaymentReintroduced : Bool
round727SeparateSelfPaymentReintroduced = false

round727SeparateExternalPaymentReintroduced : Bool
round727SeparateExternalPaymentReintroduced = false

round727CombinedPaymentClosed : Bool
round727CombinedPaymentClosed = R723.round723CombinedCutoffUniformPaymentClosed

round727CombinedToR406TransportClosed : Bool
round727CombinedToR406TransportClosed = R726.round726CombinedToR406TransportClosed

round727C2StrictMarginPaymentClosed : Bool
round727C2StrictMarginPaymentClosed = false

round727IntroducesEstimate : Bool
round727IntroducesEstimate = false

round727ClayPromotion : Bool
round727ClayPromotion = false

round727R723R726BuildExistingR410CancellationIsTrue :
  round727R723R726BuildExistingR410Cancellation ≡ true
round727R723R726BuildExistingR410CancellationIsTrue = refl

round727C2BuildsExactR414CriticalSliceIsTrue :
  round727C2BuildsExactR414CriticalSlice ≡ true
round727C2BuildsExactR414CriticalSliceIsTrue = refl

round727C2PositiveMarginIsRetainedViscosityGapIsTrue :
  round727C2PositiveMarginIsRetainedViscosityGap ≡ true
round727C2PositiveMarginIsRetainedViscosityGapIsTrue = refl

round727CombinedC1C2PlusInitialSourceBuildUniformCriticalBarrierIsTrue :
  round727CombinedC1C2PlusInitialSourceBuildUniformCriticalBarrier ≡ true
round727CombinedC1C2PlusInitialSourceBuildUniformCriticalBarrierIsTrue = refl

round727SeparateSelfPaymentReintroducedIsFalse :
  round727SeparateSelfPaymentReintroduced ≡ false
round727SeparateSelfPaymentReintroducedIsFalse = refl

round727SeparateExternalPaymentReintroducedIsFalse :
  round727SeparateExternalPaymentReintroduced ≡ false
round727SeparateExternalPaymentReintroducedIsFalse = refl

round727IntroducesEstimateIsFalse :
  round727IntroducesEstimate ≡ false
round727IntroducesEstimateIsFalse = refl

round727ClayPromotionIsFalse :
  round727ClayPromotion ≡ false
round727ClayPromotionIsFalse = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedPaymentToWeightedWorkRound724Exact where

------------------------------------------------------------------------
-- ROUND724 / R723 COMBINED RESIDUE + STANDARD INITIAL CEILING -> R699
--            GLOBAL WEIGHTED WORK PAYMENT
--
-- R723 constructs an R691 global-commutator payment directly from ONE
-- cutoff-uniform spacetime bound on the exact combined self+external residue.
-- R699 proves that the only additional upper-bound datum needed to control the
-- global weighted/input-Laplacian side is a cutoff-uniform INITIAL mixed-mass
-- ceiling; the terminal mixed mass has favorable nonnegative sign.
--
-- Compose those two exact interfaces:
--
--   CombinedSelfExternalPayment
--     + InitialMixedMassCeiling
--       -> R691 GlobalCommutatorPayment
--       -> R699 GlobalWeightedPayment.
--
-- This confirms that no separate self, external, helicity-channel, or terminal
-- nonlinear estimate survives downstream.  The initial ceiling remains a
-- standard-data receipt, not a new nonlinear PDE theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723

F : C3.RealField _
F = Rational.rationalRealField

module CombinedToWeighted
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → Data.Rational.Base.ℚ) → Time → Data.Rational.Base.ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → Data.Rational.Base.ℚ) →
      (Time → Data.Rational.Base.ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  combinedAndInitialCeilingBuildGlobalWeightedPayment :
    Combined.CutoffUniformCombinedSelfExternalPayment →
    Upper.CutoffUniformInitialMixedMassCeiling →
    Upper.CutoffUniformGlobalWeightedPayment
  combinedAndInitialCeilingBuildGlobalWeightedPayment C I =
    Upper.commutatorAndInitialCeilingBuildGlobalWeightedPayment
      (Combined.combinedPaymentBuildsR691GlobalCommutatorPayment C)
      I

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round724CombinedPaymentFeedsR699WeightedWork : Bool
round724CombinedPaymentFeedsR699WeightedWork = true

round724SeparateSelfPaymentSurvivesDownstream : Bool
round724SeparateSelfPaymentSurvivesDownstream = false

round724SeparateExternalPaymentSurvivesDownstream : Bool
round724SeparateExternalPaymentSurvivesDownstream = false

round724TerminalMixedMassNeedsIndependentUpperEstimate : Bool
round724TerminalMixedMassNeedsIndependentUpperEstimate = false

round724InitialMixedMassIsNewNonlinearPDEEstimate : Bool
round724InitialMixedMassIsNewNonlinearPDEEstimate =
  R699.round699InitialMixedMassCeilingIsNewNonlinearPDEEstimate

round724CombinedCutoffUniformPaymentClosed : Bool
round724CombinedCutoffUniformPaymentClosed =
  R723.round723CombinedCutoffUniformPaymentClosed

round724IntroducesEstimate : Bool
round724IntroducesEstimate = false

round724ClayPromotion : Bool
round724ClayPromotion = false

round724CombinedPaymentFeedsR699WeightedWorkIsTrue :
  round724CombinedPaymentFeedsR699WeightedWork ≡ true
round724CombinedPaymentFeedsR699WeightedWorkIsTrue = refl

round724SeparateSelfPaymentSurvivesDownstreamIsFalse :
  round724SeparateSelfPaymentSurvivesDownstream ≡ false
round724SeparateSelfPaymentSurvivesDownstreamIsFalse = refl

round724SeparateExternalPaymentSurvivesDownstreamIsFalse :
  round724SeparateExternalPaymentSurvivesDownstream ≡ false
round724SeparateExternalPaymentSurvivesDownstreamIsFalse = refl

round724TerminalMixedMassNeedsIndependentUpperEstimateIsFalse :
  round724TerminalMixedMassNeedsIndependentUpperEstimate ≡ false
round724TerminalMixedMassNeedsIndependentUpperEstimateIsFalse = refl

round724InitialMixedMassIsNewNonlinearPDEEstimateIsFalse :
  round724InitialMixedMassIsNewNonlinearPDEEstimate ≡ false
round724InitialMixedMassIsNewNonlinearPDEEstimateIsFalse =
  R699.round699InitialMixedMassCeilingIsNewNonlinearPDEEstimateIsFalse

round724CombinedCutoffUniformPaymentClosedIsFalse :
  round724CombinedCutoffUniformPaymentClosed ≡ false
round724CombinedCutoffUniformPaymentClosedIsFalse =
  R723.round723CombinedCutoffUniformPaymentClosedIsFalse

round724IntroducesEstimateIsFalse :
  round724IntroducesEstimate ≡ false
round724IntroducesEstimateIsFalse = refl

round724ClayPromotionIsFalse :
  round724ClayPromotion ≡ false
round724ClayPromotionIsFalse = refl

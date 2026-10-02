{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ReserveDecisionRound831Exact where

------------------------------------------------------------------------
-- R831 / NEGATIVE SELECTED COMPLETE RATE REFUTES THE R823 RESERVE
--
-- R823 proves on the SAME live packet
--
--   integratedCompleteRate = integratedReserve - integratedDemand
--
-- and that Demand <= Reserve implies 0 <= integratedCompleteRate.
--
-- Therefore any strict negative evaluation of that selected complete rate
-- immediately refutes the universal reserve inequality on that packet.
-- This file closes that logical implication.  It does not manufacture the
-- R829 same-object snapshot evaluation or the R830 real finite-ODE lift.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

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
import DASHI.Physics.Closure.NSTriadKNR650SignedComparableReserveRound823Exact as R823

F : C3.RealField _
F = Rational.rationalRealField

module ReserveDecision
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

  module Live =
    R823.SignedComparableReserve
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  negativeCompleteRateRefutesReserve :
    (cutoff : Nat) →
    (S : Live.Packet.LivePhysicalPacketStructure D C cutoff) →
    (terminal : Time) →
    Live.integratedCompleteRate cutoff S terminal < 0ℚ →
    ¬ (Live.integratedDemand cutoff S terminal
      ≤ Live.integratedReserve cutoff S terminal)
  negativeCompleteRateRefutesReserve cutoff S terminal negative reserve = 
    ℚP.<⇒≱ negative
      (Live.integratedReservePaysCompleteSignedRate
        cutoff S terminal reserve)


round831NegativeSelectedIntegralRefutesReserve : Bool
round831NegativeSelectedIntegralRefutesReserve = true

round831NoAdditionalEstimateRequiredAfterNegativeIntegral : Bool
round831NoAdditionalEstimateRequiredAfterNegativeIntegral = true

round831R829SnapshotEvaluationClosedHere : Bool
round831R829SnapshotEvaluationClosedHere = false

round831R830RealODEClosedHere : Bool
round831R830RealODEClosedHere = false

round831ClayPromotion : Bool
round831ClayPromotion = false

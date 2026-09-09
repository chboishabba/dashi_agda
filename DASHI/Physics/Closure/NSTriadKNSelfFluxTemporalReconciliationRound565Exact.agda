module DASHI.Physics.Closure.NSTriadKNSelfFluxTemporalReconciliationRound565Exact where

------------------------------------------------------------------------
-- ROUND565 / CANONICAL RECONCILIATION OF THE TWO SELF-FLUX TEMPORAL LANES
--
-- Two compatible Round564 owners now coexist:
--
--   * LiveGlobalSelfFluxDerivativeRound564Exact constructs the literal GLOBAL
--     derivative relation by finite aggregation of the exact per-output R563
--     self-flux derivatives.
--
--   * SelfFluxScalarFTCBoundaryRound564Exact isolates the ordinary scalar FTC
--     schema and correctly refuses to derive it from R393, whose endpoint FTC
--     is itself a required field.
--
-- These are not competing authorities.  The first owns the NS-specific
-- derivative construction; the second owns the remaining scalar-analysis
-- interface.  This module composes them directly on the SAME global observable.
-- No third derivative semantics, alternate flux, or replacement integration
-- functional is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact as Global564
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module Reconcile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  module Global = Global564.LiveGlobalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff

  globalSelfFluxDerivative565 :
    ScalarDerivativeOf Global.globalSelfFlux Global.globalSelfFluxTangent
  globalSelfFluxDerivative565 = Global.literalGlobalSelfFluxDerivative

  globalSelfFluxEndpointFTC565 :
    FTC564.ScalarFundamentalTheorem564
      Time initialTime integrateTo ScalarDerivativeOf →
    (terminal : Time) →
    integrateTo Global.globalSelfFluxTangent terminal
    ≡ Global.globalSelfFlux terminal - Global.globalSelfFlux initialTime
  globalSelfFluxEndpointFTC565 FTC terminal =
    FTC564.scalarEndpointFTC564 FTC globalSelfFluxDerivative565 terminal

------------------------------------------------------------------------
-- Dependency status.
------------------------------------------------------------------------

data R565Residual : Set where
  missingConcreteScalarFTCInhabitant565 : R565Residual
  missingFactoredCommutatorSpacetimeBound565 : R565Residual
  literalLeafAClosed565 : R565Residual

currentR565Residual : R565Residual
currentR565Residual = missingConcreteScalarFTCInhabitant565

round565NSDerivativeConstructionClosed : Bool
round565NSDerivativeConstructionClosed = true

round565GlobalFiniteAggregationClosed : Bool
round565GlobalFiniteAggregationClosed = true

round565R393UsedAsFTCProducer : Bool
round565R393UsedAsFTCProducer = false

round565ConcreteScalarFTCInhabitantInstalled : Bool
round565ConcreteScalarFTCInhabitantInstalled = false

round565ConcurrentTemporalOwnersReconciled : Bool
round565ConcurrentTemporalOwnersReconciled = true

round565FactoredCommutatorSpacetimeBoundClosed : Bool
round565FactoredCommutatorSpacetimeBoundClosed = false

round565CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round565CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round565ClayPromotion : Bool
round565ClayPromotion = false

round565NSDerivativeConstructionClosedIsTrue :
  round565NSDerivativeConstructionClosed ≡ true
round565NSDerivativeConstructionClosedIsTrue = refl

round565ConcurrentTemporalOwnersReconciledIsTrue :
  round565ConcurrentTemporalOwnersReconciled ≡ true
round565ConcurrentTemporalOwnersReconciledIsTrue = refl

round565R393UsedAsFTCProducerIsFalse :
  round565R393UsedAsFTCProducer ≡ false
round565R393UsedAsFTCProducerIsFalse = refl

round565ClayPromotionIsFalse : round565ClayPromotion ≡ false
round565ClayPromotionIsFalse = refl

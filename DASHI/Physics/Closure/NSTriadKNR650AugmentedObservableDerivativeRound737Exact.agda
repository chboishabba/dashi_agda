{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650AugmentedObservableDerivativeRound737Exact where

------------------------------------------------------------------------
-- ROUND737 / LITERAL DERIVATIVE OF A_N = X_N - 12 Q_{+-,N}
--
-- This owner differentiates the preferred augmented observable on the literal
-- R408 trajectory.  No FTC or estimate is used in the derivative theorem.
--
-- Existing authorities:
--   * S1b: dX_N/dt = literal critical-energy tangent;
--   * Endpoint: d selfEnergy_k/dt = coherent tangent work_k;
--   * R733: the global selfEnergy endpoint is exactly canonical Q_+-.
--
-- Hence
--
--   d/dt [X_N - 12 Q_+-]
--     = Xdot_N - 12 Qdot_+-,
--
-- with Qdot_+- the complete nonzero-output coherent tangent fold.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
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
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyPointwiseExact as Pointwise
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact as R734

F : C3.RealField _
F = Rational.rationalRealField

module AugmentedDerivative
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

  module Aug = R734.AugmentedWeighted
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Critical = Energy.LiteralCriticalEnergyCalculus
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module End = Upper.Balance.Local.End
  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  T = Aug.T

  outputEnergyCurves :
    Nat → List Z3.FourierMode → List (Time → ℚ)
  outputEnergyCurves cutoff [] = []
  outputEnergyCurves cutoff (output ∷ rest) =
    End.selfEnergy cutoff output
      ∷ outputEnergyCurves cutoff rest

  outputTangentCurves :
    Nat → List Z3.FourierMode → List (Time → ℚ)
  outputTangentCurves cutoff [] = []
  outputTangentCurves cutoff (output ∷ rest) =
    End.coherentTangentWork cutoff output
      ∷ outputTangentCurves cutoff rest

  allOutputEnergyDerivatives :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    R412.AllDerivatives ScalarDerivativeOf
      (outputEnergyCurves cutoff outputs)
      (outputTangentCurves cutoff outputs)
  allOutputEnergyDerivatives cutoff [] =
    R412.derivativesNil
  allOutputEnergyDerivatives cutoff (output ∷ rest) =
    R412.derivativesCons
      (End.selfEnergyDerivative cutoff output)
      (allOutputEnergyDerivatives cutoff rest)

  sumOutputEnergyMeaning :
    (cutoff : Nat) (outputs : List Z3.FourierMode) (time : Time) →
    R412.sumCurves (outputEnergyCurves cutoff outputs) time
    ≡ Upper.sumSelfEnergy cutoff time outputs
  sumOutputEnergyMeaning cutoff [] time = refl
  sumOutputEnergyMeaning cutoff (output ∷ rest) time =
    cong
      (End.selfEnergy cutoff output time +_)
      (sumOutputEnergyMeaning cutoff rest time)

  globalQPlusMinusTangent :
    Nat → Time → ℚ
  globalQPlusMinusTangent cutoff time =
    R412.sumCurves
      (outputTangentCurves cutoff (Canonical.nonzeroCutoffModes cutoff))
      time

  globalQPlusMinusDerivative :
    (cutoff : Nat) →
    ScalarDerivativeOf
      (Upper.globalSelfEnergy cutoff)
      (globalQPlusMinusTangent cutoff)
  globalQPlusMinusDerivative cutoff =
    R412.transportDerivative scalarDerivativeAlgebra
      (sumOutputEnergyMeaning
        cutoff (Canonical.nonzeroCutoffModes cutoff))
      (λ _ → refl)
      (R412.finiteSumDerivative scalarDerivativeAlgebra
        (allOutputEnergyDerivatives
          cutoff (Canonical.nonzeroCutoffModes cutoff)))

  criticalEnergyTangent :
    Nat → Time → ℚ
  criticalEnergyTangent cutoff time =
    Pointwise.finiteLiteralEnergyTangent
      (Live.physicalSystemAt (Live.support D) cutoff time)
      (Audit.modes
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff time))

  augmentedTangent :
    Nat → Time → ℚ
  augmentedTangent cutoff time =
    criticalEnergyTangent cutoff time
      - R700.twelve * globalQPlusMinusTangent cutoff time

  augmentedCriticalEnergyDerivative :
    (cutoff : Nat) →
    ScalarDerivativeOf
      (Aug.augmentedCriticalEnergy cutoff)
      (augmentedTangent cutoff)
  augmentedCriticalEnergyDerivative cutoff =
    let
      dX =
        Critical.liveCriticalEnergyDerivative D C cutoff

      dQ =
        globalQPlusMinusDerivative cutoff

      dMinusTwelveQ =
        R416.constantScaleDerivative constantScaleCalculus
          (- R700.twelve) dQ

      raw =
        R412.addDerivative scalarDerivativeAlgebra
          dX dMinusTwelveQ

      curveMeaning :
        (time : Time) →
        Aug.Obs.criticalEnergyAt T cutoff time
          + (- R700.twelve) * Upper.globalSelfEnergy cutoff time
        ≡ Aug.augmentedCriticalEnergy cutoff time
      curveMeaning time =
        solve
          ( Aug.Obs.criticalEnergyAt T cutoff time
          ∷ Upper.globalSelfEnergy cutoff time
          ∷ R700.twelve
          ∷ [])

      tangentMeaning :
        (time : Time) →
        criticalEnergyTangent cutoff time
          + (- R700.twelve) * globalQPlusMinusTangent cutoff time
        ≡ augmentedTangent cutoff time
      tangentMeaning time =
        solve
          ( criticalEnergyTangent cutoff time
          ∷ globalQPlusMinusTangent cutoff time
          ∷ R700.twelve
          ∷ [])
    in
    R412.transportDerivative scalarDerivativeAlgebra
      curveMeaning tangentMeaning raw

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round737GlobalQPlusMinusDerivativeClosed : Bool
round737GlobalQPlusMinusDerivativeClosed = true

round737LiteralAugmentedObservableDerivativeClosed : Bool
round737LiteralAugmentedObservableDerivativeClosed = true

round737UsesLiteralR408Trajectory : Bool
round737UsesLiteralR408Trajectory = true

round737IntroducesEstimate : Bool
round737IntroducesEstimate = false

round737W2Closed : Bool
round737W2Closed = false

round737ClayPromotion : Bool
round737ClayPromotion = false

round737GlobalQPlusMinusDerivativeClosedIsTrue :
  round737GlobalQPlusMinusDerivativeClosed ≡ true
round737GlobalQPlusMinusDerivativeClosedIsTrue = refl

round737LiteralAugmentedObservableDerivativeClosedIsTrue :
  round737LiteralAugmentedObservableDerivativeClosed ≡ true
round737LiteralAugmentedObservableDerivativeClosedIsTrue = refl

round737UsesLiteralR408TrajectoryIsTrue :
  round737UsesLiteralR408Trajectory ≡ true
round737UsesLiteralR408TrajectoryIsTrue = refl

round737IntroducesEstimateIsFalse :
  round737IntroducesEstimate ≡ false
round737IntroducesEstimateIsFalse = refl

round737W2ClosedIsFalse :
  round737W2Closed ≡ false
round737W2ClosedIsFalse = refl

round737ClayPromotionIsFalse :
  round737ClayPromotion ≡ false
round737ClayPromotionIsFalse = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteDefocusingSolutionWitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Rational.Base using (1ℚ; -[1+_])

import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Closure.DiscreteWarpedEinsteinMatterModel as Model
import DASHI.Physics.Closure.EinsteinEquationBidiResidualExact as Einstein
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.GRQFTNegativeActiveStressRepulsionRouteExact as Active
import DASHI.Physics.Foundations.GRQFTTimelikeDefocusingCompilerExact as Defocus

------------------------------------------------------------------------
-- SAME-OBJECT FINITE DEFOCUSING SOLUTION WITNESS
--
-- This bundles facts that were previously spread across independent modules:
--
--   * nonconstant warped Lorentzian geometry;
--   * positive normalized Hubble/log-scale gradient on both time edges;
--   * H-dot = 0 and positive curvature from H^2;
--   * action-derived rho > 0 and p = -rho on all three principal axes;
--   * exact normalized Einstein residual zero at kappa = +1;
--   * negative active stress rho + px + py + pz = -2;
--   * trace-reversed timelike Ricci contraction R_uu = -1;
--   * positive Raychaudhuri curvature contribution -R_uu = +1.
--
-- The critical point is same-object composition: this is not a negative-G
-- construction.  The finite Einstein residual selects the positive normalized
-- coupling while the source tension drives the defocusing sign.
------------------------------------------------------------------------

record FiniteDefocusingSolutionWitness : Set where
  constructor finite-defocusing-solution-witness
  field
    positiveExpansionPastToPresent :
      Geometry.hubbleCoefficient Geometry.pastToPresent
        ≡ Geometry.positiveUnit

    positiveExpansionPresentToFuture :
      Geometry.hubbleCoefficient Geometry.presentToFuture
        ≡ Geometry.positiveUnit

    expansionGradientConstant :
      Geometry.hubbleDerivative ≡ Geometry.zeroUnit

    curvaturePositive :
      Geometry.warpedSectionalCurvature
        ≡ Geometry.positiveCurvature

    energyDensityPositive :
      Model.warpedEnergyDensity ≡ Model.positiveSource

    pressureNegative :
      Model.warpedPressure ≡ Model.negativeSource

    equationOfStateCancellation :
      Model.rhoPlusPressure ≡ Model.zeroSource

    normalizedPositiveCouplingSelected :
      Einstein.normalizedEightPiGCoupling ≡ Geometry.positiveUnit

    normalizedEinsteinEquationPasses :
      Einstein.runEinsteinEquationAttempt Einstein.normalizedEightPiGCoupling
        ≡ Einstein.exactResidualZero

    zeroCouplingRejected :
      Einstein.runEinsteinEquationAttempt Geometry.zeroUnit
        ≡ Einstein.nonzeroResidualCounterexample

    negativeCouplingRejected :
      Einstein.runEinsteinEquationAttempt Geometry.negativeUnit
        ≡ Einstein.nonzeroResidualCounterexample

    activeStressNegative :
      Active.finiteGRActiveStressSum
        ≡ -[1+ suc zero ]

    timelikeRicciNegative :
      Defocus.ricci00TraceReversed
        Cut.finiteGRStressRational
        ≡ Defocus.minusOne

    raychaudhuriCurvatureTermPositive :
      Defocus.raychaudhuriCurvatureContribution
        (Defocus.ricci00TraceReversed
          Cut.finiteGRStressRational)
        ≡ 1ℚ

open FiniteDefocusingSolutionWitness public

canonicalFiniteDefocusingSolutionWitness :
  FiniteDefocusingSolutionWitness
canonicalFiniteDefocusingSolutionWitness =
  finite-defocusing-solution-witness
    Geometry.pastHubblePositive
    Geometry.futureHubblePositive
    Geometry.constantHubbleReceipt
    Geometry.computedPositiveCurvature
    Model.computedEnergyNonzero
    Model.computedPressureNegative
    Model.computedEquationOfStateCancellation
    refl
    Einstein.normalizedEquationAttemptPasses
    Einstein.zeroCouplingAttemptFails
    Einstein.negativeCouplingAttemptFails
    Active.finiteGRActiveStressSumIsNegativeTwo
    Defocus.finiteGRRicci00IsNegativeOne
    Defocus.finiteGRCurvatureContributionIsPositiveOne

------------------------------------------------------------------------
-- Mechanism conclusion inside the finite normalized model.
------------------------------------------------------------------------

data FiniteRepulsionMechanism : Set where
  positiveGCouplingWithNegativePressureTension :
    FiniteRepulsionMechanism

finiteModelMechanism :
  FiniteRepulsionMechanism
finiteModelMechanism =
  positiveGCouplingWithNegativePressureTension

record FiniteDefocusingSolutionBoundary : Set where
  constructor finite-defocusing-solution-boundary
  field
    finiteGeometryIsNonconstant : Bool
    positiveNormalizedCouplingPassesEinsteinResidual : Bool
    negativeNormalizedCouplingPassesEinsteinResidual : Bool
    sourceHasPositiveEnergyAndNegativePressure : Bool
    sourceProducesNegativeActiveStress : Bool
    timelikeRicciIsNegative : Bool
    raychaudhuriCurvatureContributionIsPositive : Bool
    finiteModelNeedsNegativeG : Bool
    finiteModelNeedsNegativeInertialMass : Bool
    finiteWitnessIsContinuumGlobalRepulsiveSpacetime : Bool
    completeRiemannGeodesicDeviationStillNeededForTrajectoryTheorem : Bool

canonicalFiniteDefocusingSolutionBoundary :
  FiniteDefocusingSolutionBoundary
canonicalFiniteDefocusingSolutionBoundary =
  finite-defocusing-solution-boundary
    true true false true true true true false false false true

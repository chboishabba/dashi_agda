module DASHI.Physics.ThreeBody.Bridge where

open import DASHI.Physics.ThreeBody.State
open import DASHI.Physics.ThreeBody.Step
open import DASHI.Physics.ThreeBody.Regime
open import DASHI.Physics.ThreeBody.Energy
open import DASHI.Physics.ThreeBody.Wave
open import DASHI.Physics.ThreeBody.PredictiveBoundary
open import DASHI.Physics.ThreeBody.Interference

------------------------------------------------------------------------
-- Theorem-thin package for the three-body test case.
--
-- Intended reading:
-- - no global contraction claim
-- - local energy/action surface
-- - explicit regime split:
--   contractive / cone-boundary / non-contracting
-- - wave-facing admissible path kernel

record ThreeBodyBoundaryDynamics
  (Coord : Set)
  (Scalar : Set)
  (Energy : Set)
  (Phase : Set)
  : Set₁ where
  field
    State : Set
    stateCarrier : ThreeBodyState Coord Scalar → State
    stepSurface : ThreeBodyStep State
    regimeClassifier : ThreeBodyRegimeClassifier State
    energyAction : ThreeBodyEnergyAction State Energy
    predictionSurface :
      ThreeBodyPredictiveBoundaryLayer State Energy Phase

    admissiblePathCarrier : Set
    admissiblePathSurface :
      admissiblePathCarrier → ThreeBodyAdmissiblePath State

    waveKernel :
      ThreeBodyWaveKernel State Energy Phase
    interferenceSurface :
      ThreeBodyInterferenceLayer
        State
        Energy
        Phase

    localContractiveWitness :
      (p : admissiblePathCarrier) →
      ThreeBodyRegimeClassifier.inContractiveRegion
        regimeClassifier
        (ThreeBodyAdmissiblePath.path
          (admissiblePathSurface p)
          0)

    coneBoundaryWitness :
      (p : admissiblePathCarrier) →
      ThreeBodyRegimeClassifier.onConeBoundary
        regimeClassifier
        (ThreeBodyAdmissiblePath.path
          (admissiblePathSurface p)
          0)

    nonGlobalContraction :
      Set

open ThreeBodyBoundaryDynamics public

record ThreeBodyTheoremLadder
  (State : Set)
  : Set₁ where
  field
    localEnergyDefined : Set
    localActionDefined : Set
    deltaStateDefined : Set
    localPredictiveHorizonDefined : Set
    chaosBoundaryDefined : Set
    regimeClassificationDefined : Set
    admissiblePathKernelDefined : Set
    interferenceSurfaceDefined : Set
    boundaryGeneratedBranchingDefined : Set
    waveCoefficientIdentity : Set
    positivityImpliesAdmissiblePath : Set
    majorMinorArcCriterion : Set

open ThreeBodyTheoremLadder public

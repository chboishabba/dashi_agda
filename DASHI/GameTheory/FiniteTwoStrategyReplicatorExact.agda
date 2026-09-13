module DASHI.GameTheory.FiniteTwoStrategyReplicatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)

import DASHI.GameTheory.GameTheorySourceAtlasExact as Sources

------------------------------------------------------------------------
-- FINITE TWO-STRATEGY REPLICATOR REWEIGHTING
--
-- Discrete reproductive reweighting is represented without division:
--
--   x' * fbar = x * f_R
--   y' * fbar = y * f_M
--
-- where fbar = x*f_R + y*f_M.  The positive-total condition is explicit, and
-- both before/after frequency vectors are normalized.  This is a finite exact
-- dynamics carrier, not a continuum ODE theorem or calibrated population model.
------------------------------------------------------------------------

record TwoStrategyFrequency : Set where
  constructor two-strategy-frequency
  field
    residentFrequency mutantFrequency : ℚ

    residentNonnegative : 0ℚ ≤ residentFrequency
    mutantNonnegative : 0ℚ ≤ mutantFrequency

    normalized : residentFrequency + mutantFrequency ≡ 1ℚ

open TwoStrategyFrequency public

record TwoStrategyFitness : Set where
  constructor two-strategy-fitness
  field
    residentFitness mutantFitness : ℚ
    residentFitnessNonnegative : 0ℚ ≤ residentFitness
    mutantFitnessNonnegative : 0ℚ ≤ mutantFitness

open TwoStrategyFitness public

weightedResident : TwoStrategyFrequency → TwoStrategyFitness → ℚ
weightedResident frequency fitness =
  residentFrequency frequency * residentFitness fitness

weightedMutant : TwoStrategyFrequency → TwoStrategyFitness → ℚ
weightedMutant frequency fitness =
  mutantFrequency frequency * mutantFitness fitness

meanFitness : TwoStrategyFrequency → TwoStrategyFitness → ℚ
meanFitness frequency fitness =
  weightedResident frequency fitness
  + weightedMutant frequency fitness

record ReplicatorReweightingStep
    (before : TwoStrategyFrequency)
    (fitness : TwoStrategyFitness) : Set where
  constructor replicator-reweighting-step
  field
    after : TwoStrategyFrequency

    positiveMeanFitness : 0ℚ < meanFitness before fitness

    residentReweights :
      residentFrequency after * meanFitness before fitness
      ≡ weightedResident before fitness

    mutantReweights :
      mutantFrequency after * meanFitness before fitness
      ≡ weightedMutant before fitness

    dynamicsReference : String
    sourceReference : String

open ReplicatorReweightingStep public

------------------------------------------------------------------------
-- A trajectory remains explicit and append-only at the game-dynamics level.
------------------------------------------------------------------------

record ReplicatorTrajectory : Set₁ where
  constructor replicator-trajectory
  field
    Generation : Set
    Later : Generation → Generation → Set

    frequencyAt : Generation → TwoStrategyFrequency
    fitnessAt : Generation → TwoStrategyFitness

    stepTo : Generation → Generation
    stepLater : (generation : Generation) → Later generation (stepTo generation)

    reweighting :
      (generation : Generation) →
      ReplicatorReweightingStep
        (frequencyAt generation)
        (fitnessAt generation)

    nextFrequencyMatches :
      (generation : Generation) →
      after (reweighting generation)
      ≡ frequencyAt (stepTo generation)

    trajectoryReference : String

open ReplicatorTrajectory public

------------------------------------------------------------------------
-- Attribution compatibility.
------------------------------------------------------------------------

sourceAtlasBoundary : Sources.canonicalGameTheorySourceCount ≡ 8
sourceAtlasBoundary = Sources.canonicalGameTheorySourceCountIsEight

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReplicatorStepMeansESSPermission : Set where

data ESSMeansReplicatorConvergencePermission : Set where

data ReplicatorConvergenceMeansFixationPermission : Set where

data PositiveFitnessMeansMoralValuePermission : Set where

data FiniteReplicatorMeansContinuumODEPermission : Set where

data OneTrajectoryMeansHistoricalUniversalityPermission : Set where

replicatorStepDoesNotCreateESS : ReplicatorStepMeansESSPermission → ⊥
replicatorStepDoesNotCreateESS ()

essDoesNotAutomaticallyGiveReplicatorConvergence :
  ESSMeansReplicatorConvergencePermission → ⊥
essDoesNotAutomaticallyGiveReplicatorConvergence ()

replicatorConvergenceDoesNotAutomaticallyGiveFixation :
  ReplicatorConvergenceMeansFixationPermission → ⊥
replicatorConvergenceDoesNotAutomaticallyGiveFixation ()

positiveFitnessDoesNotCreateMoralValue : PositiveFitnessMeansMoralValuePermission → ⊥
positiveFitnessDoesNotCreateMoralValue ()

finiteReweightingDoesNotClaimContinuumReplicatorODE :
  FiniteReplicatorMeansContinuumODEPermission → ⊥
finiteReweightingDoesNotClaimContinuumReplicatorODE ()

oneTrajectoryDoesNotBecomeUniversalHistory :
  OneTrajectoryMeansHistoricalUniversalityPermission → ⊥
oneTrajectoryDoesNotBecomeUniversalHistory ()

record FiniteReplicatorBoundary : Set where
  constructor finite-replicator-boundary
  field
    normalizedBeforeExplicit : Bool
    normalizedAfterExplicit : Bool
    positiveMeanFitnessExplicit : Bool
    crossMultipliedReweightingExact : Bool
    trajectoryExplicit : Bool
    continuumODEClaimed : Bool
    fixationAutomatic : Bool

canonicalFiniteReplicatorBoundary : FiniteReplicatorBoundary
canonicalFiniteReplicatorBoundary =
  finite-replicator-boundary true true true true true false false

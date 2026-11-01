module DASHI.Physics.Closure.NSOpenAI2026ReleasedCorrectionStepExact where

------------------------------------------------------------------------
-- NATIVE PORT: RELEASED ACTUAL CORRECTION-STEP DECOMPOSITION
--
-- Source owners:
--   NavierStokes/CorrectionStep.lean
--   NavierStokes/CycleStateCoherence.lean
--   NavierStokes/ActualCycleParameters.lean
--
-- The released step is not atomic.  It is the ordered composition
--
--   particular -> signed -> temporal mean -> rank mean -> pressure-alias refresh
--
-- with the next state retaining the source carrier and base error.  This file
-- ports that proof shape and compiles it into the native selected-cycle
-- bookkeeping kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedCycleBookkeepingExact
  as Cycle

------------------------------------------------------------------------
-- 1. Literal stage decomposition on one native bookkeeping state.
------------------------------------------------------------------------

record ReleasedCorrectionStepStages
    {P : Cycle.ReleasedCyclePayloadSurface}
    (before : Cycle.ReleasedCycleState P) : Set₁ where
  field
    afterParticular : Cycle.ReleasedCycleState P
    afterSigned : Cycle.ReleasedCycleState P
    afterTemporal : Cycle.ReleasedCycleState P
    afterRank : Cycle.ReleasedCycleState P

    particularRetainsLabels :
      Cycle.labels afterParticular ≡ Cycle.labels before
    signedRetainsLabels :
      Cycle.labels afterSigned ≡ Cycle.labels afterParticular
    temporalRetainsLabels :
      Cycle.labels afterTemporal ≡ Cycle.labels afterSigned
    rankRetainsLabels :
      Cycle.labels afterRank ≡ Cycle.labels afterTemporal

    particularRetainsCarrier :
      Cycle.carrier afterParticular ≡ Cycle.carrier before
    signedRetainsCarrier :
      Cycle.carrier afterSigned ≡ Cycle.carrier afterParticular
    temporalRetainsCarrier :
      Cycle.carrier afterTemporal ≡ Cycle.carrier afterSigned
    rankRetainsCarrier :
      Cycle.carrier afterRank ≡ Cycle.carrier afterTemporal

    particularRetainsRepresentation :
      Cycle.representation afterParticular ≡ Cycle.representation before
    signedRetainsRepresentation :
      Cycle.representation afterSigned ≡ Cycle.representation afterParticular
    temporalRetainsRepresentation :
      Cycle.representation afterTemporal ≡ Cycle.representation afterSigned
    rankRetainsRepresentation :
      Cycle.representation afterRank ≡ Cycle.representation afterTemporal

    particularRetainsBaseError :
      Cycle.baseError afterParticular ≡ Cycle.baseError before
    signedRetainsBaseError :
      Cycle.baseError afterSigned ≡ Cycle.baseError afterParticular
    temporalRetainsBaseError :
      Cycle.baseError afterTemporal ≡ Cycle.baseError afterSigned
    rankRetainsBaseError :
      Cycle.baseError afterRank ≡ Cycle.baseError afterTemporal

    temporalAlias : Cycle.AliasTerm P
    pressureAlias : Cycle.AliasTerm P

open ReleasedCorrectionStepStages public

------------------------------------------------------------------------
-- 2. Transitive source laws.
------------------------------------------------------------------------

stepLabelsPreserved :
  ∀ {P} {before : Cycle.ReleasedCycleState P} →
  (S : ReleasedCorrectionStepStages before) →
  Cycle.labels (afterRank S) ≡ Cycle.labels before
stepLabelsPreserved S
  rewrite rankRetainsLabels S
  | temporalRetainsLabels S
  | signedRetainsLabels S
  | particularRetainsLabels S = refl

stepCarrierPreserved :
  ∀ {P} {before : Cycle.ReleasedCycleState P} →
  (S : ReleasedCorrectionStepStages before) →
  Cycle.carrier (afterRank S) ≡ Cycle.carrier before
stepCarrierPreserved S
  rewrite rankRetainsCarrier S
  | temporalRetainsCarrier S
  | signedRetainsCarrier S
  | particularRetainsCarrier S = refl

stepRepresentationPreserved :
  ∀ {P} {before : Cycle.ReleasedCycleState P} →
  (S : ReleasedCorrectionStepStages before) →
  Cycle.representation (afterRank S) ≡ Cycle.representation before
stepRepresentationPreserved S
  rewrite rankRetainsRepresentation S
  | temporalRetainsRepresentation S
  | signedRetainsRepresentation S
  | particularRetainsRepresentation S = refl

stepBaseErrorPreserved :
  ∀ {P} {before : Cycle.ReleasedCycleState P} →
  (S : ReleasedCorrectionStepStages before) →
  Cycle.baseError (afterRank S) ≡ Cycle.baseError before
stepBaseErrorPreserved S
  rewrite rankRetainsBaseError S
  | temporalRetainsBaseError S
  | signedRetainsBaseError S
  | particularRetainsBaseError S = refl

------------------------------------------------------------------------
-- 3. A source-faithful correction-step producer.
--
-- The actual analytic port must construct the four stage states and their
-- coherence laws.  The compiler below then produces the exact one-step
-- evidence consumed by the native selected recurrence.
------------------------------------------------------------------------

record ReleasedCorrectionStepProducer
    (P : Cycle.ReleasedCyclePayloadSurface) : Set₁ where
  field
    stages :
      (before : Cycle.ReleasedCycleState P) →
      ReleasedCorrectionStepStages before

open ReleasedCorrectionStepProducer public

compileCorrectionStepEvidence :
  ∀ {P} →
  ReleasedCorrectionStepProducer P →
  (before : Cycle.ReleasedCycleState P) →
  Cycle.ReleasedCycleStepEvidence before
compileCorrectionStepEvidence producer before =
  let S = stages producer before
  in record
    { Cycle.newTemporalAlias = temporalAlias S
    ; Cycle.newPressureAlias = pressureAlias S
    ; Cycle.nextLabels = Cycle.labels (afterRank S)
    ; Cycle.nextCarrier = Cycle.carrier (afterRank S)
    ; Cycle.nextRepresentation = Cycle.representation (afterRank S)
    ; Cycle.nextBaseError = Cycle.baseError (afterRank S)
    ; Cycle.labelsPreserved = stepLabelsPreserved S
    ; Cycle.carrierPreserved = stepCarrierPreserved S
    ; Cycle.representationPreserved = stepRepresentationPreserved S
    ; Cycle.baseErrorPreserved = stepBaseErrorPreserved S
    }

compileSelectedCycleKernel :
  ∀ {P} →
  Cycle.ReleasedCycleInitialPayload P →
  ReleasedCorrectionStepProducer P →
  Cycle.ReleasedSelectedCycleKernel P
compileSelectedCycleKernel initial producer = record
  { Cycle.initial = initial
  ; Cycle.stepEvidence = compileCorrectionStepEvidence producer
  }

------------------------------------------------------------------------
-- 4. Explicit analytic obligations extracted from CycleStateCoherence.
------------------------------------------------------------------------

record ReleasedCorrectionAnalyticInputs : Set₁ where
  field
    ParticularPrimitiveData : Set
    SignedPrimitiveData : Set
    TemporalPrimitiveData : Set
    RankPrimitiveData : Set

    ParticularCovarianceControl : Set
    SignedCovarianceControl : Set
    RankGeometry : Set

    particularPrimitive : ParticularPrimitiveData
    signedPrimitive : SignedPrimitiveData
    temporalPrimitive : TemporalPrimitiveData
    rankPrimitive : RankPrimitiveData

    particularCovariance : ParticularCovarianceControl
    signedCovariance : SignedCovarianceControl
    rankGeometry : RankGeometry

open ReleasedCorrectionAnalyticInputs public

record ReleasedCorrectionPhysicalInputs : Set₁ where
  field
    ParticularWaveInsertion : Set
    SignedWaveInsertion : Set
    TemporalMeanIncrement : Set
    RankMeanIncrement : Set
    PressureAliasRefresh : Set

    particularWave : ParticularWaveInsertion
    signedWave : SignedWaveInsertion
    temporalMean : TemporalMeanIncrement
    rankMean : RankMeanIncrement
    pressureAliasRefresh : PressureAliasRefresh

open ReleasedCorrectionPhysicalInputs public

correctionStepOrderPorted : Bool
correctionStepOrderPorted = true

correctionStepPreservationCompilerClosed : Bool
correctionStepPreservationCompilerClosed = true

particularAnalyticBodyPopulatedHere : Bool
particularAnalyticBodyPopulatedHere = false

signedAnalyticBodyPopulatedHere : Bool
signedAnalyticBodyPopulatedHere = false

meanAnalyticBodiesPopulatedHere : Bool
meanAnalyticBodiesPopulatedHere = false

correctionStepOrderPortedIsTrue :
  correctionStepOrderPorted ≡ true
correctionStepOrderPortedIsTrue = refl

correctionStepPreservationCompilerClosedIsTrue :
  correctionStepPreservationCompilerClosed ≡ true
correctionStepPreservationCompilerClosedIsTrue = refl

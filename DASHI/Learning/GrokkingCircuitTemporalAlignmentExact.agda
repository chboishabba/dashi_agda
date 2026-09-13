module DASHI.Learning.GrokkingCircuitTemporalAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (_+_)
open import Data.Nat using (_∸_)

import DASHI.Learning.GrokkingOperatorContract as Grok
import DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact as Circuit

------------------------------------------------------------------------
-- Run/checkpoint identity and circuit-side observations.
------------------------------------------------------------------------

record RunIdentity : Set where
  constructor runIdentity
  field
    taskKey : Nat
    seed : Nat
    configurationKey : Nat
open RunIdentity public

record GrokkingCircuitMechanismObservation : Set where
  constructor circuitObservation
  field
    observationRunIdentity : RunIdentity
    checkpointEpoch : Nat
    extractionRuleKey : Nat
    interventionRuleKey : Nat
    relationThresholdKey : Nat
    circuitSystem : Circuit.FiniteClosedCompatibleSystem
    activeSupport : Nat
    heldOutOutcomeUsedForSelection : Bool
open GrokkingCircuitMechanismObservation public

record GrokkingCircuitTrajectoryReceipt : Set where
  constructor circuitTrajectory
  field
    trajectoryRunIdentity : RunIdentity
    firstPaidBetaTransition : Grok.FirstPassage
    extractionRuleStable : Bool
    interventionRuleStable : Bool
    relationThresholdStable : Bool
    allBetaMaximalityPaid : Bool
    checkpointCadence : Nat
open GrokkingCircuitTrajectoryReceipt public

------------------------------------------------------------------------
-- Temporal classification.
------------------------------------------------------------------------

data TemporalClassification : Set where
  betaBeforeTest95 : TemporalClassification
  betaCoincidentWithTest95 : TemporalClassification
  betaAfterTest95 : TemporalClassification
  betaTransitionUnobserved : TemporalClassification
  firstPassageRightCensored : TemporalClassification
  notComparable : TemporalClassification

natLE : Nat → Nat → Bool
natLE zero _ = true
natLE (suc _) zero = false
natLE (suc a) (suc b) = natLE a b

natAbsDiff : Nat → Nat → Nat
natAbsDiff a b = (a ∸ b) + (b ∸ a)

boolAnd : Bool → Bool → Bool
boolAnd true b = b
boolAnd false _ = false

allAdmissible : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool
allAdmissible sameRun sameSplit sameHorizon frozen extractionStable interventionStable thresholdStable betaPaid =
  boolAnd sameRun
    (boolAnd sameSplit
      (boolAnd sameHorizon
        (boolAnd frozen
          (boolAnd extractionStable
            (boolAnd interventionStable
              (boolAnd thresholdStable betaPaid))))))

classifyTemporalAlignment :
  Grok.FirstPassage → Grok.FirstPassage → Nat → Bool → TemporalClassification
classifyTemporalAlignment betaPass testPass cadence admissible with admissible
... | false = notComparable
... | true with betaPass
...   | Grok.notRecorded = betaTransitionUnobserved
...   | Grok.rightCensored = betaTransitionUnobserved
...   | Grok.observedAt betaEpoch with testPass
...     | Grok.notRecorded = notComparable
...     | Grok.rightCensored = firstPassageRightCensored
...     | Grok.observedAt testEpoch with natLE (natAbsDiff betaEpoch testEpoch) cadence
...       | true = betaCoincidentWithTest95
...       | false with natLE betaEpoch testEpoch
...         | true = betaBeforeTest95
...         | false = betaAfterTest95

------------------------------------------------------------------------
-- Alignment receipt. Promotion pays admissibility of this temporal comparison
-- only; it does not pay a GrokkingMechanismWitness, contraction, MDL, or cause.
------------------------------------------------------------------------

record GrokkingTemporalAlignmentReceipt : Set where
  constructor temporalAlignmentReceipt
  field
    observation : Grok.GrokkingObservation
    trajectory : GrokkingCircuitTrajectoryReceipt
    sameRunIdentity : Bool
    sameHeldOutSplit : Bool
    sameHorizon : Bool
    selectionFrozenBeforeOutcomeComparison : Bool
    temporalClassification : TemporalClassification
    alignmentPromotionPaid : Bool
    heldOutOutcomeUsedForSelection : Bool
open GrokkingTemporalAlignmentReceipt public

makeAlignment :
  Grok.GrokkingObservation →
  GrokkingCircuitTrajectoryReceipt →
  Bool → Bool → Bool → Bool → Bool →
  GrokkingTemporalAlignmentReceipt
makeAlignment obs traj sameRun sameSplit sameHorizon frozen outcomeUsed =
  temporalAlignmentReceipt
    obs
    traj
    sameRun
    sameSplit
    sameHorizon
    frozen
    classification
    admissible
    outcomeUsed
  where
    rulesAndBeta : Bool
    rulesAndBeta =
      allAdmissible
        sameRun
        sameSplit
        sameHorizon
        frozen
        (extractionRuleStable traj)
        (interventionRuleStable traj)
        (relationThresholdStable traj)
        (allBetaMaximalityPaid traj)

    noLeakage : Bool
    noLeakage with outcomeUsed
    ... | true = false
    ... | false = true

    admissible : Bool
    admissible = boolAnd rulesAndBeta noLeakage

    classification : TemporalClassification
    classification =
      classifyTemporalAlignment
        (firstPaidBetaTransition traj)
        (Grok.test95 obs)
        (checkpointCadence traj)
        admissible

alignmentPaysGrokkingMechanismWitness : Bool
alignmentPaysGrokkingMechanismWitness = false

------------------------------------------------------------------------
-- Synthetic finite fixtures. These test the temporal carrier only and are not
-- empirical Grokking results.
------------------------------------------------------------------------

syntheticRun : RunIdentity
syntheticRun = runIdentity 97 0 600

syntheticObservationAt60 : Grok.GrokkingObservation
syntheticObservationAt60 = record
  { horizon = 100
  ; fit99 = Grok.notRecorded
  ; test95 = Grok.observedAt 60
  ; finalTrainPermille = 1000
  ; finalTestPermille = 1000
  }

syntheticRightCensoredObservation : Grok.GrokkingObservation
syntheticRightCensoredObservation = record
  { horizon = 100
  ; fit99 = Grok.notRecorded
  ; test95 = Grok.rightCensored
  ; finalTrainPermille = 1000
  ; finalTestPermille = 900
  }

trajectoryAt : Grok.FirstPassage → Bool → Bool → Bool → Bool → GrokkingCircuitTrajectoryReceipt
trajectoryAt betaPass extractionStable interventionStable thresholdStable betaPaid =
  circuitTrajectory syntheticRun betaPass extractionStable interventionStable thresholdStable betaPaid 5

syntheticBeforeReceipt : GrokkingTemporalAlignmentReceipt
syntheticBeforeReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 40) true true true true)
    true true true true false

syntheticCoincidentReceipt : GrokkingTemporalAlignmentReceipt
syntheticCoincidentReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 56) true true true true)
    true true true true false

syntheticAfterReceipt : GrokkingTemporalAlignmentReceipt
syntheticAfterReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 80) true true true true)
    true true true true false

syntheticUnobservedReceipt : GrokkingTemporalAlignmentReceipt
syntheticUnobservedReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt Grok.notRecorded true true true true)
    true true true true false

syntheticRightCensoredReceipt : GrokkingTemporalAlignmentReceipt
syntheticRightCensoredReceipt =
  makeAlignment syntheticRightCensoredObservation (trajectoryAt (Grok.observedAt 40) true true true true)
    true true true true false

syntheticMismatchedRunReceipt : GrokkingTemporalAlignmentReceipt
syntheticMismatchedRunReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 40) true true true true)
    false true true true false

syntheticRuleDriftReceipt : GrokkingTemporalAlignmentReceipt
syntheticRuleDriftReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 40) false true true true)
    true true true true false

syntheticUnpaidBetaReceipt : GrokkingTemporalAlignmentReceipt
syntheticUnpaidBetaReceipt =
  makeAlignment syntheticObservationAt60 (trajectoryAt (Grok.observedAt 40) true true true false)
    true true true true false

syntheticAlignmentIsEmpiricalGrokkingResult : Bool
syntheticAlignmentIsEmpiricalGrokkingResult = false

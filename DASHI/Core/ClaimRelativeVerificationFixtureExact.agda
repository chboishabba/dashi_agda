module DASHI.Core.ClaimRelativeVerificationFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Core.ClaimRelativeVerificationEscalationExact as Verification
import DASHI.Core.ClaimRelativeVerificationBenchmarkExact as Benchmark

------------------------------------------------------------------------
-- Tiny inhabited fixture.
--
-- This proves only that the generic interfaces compose.  It is not an
-- empirical benchmark result and supplies no authority for GAIS, LILA, IIT or
-- any external system.
------------------------------------------------------------------------

data Paid : Set where
  paid : Paid

data TinyModel : Set where
  candidateModel : TinyModel
  baselineModel : TinyModel

admissible : TinyModel → Set
admissible _ = Paid

adequate : TinyModel → Set
adequate _ = Paid

descriptionLength : TinyModel → Nat
descriptionLength candidateModel = 1
descriptionLength baselineModel = 1

refines : TinyModel → TinyModel → Set
refines _ _ = Paid

problem : MDL.ConsumerMDLProblem
problem = MDL.consumerMDLProblem
  TinyModel
  admissible
  adequate
  descriptionLength
  refines
  (λ _ → "fixture-model")
  "fixture coding convention"
  "fixture consumer"

------------------------------------------------------------------------
-- Source/specification/consumer translation.
------------------------------------------------------------------------

data Source : Set where
  sourceItem : Source

data Specification : Set where
  specificationItem : Specification

data Consumer : Set where
  consumerItem : Consumer

translation :
  Verification.SpecificationTranslationReceipt Source Specification Consumer
translation = Verification.specification-translation-receipt
  sourceItem
  specificationItem
  consumerItem
  Paid paid
  "source:fixture"
  "specification:fixture"
  "consumer:fixture"
  "translation-method:fixture"

claimCase :
  Verification.EligibleClaimCase problem Source Specification Consumer
claimCase = Verification.eligible-claim-case
  translation
  candidateModel
  (paid , paid)
  "claim-case:fixture"

weakReceipt : Verification.WeakVerificationReceipt Specification
weakReceipt = Verification.weak-verification-receipt
  specificationItem
  Verification.weakPass
  "weak-verifier:fixture"
  "weak-evidence:fixture"

frontier : Verification.FrontierAdvisoryReceipt
frontier = Verification.frontier-advisory-receipt
  "history:fixture"
  "frontier:fixture"
  true
  "advisory:fixture"
  true refl

------------------------------------------------------------------------
-- Same-object held-out surface.
------------------------------------------------------------------------

data Object : Set where
  objectItem : Object

data Intervention : Set where
  interventionItem : Intervention

data Repair : Set where
  repairItem : Repair

data Training : Set where
  trainingItem : Training

data HeldOut : Set where
  heldOutItem : HeldOut

data Prediction : Set where
  predictionItem : Prediction

heldOutProtocol : Robust.HeldOutRepair Repair Training HeldOut Prediction
heldOutProtocol = Robust.heldOutRepair
  (λ _ _ → Paid)
  (λ _ _ → predictionItem)
  Paid

heldOutEvaluation :
  Verification.SameObjectHeldOutEvaluation
    Object Intervention Repair Training HeldOut Prediction
heldOutEvaluation = Verification.same-object-held-out-evaluation
  objectItem
  interventionItem
  heldOutProtocol
  Paid paid
  Paid paid
  "same-object-held-out:fixture"

------------------------------------------------------------------------
-- Separate validator and consumer observations.
------------------------------------------------------------------------

data ValidatorObservation : Set where
  validatorObservedPass : ValidatorObservation

data ConsumerObservation : Set where
  consumerObservedSuccess : ConsumerObservation

observations :
  Verification.ValidatorConsumerObservation
    ValidatorObservation ConsumerObservation
observations = Verification.validator-consumer-observation
  validatorObservedPass
  consumerObservedSuccess
  "validator-observation:fixture"
  "consumer-observation:fixture"

evaluation :
  Verification.ClaimRelativeEvaluationPacket
    problem Source Specification Consumer
    Object Intervention Repair Training HeldOut Prediction
    ValidatorObservation ConsumerObservation
evaluation = Verification.claim-relative-evaluation-packet
  claimCase
  weakReceipt
  refl
  frontier
  heldOutEvaluation
  observations
  "evaluation-packet:fixture"

------------------------------------------------------------------------
-- Matched comparison and multi-coordinate scorecard.
------------------------------------------------------------------------

comparator : Benchmark.MatchedComparatorContract
comparator = Benchmark.matched-comparator-contract
  Paid paid
  Paid paid
  Paid paid
  Paid paid
  Paid paid
  Paid paid
  "matched-comparator:fixture"

scorecard : Benchmark.SelectiveVerificationScorecard
scorecard = Benchmark.selective-verification-scorecard
  1
  0
  0
  0
  0
  0
  0
  "runtime-cost:fixture"
  "calibration:fixture"
  "scorecard:fixture"

benchmark :
  Benchmark.ClaimRelativeVerificationBenchmark
    problem Source Specification Consumer
    Object Intervention Repair Training HeldOut Prediction
    ValidatorObservation ConsumerObservation
benchmark = Benchmark.claim-relative-verification-benchmark
  evaluation comparator scorecard "benchmark:fixture"

------------------------------------------------------------------------
-- Paired act/abstain fixture: success requires action on the should-act side
-- and abstention before the critical action on the perturbed side.
------------------------------------------------------------------------

data Environment : Set where
  environmentItem : Environment

data Task : Set where
  shouldActItem : Task
  shouldAbstainItem : Task

pairedCase : Benchmark.PairedActionAbstentionCase Environment Task
pairedCase = Benchmark.paired-action-abstention-case
  environmentItem
  shouldActItem
  shouldAbstainItem
  Paid paid
  "critical-action:fixture"
  "paired-case:fixture"

pairedResult : Benchmark.PairedActionAbstentionResult pairedCase
pairedResult = Benchmark.paired-action-abstention-result
  Benchmark.acted
  Benchmark.abstainedBeforeCriticalAction
  "paired-trace:fixture"
  "paired-outcome:fixture"

pairedResultCorrect : Benchmark.PairedCorrect pairedResult
pairedResultCorrect = refl , refl

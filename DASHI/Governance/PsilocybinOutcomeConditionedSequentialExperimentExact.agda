module DASHI.Governance.PsilocybinOutcomeConditionedSequentialExperimentExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory

------------------------------------------------------------------------
-- PSILOCYBIN OUTCOME-CONDITIONED SEQUENTIAL EXPERIMENT
--
-- Same literal interpretation carrier as the temporal evidence fibre.
-- Stage 1 asks whether there is a therapeutic signal at all.
-- Stage 2 is reached only on the positive-signal branch and separates a
-- pharmacological therapeutic contribution from expectancy/blinding.
------------------------------------------------------------------------

data AttributionCode : Set where
  noTherapeuticEffectCode
  pharmacologicalContributionCode
  expectancyContributionCode
  outsideCurrentPsilocybinFibreCode
  : AttributionCode

attributionConsumer : Trajectory.Interpretation → AttributionCode
attributionConsumer Trajectory.noPsilocybinTherapeuticEffect = noTherapeuticEffectCode
attributionConsumer Trajectory.psilocybinTherapeuticEffect = pharmacologicalContributionCode
attributionConsumer Trajectory.expectancyBlindingContribution = expectancyContributionCode
attributionConsumer _ = outsideCurrentPsilocybinFibreCode

earlyLive : Trajectory.Interpretation → Set
earlyLive = Trajectory.Compatible Trajectory.psilocybinEarlyModernTrials

------------------------------------------------------------------------
-- Stage 1: efficacy screen.
------------------------------------------------------------------------

data EfficacyObservation : Set where
  noTherapeuticSignal positiveTherapeuticSignal irrelevantEfficacySignal : EfficacyObservation

efficacyObserve : Trajectory.Interpretation → EfficacyObservation
efficacyObserve Trajectory.noPsilocybinTherapeuticEffect = noTherapeuticSignal
efficacyObserve Trajectory.psilocybinTherapeuticEffect = positiveTherapeuticSignal
efficacyObserve Trajectory.expectancyBlindingContribution = positiveTherapeuticSignal
efficacyObserve _ = irrelevantEfficacySignal

efficacyBundle : Disc.ExperimentBundle Trajectory.Interpretation
efficacyBundle = Disc.experimentBundle
  EfficacyObservation
  efficacyObserve
  2
  "stage-1 randomized therapeutic-efficacy discriminator"
  "outcome calibration distinguishes no signal from positive signal without yet attributing mechanism"

------------------------------------------------------------------------
-- Stage 2: attribution/control screen.
------------------------------------------------------------------------

data AttributionObservation : Set where
  noEffectReadout drugContributionReadout expectancyContributionReadout irrelevantAttributionReadout
  : AttributionObservation

attributionObserve : Trajectory.Interpretation → AttributionObservation
attributionObserve Trajectory.noPsilocybinTherapeuticEffect = noEffectReadout
attributionObserve Trajectory.psilocybinTherapeuticEffect = drugContributionReadout
attributionObserve Trajectory.expectancyBlindingContribution = expectancyContributionReadout
attributionObserve _ = irrelevantAttributionReadout

attributionBundle : Disc.ExperimentBundle Trajectory.Interpretation
attributionBundle = Disc.experimentBundle
  AttributionObservation
  attributionObserve
  3
  "stage-2 active-control expectancy/blinding discriminator"
  "active placebo, expectancy measurement, masking integrity and locked analysis"

------------------------------------------------------------------------
-- Local closure lemmas on the literal early psilocybin fibre.
------------------------------------------------------------------------

attributionReadoutDeterminesConsumer :
  (left right : Trajectory.Interpretation) →
  earlyLive left →
  earlyLive right →
  attributionObserve left ≡ attributionObserve right →
  attributionConsumer left ≡ attributionConsumer right
attributionReadoutDeterminesConsumer Trajectory.noPsilocybinTherapeuticEffect Trajectory.noPsilocybinTherapeuticEffect _ _ same = refl
attributionReadoutDeterminesConsumer Trajectory.noPsilocybinTherapeuticEffect Trajectory.psilocybinTherapeuticEffect _ _ ()
attributionReadoutDeterminesConsumer Trajectory.noPsilocybinTherapeuticEffect Trajectory.expectancyBlindingContribution _ _ ()
attributionReadoutDeterminesConsumer Trajectory.psilocybinTherapeuticEffect Trajectory.noPsilocybinTherapeuticEffect _ _ ()
attributionReadoutDeterminesConsumer Trajectory.psilocybinTherapeuticEffect Trajectory.psilocybinTherapeuticEffect _ _ same = refl
attributionReadoutDeterminesConsumer Trajectory.psilocybinTherapeuticEffect Trajectory.expectancyBlindingContribution _ _ ()
attributionReadoutDeterminesConsumer Trajectory.expectancyBlindingContribution Trajectory.noPsilocybinTherapeuticEffect _ _ ()
attributionReadoutDeterminesConsumer Trajectory.expectancyBlindingContribution Trajectory.psilocybinTherapeuticEffect _ _ ()
attributionReadoutDeterminesConsumer Trajectory.expectancyBlindingContribution Trajectory.expectancyBlindingContribution _ _ same = refl
attributionReadoutDeterminesConsumer Trajectory.noPsilocybinTherapeuticEffect _ _ () same
attributionReadoutDeterminesConsumer Trajectory.psilocybinTherapeuticEffect _ _ () same
attributionReadoutDeterminesConsumer Trajectory.expectancyBlindingContribution _ _ () same
attributionReadoutDeterminesConsumer _ _ () _ same

closeAfterNoSignal :
  Sequential.SequentialConsumerPlan
    attributionConsumer
    (Sequential.RefineByBundle earlyLive efficacyBundle noTherapeuticSignal)
closeAfterNoSignal = Sequential.closeConsumer closure
  where
  closure :
    (left right : Trajectory.Interpretation) →
    Sequential.RefineByBundle earlyLive efficacyBundle noTherapeuticSignal left →
    Sequential.RefineByBundle earlyLive efficacyBundle noTherapeuticSignal right →
    attributionConsumer left ≡ attributionConsumer right
  closure Trajectory.noPsilocybinTherapeuticEffect Trajectory.noPsilocybinTherapeuticEffect leftProof rightProof = refl
  closure Trajectory.noPsilocybinTherapeuticEffect Trajectory.psilocybinTherapeuticEffect leftProof (_ , ())
  closure Trajectory.noPsilocybinTherapeuticEffect Trajectory.expectancyBlindingContribution leftProof (_ , ())
  closure Trajectory.noPsilocybinTherapeuticEffect _ leftProof (() , _)
  closure Trajectory.psilocybinTherapeuticEffect _ (_ , ()) rightProof
  closure Trajectory.expectancyBlindingContribution _ (_ , ()) rightProof
  closure _ _ (() , _) rightProof

------------------------------------------------------------------------
-- Positive efficacy branch asks the attribution experiment; no-signal branch
-- terminates immediately.  An impossible irrelevant outcome creates no search
-- obligation.
------------------------------------------------------------------------

positiveBase : Trajectory.Interpretation → Set
positiveBase = Sequential.RefineByBundle earlyLive efficacyBundle positiveTherapeuticSignal

closeAfterAttribution :
  (outcome : AttributionObservation) →
  Sequential.OutcomePossible positiveBase attributionBundle outcome →
  Sequential.SequentialConsumerPlan
    attributionConsumer
    (Sequential.RefineByBundle positiveBase attributionBundle outcome)
closeAfterAttribution outcome possible = Sequential.closeConsumer closure
  where
  closure :
    (left right : Trajectory.Interpretation) →
    Sequential.RefineByBundle positiveBase attributionBundle outcome left →
    Sequential.RefineByBundle positiveBase attributionBundle outcome right →
    attributionConsumer left ≡ attributionConsumer right
  closure left right (leftBase , leftOutcome) (rightBase , rightOutcome) =
    attributionReadoutDeterminesConsumer
      left right
      (proj₁ leftBase)
      (proj₁ rightBase)
      (trans leftOutcome (sym rightOutcome))

positiveContinuation :
  Sequential.SequentialConsumerPlan attributionConsumer positiveBase
positiveContinuation = Sequential.askThen attributionBundle closeAfterAttribution

irrelevantEfficacyImpossible :
  Sequential.OutcomePossible earlyLive efficacyBundle irrelevantEfficacySignal → ⊥
irrelevantEfficacyImpossible
  (Trajectory.noPsilocybinTherapeuticEffect , _ , ())
irrelevantEfficacyImpossible
  (Trajectory.psilocybinTherapeuticEffect , _ , ())
irrelevantEfficacyImpossible
  (Trajectory.expectancyBlindingContribution , _ , ())
irrelevantEfficacyImpossible (_ , () , _)

continuationAfterEfficacy :
  (outcome : EfficacyObservation) →
  Sequential.OutcomePossible earlyLive efficacyBundle outcome →
  Sequential.SequentialConsumerPlan
    attributionConsumer
    (Sequential.RefineByBundle earlyLive efficacyBundle outcome)
continuationAfterEfficacy noTherapeuticSignal possible = closeAfterNoSignal
continuationAfterEfficacy positiveTherapeuticSignal possible = positiveContinuation
continuationAfterEfficacy irrelevantEfficacySignal possible with irrelevantEfficacyImpossible possible
... | ()

psilocybinSequentialPlan :
  Sequential.SequentialConsumerPlan attributionConsumer earlyLive
psilocybinSequentialPlan = Sequential.askThen efficacyBundle continuationAfterEfficacy

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

sequentialBoundary : Sequential.SequentialExperimentPlannerBoundary
sequentialBoundary = Sequential.canonicalSequentialExperimentPlannerBoundary

data PositiveSignalPromotesDrugMechanism : Set where

data StageOneMustAlwaysTriggerStageTwo : Set where

data SequentialClosurePromotesWorldIdentity : Set where

positiveSignalDoesNotPromoteDrugMechanism : PositiveSignalPromotesDrugMechanism → ⊥
positiveSignalDoesNotPromoteDrugMechanism ()

stageOneNeedNotAlwaysTriggerStageTwo : StageOneMustAlwaysTriggerStageTwo → ⊥
stageOneNeedNotAlwaysTriggerStageTwo ()

sequentialClosureDoesNotPromoteWorldIdentity : SequentialClosurePromotesWorldIdentity → ⊥
sequentialClosureDoesNotPromoteWorldIdentity ()

record PsilocybinOutcomeConditionedSequentialBoundary : Set where
  constructor psilocybinOutcomeConditionedSequentialBoundary
  field
    stageOneCanCloseNoEffectBranch : Bool
    stageOneCanCloseNoEffectBranchIsTrue : stageOneCanCloseNoEffectBranch ≡ true
    positiveStageOneOutcomeCanTriggerAttributionStudy : Bool
    positiveStageOneOutcomeCanTriggerAttributionStudyIsTrue :
      positiveStageOneOutcomeCanTriggerAttributionStudy ≡ true
    positiveSignalEqualsMechanismProof : Bool
    positiveSignalEqualsMechanismProofIsFalse : positiveSignalEqualsMechanismProof ≡ false
    impossibleOutcomeCreatesContinuationBurden : Bool
    impossibleOutcomeCreatesContinuationBurdenIsFalse :
      impossibleOutcomeCreatesContinuationBurden ≡ false

canonicalPsilocybinOutcomeConditionedSequentialBoundary :
  PsilocybinOutcomeConditionedSequentialBoundary
canonicalPsilocybinOutcomeConditionedSequentialBoundary =
  psilocybinOutcomeConditionedSequentialBoundary
    true refl true refl false refl false refl

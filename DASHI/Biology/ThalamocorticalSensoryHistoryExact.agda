module DASHI.Biology.ThalamocorticalSensoryHistoryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥; ¬_; _×_; _,_)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ContrastiveHistoryResidualExact as Contrast

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Yi Ning Leow; Arundhati Natesan; Alexandria Barlowe;
-- Sofie Ährlund-Richter; Tianyu (Cindy) Luo; Mehrdad Jazayeri;
-- Mriganka Sur (2026),
-- "A thalamocortical circuit encoding deviations from sensory history",
-- Science 393(6812).
-- DOI: 10.1126/science.aeg4720
-- https://doi.org/10.1126/science.aeg4720
--
-- Source-level observations used here:
--
-- * mice performed a visual motion discrimination task across consecutive
--   trials with varying motion direction/coherence;
-- * choices depended on trial-by-trial differences between consecutive cues;
-- * LP (rodent pulvinar) -> ACC axons encoded a history-referenced sensory
--   representation whose geometry scaled with the magnitude of cue deviation;
-- * optogenetic perturbation of LP -> ACC axons produced deviation-dependent
--   choice biases, supporting causal involvement of the pathway in the
--   history-dependent comparison process;
-- * ACC activity transformed the LP input toward activity predictive of final
--   choice rather than the LP pathway itself simply being identified as the
--   final decision variable;
-- * behavioral repeat/update tendencies also depended on whether the previous
--   choice was correct or incorrect.
--
-- DASHI CONTRIBUTION
--
-- The finite model below extracts only the observer/quotient logic.  It does
-- not reproduce the paper's psychophysics, calcium manifold, optogenetic
-- effect sizes, or neural dynamics.  In particular:
--
--   current cue != complete history-referenced evidence;
--   (current cue, cue contrast) != automatically complete decision state;
--   neural encoding evidence != intervention evidence.
------------------------------------------------------------------------

canonicalTitle : String
canonicalTitle = "A thalamocortical circuit encoding deviations from sensory history"

canonicalAuthors : List String
canonicalAuthors =
  "Yi Ning Leow" ∷
  "Arundhati Natesan" ∷
  "Alexandria Barlowe" ∷
  "Sofie Ährlund-Richter" ∷
  "Tianyu (Cindy) Luo" ∷
  "Mehrdad Jazayeri" ∷
  "Mriganka Sur" ∷ []

canonicalDOI : String
canonicalDOI = "10.1126/science.aeg4720"

canonicalDOIURL : String
canonicalDOIURL = "https://doi.org/10.1126/science.aeg4720"

canonicalJournal : String
canonicalJournal = "Science"

canonicalVolumeIssue : String
canonicalVolumeIssue = "393(6812)"

canonicalYear : Nat
canonicalYear = 2026

record SourceAttribution : Set where
  constructor sourceAttribution
  field
    title : String
    authors : List String
    doi : String
    doiURL : String
    journal : String
    volumeIssue : String
    year : Nat

open SourceAttribution public

canonicalSourceAttribution : SourceAttribution
canonicalSourceAttribution =
  sourceAttribution
    canonicalTitle
    canonicalAuthors
    canonicalDOI
    canonicalDOIURL
    canonicalJournal
    canonicalVolumeIssue
    canonicalYear

------------------------------------------------------------------------
-- Minimal trial carrier.
------------------------------------------------------------------------

data MotionCue : Set where
  cueLeft cueRight : MotionCue

data PreviousOutcome : Set where
  previousCorrect previousIncorrect : PreviousOutcome

record TrialState : Set where
  constructor trialState
  field
    previousCue : MotionCue
    currentCue : MotionCue
    previousOutcome : PreviousOutcome

open TrialState public

data CueDeviation : Set where
  similarToRecent changedFromRecent : CueDeviation

cueDeviation : MotionCue → MotionCue → CueDeviation
cueDeviation cueLeft cueLeft = similarToRecent
cueDeviation cueLeft cueRight = changedFromRecent
cueDeviation cueRight cueLeft = changedFromRecent
cueDeviation cueRight cueRight = similarToRecent

historyObserver : TrialState → MotionCue
historyObserver = previousCue

currentObserver : TrialState → MotionCue
currentObserver = currentCue

contrastObserver : TrialState → CueDeviation
contrastObserver =
  Contrast.ContrastiveResidual historyObserver currentObserver cueDeviation

------------------------------------------------------------------------
-- Present-only observation loses immediate sensory-history contrast.
------------------------------------------------------------------------

rightAfterRight : TrialState
rightAfterRight = trialState cueRight cueRight previousCorrect

rightAfterLeft : TrialState
rightAfterLeft = trialState cueLeft cueRight previousCorrect

sameCurrentCueWitness :
  currentObserver rightAfterRight ≡ currentObserver rightAfterLeft
sameCurrentCueWitness = refl

contrastDiffersAcrossSameCurrentCue :
  contrastObserver rightAfterRight ≡ contrastObserver rightAfterLeft → ⊥
contrastDiffersAcrossSameCurrentCue ()

currentPlusContrastStrictlyRefinesCurrent :
  Observer.StrictRefinement
    currentObserver
    (Contrast.currentAndContrastObserver
      historyObserver currentObserver cueDeviation)
currentPlusContrastStrictlyRefinesCurrent =
  Contrast.contrastiveCollisionGivesStrictRefinement
    historyObserver
    currentObserver
    cueDeviation
    rightAfterRight
    rightAfterLeft
    sameCurrentCueWitness
    contrastDiffersAcrossSameCurrentCue

contrastCannotDescendThroughCurrentCueAlone :
  ¬ Contrast.ContrastDescendsThroughCurrent
      historyObserver currentObserver cueDeviation
contrastCannotDescendThroughCurrentCueAlone descent =
  Contrast.contrastiveCollisionBlocksCurrentDescent
    sameCurrentCueWitness
    contrastDiffersAcrossSameCurrentCue
    descent

------------------------------------------------------------------------
-- Contrast is useful but is not automatically the complete behavioral state.
--
-- The source reports that similarity/change interacts with previous success:
-- after correct choices similarity favours repeating, whereas after incorrect
-- choices the tendency reverses.  The following finite policy is a schematic
-- encoding of that qualitative interaction, not a fitted behavioral model.
------------------------------------------------------------------------

data DecisionDisposition : Set where
  maintainPreviousDisposition reconsiderDisposition : DecisionDisposition

behavioralDisposition : TrialState → DecisionDisposition
behavioralDisposition (trialState previous current previousCorrect)
  with cueDeviation previous current
... | similarToRecent = maintainPreviousDisposition
... | changedFromRecent = reconsiderDisposition
behavioralDisposition (trialState previous current previousIncorrect)
  with cueDeviation previous current
... | similarToRecent = reconsiderDisposition
... | changedFromRecent = maintainPreviousDisposition

rightAfterRightIncorrect : TrialState
rightAfterRightIncorrect =
  trialState cueRight cueRight previousIncorrect

sameCurrentAcrossOutcomeWitness :
  currentObserver rightAfterRight ≡ currentObserver rightAfterRightIncorrect
sameCurrentAcrossOutcomeWitness = refl

sameContrastAcrossOutcomeWitness :
  contrastObserver rightAfterRight ≡ contrastObserver rightAfterRightIncorrect
sameContrastAcrossOutcomeWitness = refl

behavioralDispositionDiffersAcrossOutcome :
  behavioralDisposition rightAfterRight
    ≡ behavioralDisposition rightAfterRightIncorrect → ⊥
behavioralDispositionDiffersAcrossOutcome ()

currentPlusContrastNotAutomaticallyDecisionSufficient :
  ¬ Contrast.ContrastSufficientFor
      historyObserver
      currentObserver
      cueDeviation
      behavioralDisposition
currentPlusContrastNotAutomaticallyDecisionSufficient sufficient =
  Contrast.sameCurrentContrastDifferentActionBlocksSufficiency
    sameCurrentAcrossOutcomeWitness
    sameContrastAcrossOutcomeWitness
    behavioralDispositionDiffersAcrossOutcome
    sufficient

------------------------------------------------------------------------
-- Once previous outcome is retained as an explicit extra coordinate, this
-- finite qualitative policy does factor through the refined observation.
------------------------------------------------------------------------

record DecisionObservation : Set where
  constructor decisionObservation
  field
    observedCurrent : MotionCue
    observedDeviation : CueDeviation
    observedPreviousOutcome : PreviousOutcome

observeDecisionContext : TrialState → DecisionObservation
observeDecisionContext state =
  decisionObservation
    (currentCue state)
    (contrastObserver state)
    (previousOutcome state)

dispositionFromObservation : DecisionObservation → DecisionDisposition
dispositionFromObservation
  (decisionObservation current similarToRecent previousCorrect) =
  maintainPreviousDisposition
dispositionFromObservation
  (decisionObservation current changedFromRecent previousCorrect) =
  reconsiderDisposition
dispositionFromObservation
  (decisionObservation current similarToRecent previousIncorrect) =
  reconsiderDisposition
dispositionFromObservation
  (decisionObservation current changedFromRecent previousIncorrect) =
  maintainPreviousDisposition

decisionObservationIsSufficientForFinitePolicy :
  (state : TrialState) →
  dispositionFromObservation (observeDecisionContext state)
    ≡ behavioralDisposition state
decisionObservationIsSufficientForFinitePolicy
  (trialState cueLeft cueLeft previousCorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueLeft cueRight previousCorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueRight cueLeft previousCorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueRight cueRight previousCorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueLeft cueLeft previousIncorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueLeft cueRight previousIncorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueRight cueLeft previousIncorrect) = refl
decisionObservationIsSufficientForFinitePolicy
  (trialState cueRight cueRight previousIncorrect) = refl

------------------------------------------------------------------------
-- Evidence layers are typed separately so representational and intervention
-- evidence cannot be silently conflated in prose or downstream imports.
------------------------------------------------------------------------

data EvidenceLayer : Set where
  behavioralHistoryDependence : EvidenceLayer
  LPACCContrastEncoding : EvidenceLayer
  LPACCOptogeneticPerturbation : EvidenceLayer
  ACCChoicePredictiveTransformation : EvidenceLayer

sourceEvidenceLayers : List EvidenceLayer
sourceEvidenceLayers =
  behavioralHistoryDependence ∷
  LPACCContrastEncoding ∷
  LPACCOptogeneticPerturbation ∷
  ACCChoicePredictiveTransformation ∷ []

record SourceClaimBoundary : Set where
  constructor sourceClaimBoundary
  field
    historyDependentBehaviorReported : Bool
    historyDependentBehaviorReportedIsTrue :
      historyDependentBehaviorReported ≡ true

    LPACCContrastiveEncodingReported : Bool
    LPACCContrastiveEncodingReportedIsTrue :
      LPACCContrastiveEncodingReported ≡ true

    optogeneticCausalPerturbationReported : Bool
    optogeneticCausalPerturbationReportedIsTrue :
      optogeneticCausalPerturbationReported ≡ true

    presentOnlyObserverProvedInsufficientForFiniteWitness : Bool
    presentOnlyObserverProvedInsufficientForFiniteWitnessIsTrue :
      presentOnlyObserverProvedInsufficientForFiniteWitness ≡ true

    contrastAloneIsCompleteDecisionState : Bool
    contrastAloneIsCompleteDecisionStateIsFalse :
      contrastAloneIsCompleteDecisionState ≡ false

    neuralEncodingAloneProvesCausalUse : Bool
    neuralEncodingAloneProvesCausalUseIsFalse :
      neuralEncodingAloneProvesCausalUse ≡ false

    mouseCircuitProvesHumanCircuitIdentity : Bool
    mouseCircuitProvesHumanCircuitIdentityIsFalse :
      mouseCircuitProvesHumanCircuitIdentity ≡ false

    sourceEstablishesAutismMechanism : Bool
    sourceEstablishesAutismMechanismIsFalse :
      sourceEstablishesAutismMechanism ≡ false

    paperNeuralManifoldReimplementedInDASHI : Bool
    paperNeuralManifoldReimplementedInDASHIIsFalse :
      paperNeuralManifoldReimplementedInDASHI ≡ false

canonicalSourceClaimBoundary : SourceClaimBoundary
canonicalSourceClaimBoundary =
  sourceClaimBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

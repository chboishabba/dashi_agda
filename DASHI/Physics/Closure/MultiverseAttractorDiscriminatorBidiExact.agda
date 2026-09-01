module DASHI.Physics.Closure.MultiverseAttractorDiscriminatorBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi
import DASHI.Core.ObserverRefinementExact as Refinement
import DASHI.Physics.Foundations.FundamentalConstantViabilityFibreExact as Viability
import DASHI.Physics.Closure.TSFVMultiverseViabilityCrossPollinationExact as TSFV

------------------------------------------------------------------------
-- MULTIVERSE / ATTRACTOR / UNIQUE-LAW / TSFV DISCRIMINATOR FRONTIER
--
-- Observing one viable parameter point does not identify the explanatory
-- mechanism that produced or selected it.  The finite fixture makes that
-- collision explicit and provides a refined observation language which can in
-- principle distinguish different predicted signatures.  Application to real
-- cosmology requires empirical/theorem receipts for those signatures.
------------------------------------------------------------------------

data ExplanationHypothesis : Set where
  observerSelectedMultiverse
  dynamicalAttractor
  uniqueLawSelection
  tsfvHistoryConditionedSelection
  : ExplanationHypothesis

data PresentConstantObservation : Set where
  observedViableConstants : PresentConstantObservation

presentObservation : ExplanationHypothesis → PresentConstantObservation
presentObservation _ = observedViableConstants

data CandidateSignature : Set where
  populationSelectionSignature
  basinDynamicsSignature
  lawConstraintSignature
  historyTrajectorySignature
  : CandidateSignature

candidateSignature : ExplanationHypothesis → CandidateSignature
candidateSignature observerSelectedMultiverse = populationSelectionSignature
candidateSignature dynamicalAttractor = basinDynamicsSignature
candidateSignature uniqueLawSelection = lawConstraintSignature
candidateSignature tsfvHistoryConditionedSelection = historyTrajectorySignature

multiverseAndAttractorSharePresentObservation :
  presentObservation observerSelectedMultiverse
  ≡ presentObservation dynamicalAttractor
multiverseAndAttractorSharePresentObservation = refl

multiverseAndAttractorCandidateSignaturesDiffer :
  candidateSignature observerSelectedMultiverse
  ≡ candidateSignature dynamicalAttractor → ⊥
multiverseAndAttractorCandidateSignaturesDiffer ()

refinedObserver : ExplanationHypothesis → PresentConstantObservation × CandidateSignature
refinedObserver hypothesis =
  presentObservation hypothesis , candidateSignature hypothesis

refinedObserverSeparatesMultiverseAttractorFixture :
  refinedObserver observerSelectedMultiverse
  ≡ refinedObserver dynamicalAttractor → ⊥
refinedObserverSeparatesMultiverseAttractorFixture same =
  multiverseAndAttractorCandidateSignaturesDiffer (cong proj₂ same)

viabilityBoundary : Viability.FundamentalConstantViabilityBoundary
viabilityBoundary = Viability.canonicalFundamentalConstantViabilityBoundary

tsfvBoundary : TSFV.TSFVMultiverseViabilityBoundary
tsfvBoundary = TSFV.canonicalTSFVMultiverseViabilityBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record CosmologicalExplanationDiscriminatorReceipt : Set where
  constructor cosmological-explanation-discriminator-receipt
  field
    hypothesisFamilyReference : String
    commonObservationReference : String
    predictedSignatureReference : String
    measurementOrTheoremReference : String
    nuisanceReference : String
    observerSelectionReference : String
    dynamicalAttractorReference : String
    uniqueLawReference : String
    tsfvHistoryReference : String
    provenanceReference : String
    validationReference : String

record MultiverseAttractorDiscriminatorBoundary : Set where
  constructor multiverse-attractor-discriminator-boundary
  field
    observedConstantsIdentifyUniqueExplanation : Bool
    observedConstantsIdentifyUniqueExplanationIsFalse :
      observedConstantsIdentifyUniqueExplanation ≡ false
    viableRegionProvesObserverSelectedMultiverse : Bool
    viableRegionProvesObserverSelectedMultiverseIsFalse :
      viableRegionProvesObserverSelectedMultiverse ≡ false
    viableRegionProvesDynamicalAttractor : Bool
    viableRegionProvesDynamicalAttractorIsFalse :
      viableRegionProvesDynamicalAttractor ≡ false
    samePresentObservationCanHideDifferentExplanationHypotheses : Bool
    samePresentObservationCanHideDifferentExplanationHypothesesIsTrue :
      samePresentObservationCanHideDifferentExplanationHypotheses ≡ true
    refinedPredictionLanguageCanSeparateCandidateHypotheses : Bool
    refinedPredictionLanguageCanSeparateCandidateHypothesesIsTrue :
      refinedPredictionLanguageCanSeparateCandidateHypotheses ≡ true
    candidateSignatureLabelByItselfIsEmpiricalEvidence : Bool
    candidateSignatureLabelByItselfIsEmpiricalEvidenceIsFalse :
      candidateSignatureLabelByItselfIsEmpiricalEvidence ≡ false
    tsfvHistoryReadingIsDistinctFromMultiverseOntology : Bool
    tsfvHistoryReadingIsDistinctFromMultiverseOntologyIsTrue :
      tsfvHistoryReadingIsDistinctFromMultiverseOntology ≡ true
    discriminatorProgrammeUsesActiveBidiLoop : Bool
    discriminatorProgrammeUsesActiveBidiLoopIsTrue :
      discriminatorProgrammeUsesActiveBidiLoop ≡ true
    reading : String

canonicalMultiverseAttractorDiscriminatorBoundary :
  MultiverseAttractorDiscriminatorBoundary
canonicalMultiverseAttractorDiscriminatorBoundary =
  multiverse-attractor-discriminator-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    "The observed values of constants are a coarse observation shared by multiple explanatory hypotheses. Multiverse/observer selection, dynamical attractor, unique-law and TSFV/history-conditioned readings remain distinct until an independently grounded measurement or theorem supplies a signature that separates their live fibres."

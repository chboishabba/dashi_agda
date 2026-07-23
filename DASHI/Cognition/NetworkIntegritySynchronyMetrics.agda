module DASHI.Cognition.NetworkIntegritySynchronyMetrics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.CognitiveResearchSources as Sources
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Cognition.PsychedelicNetworkDiffusion as Network

------------------------------------------------------------------------
-- These quantities answer different questions and must not be conflated:
--
-- * difference/Frobenius-like norm: how far a connectivity profile moved;
-- * cosine data: whether the profile points in a similar edge-space direction;
-- * Jacobian: local derivative of an explicitly selected dynamical model;
-- * phase synchrony: consistency of timing/phase between signals;
-- * within-system integrity: strength/cohesion internal to a chosen network;
-- * cross-system transport: effective communication between chosen networks.
--
-- Sources:
-- Karl J. Friston (2011), DOI 10.1089/brain.2011.0008.
-- Pascal Fries (2005), DOI 10.1016/j.tics.2005.08.011.
------------------------------------------------------------------------

metricSources : List Sources.ResearchSource
metricSources =
  Sources.fristonConnectivityReview ∷
  Sources.friesCommunicationThroughCoherence ∷ []

data MetricKind : Set where
  baselineDifferenceNorm
  flattenedProfileCosine
  dynamicalJacobian
  phaseSynchronyMetric
  withinNetworkIntegrity
  crossNetworkTransport : MetricKind

------------------------------------------------------------------------
-- Finite phase-locking receipt.
------------------------------------------------------------------------

phaseEqual : Phase.Phase3 → Phase.Phase3 → Bool
phaseEqual Phase.phase0 Phase.phase0 = true
phaseEqual Phase.phase1 Phase.phase1 = true
phaseEqual Phase.phase2 Phase.phase2 = true
phaseEqual _ _ = false

countPhaseAgreement : List Phase.Phase3 → List Phase.Phase3 → Nat
countPhaseAgreement [] right = 0
countPhaseAgreement left [] = 0
countPhaseAgreement (left ∷ lefts) (right ∷ rights) with phaseEqual left right
... | true = suc (countPhaseAgreement lefts rights)
... | false = countPhaseAgreement lefts rights

baselineTransmodalPhases : List Phase.Phase3
baselineTransmodalPhases =
  Phase.phase0 ∷ Phase.phase1 ∷ Phase.phase2 ∷ []

baselineSensoryPhases : List Phase.Phase3
baselineSensoryPhases =
  Phase.phase0 ∷ Phase.phase1 ∷ Phase.phase2 ∷ []

psychedelicTransmodalPhases : List Phase.Phase3
psychedelicTransmodalPhases =
  Phase.phase0 ∷ Phase.phase1 ∷ Phase.phase2 ∷ []

psychedelicSensoryPhases : List Phase.Phase3
psychedelicSensoryPhases =
  Phase.phase0 ∷ Phase.phase2 ∷ Phase.phase1 ∷ []

baselinePhaseAgreementIsThree :
  countPhaseAgreement baselineTransmodalPhases baselineSensoryPhases ≡ 3
baselinePhaseAgreementIsThree = refl

psychedelicPhaseAgreementIsOne :
  countPhaseAgreement psychedelicTransmodalPhases psychedelicSensoryPhases ≡ 1
psychedelicPhaseAgreementIsOne = refl

------------------------------------------------------------------------
-- Increased cross-system communication can coexist with reduced synchrony.
-- This is the precise finite answer to why reduced network integrity or phase
-- alignment is not contradicted by greater communication across systems.
------------------------------------------------------------------------

crossTransportHighSynchronyLow :
  (Network.crossCommunication Network.psychedelicProfile ≡ 8)
  ×
  (countPhaseAgreement psychedelicTransmodalPhases psychedelicSensoryPhases ≡ 1)
crossTransportHighSynchronyLow = refl , refl

withinIntegrityLowerCrossTransportHigher :
  (Network.withinIntegrity Network.psychedelicProfile ≡ 12)
  ×
  (Network.crossCommunication Network.psychedelicProfile ≡ 8)
withinIntegrityLowerCrossTransportHigher = refl , refl

------------------------------------------------------------------------
-- Concrete selector: which mathematical object corresponds to which empirical
-- question.  No single scalar is promoted as the universal network measure.
------------------------------------------------------------------------

data NetworkQuestion : Set where
  howFarFromBaseline
  sameConnectivityDirection
  localResponseToPerturbation
  timingAlignment
  internalCohesion
  intersystemCommunication : NetworkQuestion

appropriateMetric : NetworkQuestion → MetricKind
appropriateMetric howFarFromBaseline = baselineDifferenceNorm
appropriateMetric sameConnectivityDirection = flattenedProfileCosine
appropriateMetric localResponseToPerturbation = dynamicalJacobian
appropriateMetric timingAlignment = phaseSynchronyMetric
appropriateMetric internalCohesion = withinNetworkIntegrity
appropriateMetric intersystemCommunication = crossNetworkTransport

jacobianAnswersPerturbationQuestion :
  appropriateMetric localResponseToPerturbation ≡ dynamicalJacobian
jacobianAnswersPerturbationQuestion = refl

synchronyAnswersTimingQuestion :
  appropriateMetric timingAlignment ≡ phaseSynchronyMetric
synchronyAnswersTimingQuestion = refl

module DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ArgumentObstructionCore as Argument
import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop

------------------------------------------------------------------------
-- OPPOSITE ARGUMENT != GEOMETRIC OPPOSITE
--
-- A response to an argument occupies a structured response space.  It may deny
-- a premise, challenge evidence, dispute a rule/causal link, add context, offer
-- an alternative explanation, or suspend judgement.  None of these is
-- definitionally the logical negation or geometric antipode of the conclusion.
------------------------------------------------------------------------

data ResponseKind : Set where
  denyPremise
  challengeEvidence
  challengeRule
  disputeCausation
  disputeCharacterisation
  addContext
  alternativeExplanation
  acceptWithQualification
  suspendJudgement
  : ResponseKind

responseReopens : ResponseKind → Backprop.ReopenCoordinate
responseReopens denyPremise = Backprop.reopenPremise
responseReopens challengeEvidence = Backprop.reopenObservation
responseReopens challengeRule = Backprop.reopenRule
responseReopens disputeCausation = Backprop.reopenModel
responseReopens disputeCharacterisation = Backprop.reopenFrame
responseReopens addContext = Backprop.reopenFrame
responseReopens alternativeExplanation = Backprop.reopenModel
responseReopens acceptWithQualification = Backprop.reopenConsumer
responseReopens suspendJudgement = Backprop.reopenObservation

record StructuredResponse : Set where
  constructor structured-response
  field
    kind : ResponseKind
    reopenTarget : Backprop.ReopenCoordinate
    targetCorrect : reopenTarget ≡ responseReopens kind
    responseReference : String
    retainedWholeArgumentReference : String
    retainedProvenanceReference : String

open StructuredResponse public

------------------------------------------------------------------------
-- Exact response-space witnesses.
------------------------------------------------------------------------

challengeEvidenceResponse : StructuredResponse
challengeEvidenceResponse =
  structured-response challengeEvidence Backprop.reopenObservation refl
    "challenge the evidence supporting the transport"
    "retain the whole argument while evidence is re-audited"
    "retain argument/source provenance"

alternativeExplanationResponse : StructuredResponse
alternativeExplanationResponse =
  structured-response alternativeExplanation Backprop.reopenModel refl
    "offer an alternative explanation rather than negate the target"
    "retain the original target and premises as live graph objects"
    "retain provenance of both explanations"

qualifiedAcceptanceResponse : StructuredResponse
qualifiedAcceptanceResponse =
  structured-response acceptWithQualification Backprop.reopenConsumer refl
    "accept some proposition while changing the consumer/qualification"
    "acceptance with qualification is not the antipode of denial"
    "qualification and source provenance remain explicit"

------------------------------------------------------------------------
-- Argument-transport donor consequences.
------------------------------------------------------------------------

currentNoTypedMeetMayReopenByDeeperParse :
  Transport.Inspect.NoTypedMeetAtInspection.revisableUnderDeeperParse
    Transport.Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReopenByDeeperParse =
  Transport.currentNoTypedMeetMayReviseByDeeperParse

currentNoTypedMeetMayReopenByBridge :
  Transport.Inspect.NoTypedMeetAtInspection.revisableUnderBridge
    Transport.Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReopenByBridge =
  Transport.currentNoTypedMeetMayReviseByBridge

currentNoTypedMeetMayReopenByRoleAssignment :
  Transport.Inspect.NoTypedMeetAtInspection.revisableUnderNewRoleAssignment
    Transport.Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReopenByRoleAssignment =
  Transport.currentNoTypedMeetMayReviseByRoleAssignment

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ResponseIsLogicalNegation : Set where
data ChallengeEvidenceRefutesConclusion : Set where
data AlternativeExplanationIsGeometricAntipode : Set where
data LocalTransportFailureErasesWholeArgument : Set where

responseIsNotAutomaticallyLogicalNegation : ResponseIsLogicalNegation → ⊥
responseIsNotAutomaticallyLogicalNegation ()

challengeEvidenceDoesNotRefuteConclusion : ChallengeEvidenceRefutesConclusion → ⊥
challengeEvidenceDoesNotRefuteConclusion ()

alternativeExplanationIsNotGeometricAntipode : AlternativeExplanationIsGeometricAntipode → ⊥
alternativeExplanationIsNotGeometricAntipode ()

localTransportFailureDoesNotEraseWholeArgument :
  LocalTransportFailureErasesWholeArgument → ⊥
localTransportFailureDoesNotEraseWholeArgument ()

obstructionMayStillLeaveConclusionOpen :
  {core : Argument.ArgumentCore} →
  Argument.Obstruction core → Bool
obstructionMayStillLeaveConclusionOpen =
  Argument.fallacyDoesNotRefuteConclusion

record ArgumentResponseGeometryBoundary : Set where
  constructor argument-response-geometry-boundary
  field
    responseSpaceHasMultipleConstructors : Bool
    responseEqualsLogicalNegation : Bool
    obstructionEqualsConclusionRefutation : Bool
    localFailureMayTriggerReparseOrRechart : Bool
    wholeArgumentAndProvenanceRemainRetained : Bool
    geometricOppositeCanBeInferredFromAdversarialRole : Bool

canonicalArgumentResponseGeometryBoundary : ArgumentResponseGeometryBoundary
canonicalArgumentResponseGeometryBoundary =
  argument-response-geometry-boundary true false false true true false

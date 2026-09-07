module DASHI.Law.SecuritySemanticEscalationDistanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.SecurityThreatSemanticBroadeningTopologyExact as Broad

------------------------------------------------------------------------
-- Ordered semantic escalation surface.
-- This is an audit metric over representation severity, not a claim that every
-- later label is false or unlawful.
------------------------------------------------------------------------

data EscalationLevel : Set where
  preservedLevel
  narrowedLevel
  broadenedScopeLevel
  broadenedPredicateLevel
  collectiveEnemyLevel
  terminalEnemyLevel : EscalationLevel

levelCode : EscalationLevel → ℕ
levelCode preservedLevel = 0
levelCode narrowedLevel = 0
levelCode broadenedScopeLevel = 1
levelCode broadenedPredicateLevel = 2
levelCode collectiveEnemyLevel = 3
levelCode terminalEnemyLevel = 4

record EscalationReceipt : Set where
  constructor escalationReceipt
  field
    sourceNode targetNode : Broad.ThreatNode
    sourceLevel targetLevel : EscalationLevel
    producerReference : String
    sameObjectLineageClosed : Bool
    evidenceAdequacyClosed : Bool

open EscalationReceipt public

record EscalationPath : Set where
  constructor escalationPath
  field
    first second third : EscalationReceipt
    monotoneNonDecreasing : Bool
    strictIncreaseObserved : Bool
    pathReference : String

open EscalationPath public

syntheticEscalationPath : EscalationPath
syntheticEscalationPath = escalationPath
  (escalationReceipt Broad.specificIndividualThreat Broad.subsetRisk
    preservedLevel broadenedScopeLevel "synthetic calibration" true true)
  (escalationReceipt Broad.subsetRisk Broad.wholeAssemblyRisk
    broadenedScopeLevel collectiveEnemyLevel "synthetic calibration" true true)
  (escalationReceipt Broad.wholeAssemblyRisk Broad.wholeAssemblyOrder
    collectiveEnemyLevel collectiveEnemyLevel "synthetic calibration" true true)
  true true
  "specific individual concern -> subset -> whole-assembly collective-risk classification"

syntheticPathMonotone : monotoneNonDecreasing syntheticEscalationPath ≡ true
syntheticPathMonotone = refl

syntheticPathStrict : strictIncreaseObserved syntheticEscalationPath ≡ true
syntheticPathStrict = refl

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data EscalationClaim : Set where
  semanticEscalationOccurred
  escalationWasEvidenceJustified
  escalationWasMonotoneAcrossInstitutions
  collectiveEnemyStageReached
  terminalEnemyStageReached
  escalationWasIdeologicallyMotivated : EscalationClaim

data EscalationProducer : Set where
  semanticTransformationCorpusProducer
  stageSpecificEvidenceAdequacyProducer
  orderedSameObjectPathProducer
  collectiveEnemyClassificationProducer
  terminalisationCommandConductProducer
  motiveCarrierProducer : EscalationProducer

reverseEscalation : EscalationClaim → EscalationProducer
reverseEscalation semanticEscalationOccurred = semanticTransformationCorpusProducer
reverseEscalation escalationWasEvidenceJustified = stageSpecificEvidenceAdequacyProducer
reverseEscalation escalationWasMonotoneAcrossInstitutions = orderedSameObjectPathProducer
reverseEscalation collectiveEnemyStageReached = collectiveEnemyClassificationProducer
reverseEscalation terminalEnemyStageReached = terminalisationCommandConductProducer
reverseEscalation escalationWasIdeologicallyMotivated = motiveCarrierProducer

record EscalationBoundary : Set where
  constructor escalationBoundary
  field
    strongerLaterLanguageProvesSameObjectEscalation : Bool
    strongerLaterLanguageProvesSameObjectEscalationIsFalse : strongerLaterLanguageProvesSameObjectEscalation ≡ false
    monotoneEscalationProvesEvidenceAdequacy : Bool
    monotoneEscalationProvesEvidenceAdequacyIsFalse : monotoneEscalationProvesEvidenceAdequacy ≡ false
    collectiveEnemyLabelEqualsTerminalisation : Bool
    collectiveEnemyLabelEqualsTerminalisationIsFalse : collectiveEnemyLabelEqualsTerminalisation ≡ false
    semanticEscalationProvesIdeologicalMotive : Bool
    semanticEscalationProvesIdeologicalMotiveIsFalse : semanticEscalationProvesIdeologicalMotive ≡ false

canonicalEscalationBoundary : EscalationBoundary
canonicalEscalationBoundary = escalationBoundary false refl false refl false refl false refl

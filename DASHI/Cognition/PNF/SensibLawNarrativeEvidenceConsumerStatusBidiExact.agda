module DASHI.Cognition.PNF.SensibLawNarrativeEvidenceConsumerStatusBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as Narrative
import DASHI.Cognition.PNF.ConsumerIndexedNarrativeProjectionExact as Consumer
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status

------------------------------------------------------------------------
-- NARRATIVE EVIDENCE / CONSUMER-STATUS BIDI
--
-- Existing narrative owners already separate factual, rhetorical, cultural and
-- institutional consumer planes and already prove that replicated narrative
-- evidence does not become independent evidence.  This module attaches those
-- exact distinctions to the new semantic status product.
------------------------------------------------------------------------

factStatusToTruth : Consumer.FactStatus → Status.TruthStatus
factStatusToTruth Consumer.factSupported = Status.candidateTrue
factStatusToTruth Consumer.factRefuted = Status.candidateFalse
factStatusToTruth Consumer.factUnresolved = Status.truthUnresolved

institutionalToJudicial :
  Consumer.InstitutionalStatus → Status.JudicialDiscourseStatus
institutionalToJudicial Consumer.noDisposition = Status.judicialStatusUnresolved
institutionalToJudicial Consumer.nonActionableOpinion = Status.disposition
institutionalToJudicial Consumer.actionableStatement = Status.disposition

record ConsumerStatusProjectionReceipt : Set where
  constructor consumerStatusProjectionReceipt
  field
    propositionReference : String
    factStatus : Consumer.FactStatus
    institutionalStatus : Consumer.InstitutionalStatus
    proposition : Status.PropositionStatusProduct
    legal : Status.LegalStatusProduct
    truthProjectionExact :
      Status.truthStatus proposition ≡ factStatusToTruth factStatus
    judicialProjectionExact :
      Status.judicialStatus legal ≡ institutionalToJudicial institutionalStatus

open ConsumerStatusProjectionReceipt public

compileConsumerStatus :
  String → Consumer.FactStatus → Consumer.InstitutionalStatus →
  ConsumerStatusProjectionReceipt
compileConsumerStatus propositionRef fact institution =
  consumerStatusProjectionReceipt
    propositionRef
    fact
    institution
    (Status.propositionStatusProduct
      propositionRef
      Status.propositionRepresented
      (factStatusToTruth fact)
      Status.attributionUnresolved
      Status.evidencePolarityUnresolved
      Status.evidenceKindUnresolved
      Status.modalityKindUnresolved
      Status.modalForceUnresolved
      Status.scopeUnresolved)
    (Status.legalStatusProduct
      Status.jurisdictionUnresolved
      Status.authorityUnresolved
      Status.conditionUnresolved
      Status.applicabilityUnresolved
      Status.violationUnresolved
      Status.liabilityUnresolved
      Status.burdenKindUnresolved
      Status.standardUnresolved
      (institutionalToJudicial institution)
      Status.normativeRelationUnresolved)
    refl
    refl

notLikeUsConsumerStatus : ConsumerStatusProjectionReceipt
notLikeUsConsumerStatus =
  compileConsumerStatus
    "narrative:not-like-us"
    (Consumer.factual Consumer.notLikeUsConsumers Consumer.notLikeUsArtifact)
    (Consumer.institutional Consumer.notLikeUsConsumers Consumer.notLikeUsArtifact)

notLikeUsTruthStillUnresolved :
  Status.truthStatus
    (ConsumerStatusProjectionReceipt.proposition notLikeUsConsumerStatus)
  ≡ Status.truthUnresolved
notLikeUsTruthStillUnresolved = refl

notLikeUsDispositionIsSeparate :
  Status.judicialStatus
    (ConsumerStatusProjectionReceipt.legal notLikeUsConsumerStatus)
  ≡ Status.disposition
notLikeUsDispositionIsSeparate = refl

------------------------------------------------------------------------
-- Evidence lineage transport.  Replication changes repetition/salience but
-- preserves the literal origin and therefore cannot manufacture a second
-- independent evidence receipt or upgrade truth.
------------------------------------------------------------------------

record EvidenceReplicationStatusReceipt : Set where
  constructor evidenceReplicationStatusReceipt
  field
    before after : Narrative.EvidenceLineage
    truthBefore truthAfter : Status.TruthStatus
    afterIsReplication : after ≡ Narrative.replicateEvidence before
    sameOrigin : Narrative.originId after ≡ Narrative.originId before
    truthUnchanged : truthAfter ≡ truthBefore
    independentEvidenceAdded : Bool
    independentEvidenceAddedIsFalse : independentEvidenceAdded ≡ false

open EvidenceReplicationStatusReceipt public

replicateEvidenceWithoutTruthUpgrade :
  Narrative.EvidenceLineage → Status.TruthStatus → EvidenceReplicationStatusReceipt
replicateEvidenceWithoutTruthUpgrade lineage truth =
  evidenceReplicationStatusReceipt
    lineage
    (Narrative.replicateEvidence lineage)
    truth
    truth
    refl
    (Narrative.replicationPreservesOrigin lineage)
    refl
    false
    refl

replicationCannotPayIndependentEvidence :
  (lineage : Narrative.EvidenceLineage) →
  Narrative.IndependentEvidencePair lineage (Narrative.replicateEvidence lineage) → ⊥
replicationCannotPayIndependentEvidence =
  Narrative.replicationDoesNotCreateIndependentEvidence

------------------------------------------------------------------------
-- No cross-plane collapse.
------------------------------------------------------------------------

data InstitutionalDispositionAdmitsTruth : Set where
data CandidateFactSupportAdmitsTruth : Set where
data RepetitionRaisesTruthAuthority : Set where

institutionalDispositionDoesNotAdmitTruth :
  InstitutionalDispositionAdmitsTruth → ⊥
institutionalDispositionDoesNotAdmitTruth ()

candidateFactSupportDoesNotAdmitTruth : CandidateFactSupportAdmitsTruth → ⊥
candidateFactSupportDoesNotAdmitTruth ()

repetitionDoesNotRaiseTruthAuthority : RepetitionRaisesTruthAuthority → ⊥
repetitionDoesNotRaiseTruthAuthority ()

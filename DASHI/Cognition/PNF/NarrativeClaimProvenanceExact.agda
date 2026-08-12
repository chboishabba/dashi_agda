module DASHI.Cognition.PNF.NarrativeClaimProvenanceExact where

------------------------------------------------------------------------
-- NARRATIVE CLAIM / PROVENANCE CORE
--
-- A public narrative is not one truth-valued proposition.  It is a family of
-- proposition-local, provenance-bearing claim edges that may be copied and
-- amplified without creating new independent evidence.
--
-- This module is domain-generic.  The Kendrick/Drake worked example is in
-- DissTrackNarrativeDynamicsExact; no allegation about any real person is
-- asserted as mathematical fact here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Claim modality and consumer planes remain separately typed.
------------------------------------------------------------------------

data ClaimModality : Set where
  alleged denied corroborated refuted unresolved interpreted : ClaimModality

data NarrativePlane : Set where
  factual rhetorical cultural institutional : NarrativePlane

record ClaimEdge
    (Subject Proposition Source Evidence Provenance : Set) : Set₁ where
  constructor claimEdge
  field
    subject : Subject
    proposition : Proposition
    source : Source
    evidence : Evidence
    provenance : Provenance
    modality : ClaimModality

open ClaimEdge public

------------------------------------------------------------------------
-- Evidence lineage: repetition is not independent corroboration.
------------------------------------------------------------------------

record EvidenceLineage : Set where
  constructor evidenceLineage
  field
    originId : Nat
    repetitionCount : Nat

open EvidenceLineage public

replicateEvidence : EvidenceLineage → EvidenceLineage
replicateEvidence (evidenceLineage origin copies) =
  evidenceLineage origin (suc copies)

replicationPreservesOrigin :
  (lineage : EvidenceLineage) →
  originId (replicateEvidence lineage) ≡ originId lineage
replicationPreservesOrigin lineage = refl

replicationIncrementsRepetition :
  (lineage : EvidenceLineage) →
  repetitionCount (replicateEvidence lineage)
  ≡ suc (repetitionCount lineage)
replicationIncrementsRepetition lineage = refl

record IndependentEvidencePair
    (left right : EvidenceLineage) : Set where
  constructor independentEvidencePair
  field
    distinctOrigins : originId left ≡ originId right → ⊥

open IndependentEvidencePair public

replicationDoesNotCreateIndependentEvidence :
  (lineage : EvidenceLineage) →
  IndependentEvidencePair lineage (replicateEvidence lineage) → ⊥
replicationDoesNotCreateIndependentEvidence lineage independent =
  distinctOrigins independent refl

------------------------------------------------------------------------
-- Replication can increase salience while provenance remains unchanged.
------------------------------------------------------------------------

record NarrativeSignal : Set where
  constructor narrativeSignal
  field
    lineage : EvidenceLineage
    salience : Nat

open NarrativeSignal public

replicateSignal : NarrativeSignal → NarrativeSignal
replicateSignal (narrativeSignal provenance n) =
  narrativeSignal (replicateEvidence provenance) (suc n)

signalReplicationPreservesOrigin :
  (signal : NarrativeSignal) →
  originId (lineage (replicateSignal signal))
  ≡ originId (lineage signal)
signalReplicationPreservesOrigin signal = refl

signalReplicationRaisesSalience :
  (signal : NarrativeSignal) →
  salience (replicateSignal signal) ≡ suc (salience signal)
signalReplicationRaisesSalience signal = refl

------------------------------------------------------------------------
-- Four public planes can be updated independently.  No constructor promotes
-- rhetorical/cultural/institutional state into factual truth.
------------------------------------------------------------------------

record FourPlaneState
    (Factual Rhetorical Cultural Institutional : Set) : Set₁ where
  constructor fourPlaneState
  field
    factualState : Factual
    rhetoricalState : Rhetorical
    culturalState : Cultural
    institutionalState : Institutional

open FourPlaneState public

updateRhetorical :
  ∀ {F R C I} → R → FourPlaneState F R C I → FourPlaneState F R C I
updateRhetorical new (fourPlaneState f old c i) =
  fourPlaneState f new c i

updateCultural :
  ∀ {F R C I} → C → FourPlaneState F R C I → FourPlaneState F R C I
updateCultural new (fourPlaneState f r old i) =
  fourPlaneState f r new i

updateInstitutional :
  ∀ {F R C I} → I → FourPlaneState F R C I → FourPlaneState F R C I
updateInstitutional new (fourPlaneState f r c old) =
  fourPlaneState f r c new

rhetoricalUpdatePreservesFact :
  ∀ {F R C I} (new : R) (state : FourPlaneState F R C I) →
  factualState (updateRhetorical new state) ≡ factualState state
rhetoricalUpdatePreservesFact new state = refl

culturalUpdatePreservesFact :
  ∀ {F R C I} (new : C) (state : FourPlaneState F R C I) →
  factualState (updateCultural new state) ≡ factualState state
culturalUpdatePreservesFact new state = refl

institutionalUpdatePreservesFact :
  ∀ {F R C I} (new : I) (state : FourPlaneState F R C I) →
  factualState (updateInstitutional new state) ≡ factualState state
institutionalUpdatePreservesFact new state = refl

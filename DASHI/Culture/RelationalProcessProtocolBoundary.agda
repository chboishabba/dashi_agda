module DASHI.Culture.RelationalProcessProtocolBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Culture.DerivedCulturalUseAdmissibility as Cultural

------------------------------------------------------------------------
-- A provenance-bounded workflow inspired by attributed relational principles.
-- This is not claimed to reproduce or replace living Indigenous knowledge.

data ProcessPhase : Set where
  respectPhase connectPhase reflectPhase directPhase : ProcessPhase

record ProtocolStep : Set where
  constructor protocolStep
  field
    phase : ProcessPhase
    purpose : String
    requiredWitness : String
    output : String

open ProtocolStep public

respectStep : ProtocolStep
respectStep =
  protocolStep respectPhase
    "establish authority, consent, boundaries, and access conditions"
    "provenance and permission receipt appropriate to the material"
    "declared protocol and protected information classes"

connectStep : ProtocolStep
connectStep =
  protocolStep connectPhase
    "map relations among people, place, time, claims, evidence, and obligations"
    "source/context links and participant-defined relation labels"
    "relational graph with retained provenance"

reflectStep : ProtocolStep
reflectStep =
  protocolStep reflectPhase
    "compare local accounts, preserve disagreement, and inspect gluing defects"
    "overlap, restriction, uncertainty, and contention receipts"
    "shared structure plus explicit residual disagreement"

directStep : ProtocolStep
directStep =
  protocolStep directPhase
    "authorise bounded action without erasing dissent or uncertainty"
    "decision authority, consent scope, and review path"
    "action record with responsibility and revisit conditions"

canonicalProtocol : List ProtocolStep
canonicalProtocol = respectStep ∷ connectStep ∷ reflectStep ∷ directStep ∷ []

------------------------------------------------------------------------
-- Reciprocity/resource accounting is a selected audit view, not the ethic.

record ReciprocityAudit : Set₁ where
  field
    Node Transfer Weight Balance : Set
    transfer : Node → Node → Transfer
    weight : Node → Node → Weight
    incoming : Node → Balance
    outgoing : Node → Balance
    weightedResidual : Node → Balance
    residualLaw : Set
    needAndCapacityRepresented : Set
    consentRepresented : Set

record ActionAuthorisation : Set where
  constructor actionAuthorisation
  field
    authorityHolder : String
    authorityScope : String
    consentReference : String
    dissentPreserved : Bool
    reviewAvailable : Bool

canonicalActionAuthorisation : ActionAuthorisation
canonicalActionAuthorisation =
  actionAuthorisation
    "domain-appropriate authorised participant"
    "bounded action recorded by the protocol"
    "explicit consent/provenance receipt required from the concrete instance"
    true
    true

------------------------------------------------------------------------
-- Provenance for this limited formal analogy.

protocolProvenance : Cultural.ProvenanceWitness
protocolProvenance =
  Cultural.mkProvenanceWitness
    "Tyson Yunkaporta / user-supplied Sand Talk discussion"
    "Respect, Connect, Reflect, Direct as attributed in the supplied design material"
    "limited workflow analogy for relational evidence and decision governance"
    "not a formalisation of Indigenous Knowledge, not community authority, and not permission to extract or substitute living practice"

protocolAnalogyAdmissible :
  Cultural.AdmissibleCulturalUse
    Cultural.formalAnalogyMaterial
    Cultural.limitedFormalAnalogyUse
protocolAnalogyAdmissible = Cultural.formalAnalogyAdmissible protocolProvenance

record RelationalProcessBoundary : Set where
  constructor relationalProcessBoundary
  field
    provenanceRequired : Bool
    consentAndAuthorityRequired : Bool
    disagreementPreserved : Bool
    processMayGuideITIRWorkflow : Bool
    processImplementsIndigenousKnowledge : Bool
    processImplementsIndigenousKnowledgeIsFalse :
      processImplementsIndigenousKnowledge ≡ false
    reciprocityScoreExhaustsEthics : Bool
    reciprocityScoreExhaustsEthicsIsFalse : reciprocityScoreExhaustsEthics ≡ false
    communityPermissionImplied : Bool
    communityPermissionImpliedIsFalse : communityPermissionImplied ≡ false
    interpretation : String

canonicalRelationalProcessBoundary : RelationalProcessBoundary
canonicalRelationalProcessBoundary =
  relationalProcessBoundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "Respect-Connect-Reflect-Direct is retained as a provenance-bounded workflow analogy with consent, relationship mapping, reflection, and authorised action; it does not claim community authority or cultural substitution"

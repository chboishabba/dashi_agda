module DASHI.Governance.RelationPolicyTransportComposition where

open import Data.Empty using (⊥)
import DASHI.Core.PropositionLocalRelationTransport as Core
import DASHI.Governance.AsymmetricReflectionPropositionLocality as Orbit
import DASHI.Governance.ProvenancePolicyTransport as Policy

------------------------------------------------------------------------
-- Governance adapter over the canonical proposition-local relation core.
--
-- DASHI.Core.PropositionLocalRelationTransport already owns typed two-step
-- paths, proposition-specific TransportLicence, LicensedPathClaim, and the
-- unlicensed-path impossibility theorem.  This module does not duplicate those
-- objects; it only connects a licensed relational claim to proposition-local
-- policy routing.
------------------------------------------------------------------------

record OrbitRelationCoreAdapter
    (R : Orbit.RelationalOrbitSystem) : Set₁ where
  field
    Proposition : Set
    Evidence : Set
    Provenance : Set
    supports : Evidence → Proposition → Set
    provenanceOf : Evidence → Provenance

open OrbitRelationCoreAdapter public

orbitCore :
  (R : Orbit.RelationalOrbitSystem) →
  OrbitRelationCoreAdapter R →
  Core.TypedRelationSystem
orbitCore R A =
  record
    { Node = Orbit.Actor R
    ; Relation = Orbit.RelationKind
    ; Proposition = Proposition A
    ; Evidence = Evidence A
    ; Provenance = Provenance A
    ; Edge = Orbit.Related R
    ; supports = supports A
    ; provenanceOf = provenanceOf A
    }

------------------------------------------------------------------------
-- Bridge a core relational node into an existing provenance-policy system.
-- The bridge itself conveys no guilt, knowledge, facilitation, or
-- participation.
------------------------------------------------------------------------

record RelationPolicyBridge
    (G : Core.TypedRelationSystem)
    (S : Policy.ProvenancePolicySystem) : Set₁ where
  field
    policyActor : Core.Node G → Policy.Actor S
    localPolicy : Policy.PropositionLocalPolicy S

open RelationPolicyBridge public

------------------------------------------------------------------------
-- A path-derived policy relevance witness consumes the canonical
-- LicensedPathClaim.  Therefore relation-pair + proposition transport evidence
-- has already been supplied before the downstream policy layer is entered.
------------------------------------------------------------------------

data LicensedPathPolicyRelevance
    {G : Core.TypedRelationSystem}
    {S : Policy.ProvenancePolicySystem}
    (B : RelationPolicyBridge G S) : Set₁ where
  licensedPolicyRoute :
    ∀ {source middle target first second} →
    (path : Core.TwoStepPath G source middle target first second) →
    (proposition : Core.Proposition G) →
    Core.LicensedPathClaim G path proposition →
    (evidence : Policy.PresentEvidence S) →
    Policy.ActionSupport (localPolicy B)
      (policyActor B target)
      (Policy.route S
        (Policy.provenance S (policyActor B target))
        evidence
        (Policy.classify S evidence (policyActor B target))) →
    LicensedPathPolicyRelevance B

------------------------------------------------------------------------
-- Connectivity alone still cannot authorise policy.  This is intentionally a
-- separate promotion boundary from the canonical core's
-- UnlicensedPathPromotion, because a licensed proposition is still not by
-- itself a policy action.
------------------------------------------------------------------------

data ConnectivityAutomaticallyAuthorisesPolicy
    {G : Core.TypedRelationSystem}
    {S : Policy.ProvenancePolicySystem}
    (B : RelationPolicyBridge G S) : Set where

connectivityDoesNotAutomaticallyAuthorisePolicy :
  ∀ {G S} {B : RelationPolicyBridge G S} →
  ConnectivityAutomaticallyAuthorisesPolicy B → ⊥
connectivityDoesNotAutomaticallyAuthorisePolicy ()

------------------------------------------------------------------------
-- Special-purpose names are deliberately absent: Epstein/network, kinship,
-- nationality, ethnicity, party, military, and organisational applications
-- all instantiate the same canonical relation-pair + proposition licence.
------------------------------------------------------------------------

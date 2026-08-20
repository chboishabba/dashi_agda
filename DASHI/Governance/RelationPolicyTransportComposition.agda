module DASHI.Governance.RelationPolicyTransportComposition where

open import Data.Empty using (⊥)
import DASHI.Governance.AsymmetricReflectionPropositionLocality as Orbit
import DASHI.Governance.ProvenancePolicyTransport as Policy

------------------------------------------------------------------------
-- Typed relation-path -> policy relevance composition.
--
-- Reachability in an elite/social/political graph is not inheritance of an
-- arbitrary proposition.  A two-edge path can enter policy only through an
-- explicit proposition-specific transport licence and an independently
-- supplied proposition-local support witness.
------------------------------------------------------------------------

record TwoStepRelationPath (R : Orbit.RelationalOrbitSystem) : Set₁ where
  field
    source middle target : Orbit.Actor R
    firstKind secondKind : Orbit.RelationKind
    firstEdge : Orbit.Related R firstKind source middle
    secondEdge : Orbit.Related R secondKind middle target

open TwoStepRelationPath public

record PropositionTransportLicence
    (R : Orbit.RelationalOrbitSystem)
    (path : TwoStepRelationPath R) : Set₁ where
  field
    Proposition : Set
    proposition : Proposition
    LicenceEvidence : Set
    licenceEvidence : LicenceEvidence

open PropositionTransportLicence public

------------------------------------------------------------------------
-- Bridge a relational actor into an existing provenance-policy system.  The
-- bridge itself conveys no guilt, knowledge, facilitation, or participation.
------------------------------------------------------------------------

record RelationPolicyBridge
    (R : Orbit.RelationalOrbitSystem)
    (S : Policy.ProvenancePolicySystem) : Set₁ where
  field
    policyActor : Orbit.Actor R → Policy.Actor S
    localPolicy : Policy.PropositionLocalPolicy S

open RelationPolicyBridge public

------------------------------------------------------------------------
-- Closed constructor surface: path-derived policy relevance can only be built
-- by presenting a path, its proposition-specific licence, current evidence,
-- and a support-locality witness for the resulting routed action.
------------------------------------------------------------------------

data PathPolicyRelevance
    {R : Orbit.RelationalOrbitSystem}
    {S : Policy.ProvenancePolicySystem}
    (B : RelationPolicyBridge R S) : Set₁ where
  licensedPath :
    (path : TwoStepRelationPath R) →
    (licence : PropositionTransportLicence R path) →
    (evidence : Policy.PresentEvidence S) →
    Policy.ActionSupport (localPolicy B)
      (policyActor B (target path))
      (Policy.route S
        (Policy.provenance S (policyActor B (target path)))
        evidence
        (Policy.classify S evidence (policyActor B (target path)))) →
    PathPolicyRelevance B

------------------------------------------------------------------------
-- Explicit non-promotion types.  These intentionally have no constructors:
-- neither graph connectivity nor kinship/social adjacency manufactures the
-- missing proposition licence.
------------------------------------------------------------------------

data PathAutomaticallyInheritsProposition
    {R : Orbit.RelationalOrbitSystem}
    (path : TwoStepRelationPath R) : Set where

pathDoesNotAutomaticallyInheritProposition :
  ∀ {R} {path : TwoStepRelationPath R} →
  PathAutomaticallyInheritsProposition path → ⊥
pathDoesNotAutomaticallyInheritProposition ()

data ConnectivityAutomaticallyAuthorisesPolicy
    {R : Orbit.RelationalOrbitSystem}
    {S : Policy.ProvenancePolicySystem}
    (B : RelationPolicyBridge R S)
    (path : TwoStepRelationPath R) : Set where

connectivityDoesNotAutomaticallyAuthorisePolicy :
  ∀ {R S} {B : RelationPolicyBridge R S}
    {path : TwoStepRelationPath R} →
  ConnectivityAutomaticallyAuthorisesPolicy B path → ⊥
connectivityDoesNotAutomaticallyAuthorisePolicy ()

------------------------------------------------------------------------
-- Special-purpose names are deliberately absent: Epstein/network, kinship,
-- nationality, ethnicity, party, military, and organisational applications
-- must all instantiate the same relation-pair + proposition licence interface.
------------------------------------------------------------------------

module DASHI.Cognition.PNF.SensibLawMatterContextProjectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Context.NarrativeProjectionBoundary as Narrative
import DASHI.Context.RoleScopedAccessContract as Access

------------------------------------------------------------------------
-- S30.C MatterContext projection contract.
--
-- This is NOT a new semantic world and NOT a truth-bearing ontology.
-- It binds an already-reviewed matter world to one purpose/role/knowledge
-- cut/disclosure boundary and records which coordinates may be rendered.
------------------------------------------------------------------------

data MatterDisclosureBoundary : Set where
  matterInternal : MatterDisclosureBoundary
  roleScoped : MatterDisclosureBoundary
  recipientScoped : MatterDisclosureBoundary
  metadataOnly : MatterDisclosureBoundary
  publicProjection : MatterDisclosureBoundary
  protectedDisclosure : MatterDisclosureBoundary

data KnowledgeTimeCut : Set where
  allKnown : KnowledgeTimeCut
  asKnownAt : String → KnowledgeTimeCut

data KnowledgeCutMembership : Set where
  knownAtCut : KnowledgeCutMembership
  knownAfterCut : KnowledgeCutMembership
  unknownAtCut : KnowledgeCutMembership
  notApplicable : KnowledgeCutMembership

record MatterContext : Set where
  constructor matter-context
  field
    matterRef : String
    purpose : Access.AccessPurpose
    activeConsumerRole : Narrative.AudienceRole
    disclosureBoundary : MatterDisclosureBoundary
    knowledgeTimeCut : KnowledgeTimeCut
    sealedRefs : List String
    accessGrant : Access.AccessGrant

    grantRoleMatches :
      Access.granteeRole accessGrant ≡ activeConsumerRole

    grantPurposeMatches :
      Access.purpose accessGrant ≡ purpose

    minimumNecessary : Bool
    minimumNecessaryIsTrue : minimumNecessary ≡ true

    purposeLimited : Bool
    purposeLimitedIsTrue : purposeLimited ≡ true

    accessLogged : Bool
    accessLoggedIsTrue : accessLogged ≡ true

    revocable : Bool
    revocableIsTrue : revocable ≡ true

    mutatesCanonicalWorld : Bool
    mutatesCanonicalWorldIsFalse : mutatesCanonicalWorld ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open MatterContext public

record ContextProjectionCoordinate : Set where
  constructor context-projection-coordinate
  field
    semanticRef : String
    matterRef : String
    knowledgeMembership : KnowledgeCutMembership
    explicitlySelected : Bool
    sealed : Bool

open ContextProjectionCoordinate public

data ContextExclusionKind : Set where
  wrongMatter : ContextExclusionKind
  sealedExclusion : ContextExclusionKind
  roleNotAllowed : ContextExclusionKind
  purposeNotAllowed : ContextExclusionKind
  knownAfterCutExclusion : ContextExclusionKind
  unknownAtCutExclusion : ContextExclusionKind
  notSelectedMinimumNecessary : ContextExclusionKind

record MatterContextProjectionReceipt : Set where
  constructor matter-context-projection-receipt
  field
    matterRef : String
    includedRefs : List String
    excludedRefs : List String

    canonicalWorldMutated : Bool
    canonicalWorldMutatedIsFalse : canonicalWorldMutated ≡ false

    invisibilityMeansFalse : Bool
    invisibilityMeansFalseIsFalse : invisibilityMeansFalse ≡ false

    unsharedMeansAbsent : Bool
    unsharedMeansAbsentIsFalse : unsharedMeansAbsent ≡ false

    roleVisibilityCreatesTruth : Bool
    roleVisibilityCreatesTruthIsFalse :
      roleVisibilityCreatesTruth ≡ false

    laterKnowledgeRewritesEarlierCut : Bool
    laterKnowledgeRewritesEarlierCutIsFalse :
      laterKnowledgeRewritesEarlierCut ≡ false

open MatterContextProjectionReceipt public

------------------------------------------------------------------------
-- Reuse the historical role/purpose contract rather than defining a second
-- access-control ontology.
------------------------------------------------------------------------

canonicalMatterContext : MatterContext
canonicalMatterContext =
  matter-context
    "matter:example"
    Access.legalAdvocacy
    Narrative.advocate
    recipientScoped
    (asKnownAt "knowledge-cut:example")
    []
    Access.canonicalAdvocateGrant
    refl
    refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

canonicalMatterProjectionReceipt : MatterContextProjectionReceipt
canonicalMatterProjectionReceipt =
  matter-context-projection-receipt
    "matter:example"
    []
    []
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MatterContextIsNewSemanticWorld : Set where
data ContextProjectionMutatesSource : Set where
data LaterKnowledgeRewritesEarlierEpistemicView : Set where
data SealedRefAppearsInOrdinaryProjection : Set where
data NotVisibleMeansFalse : Set where
data NotSharedMeansAbsentFromWorld : Set where
data RoleVisibilityCreatesClaimTruth : Set where
data MinimumNecessaryProjectionDeletesCanonicalSource : Set where
data KnowledgeCutStringOrderingCreatesTemporalFact : Set where
data ContextAccessGrantCreatesSemanticAuthority : Set where

matterContextIsNotNewSemanticWorld :
  MatterContextIsNewSemanticWorld → ⊥
matterContextIsNotNewSemanticWorld ()

contextProjectionDoesNotMutateSource :
  ContextProjectionMutatesSource → ⊥
contextProjectionDoesNotMutateSource ()

laterKnowledgeDoesNotRewriteEarlierEpistemicView :
  LaterKnowledgeRewritesEarlierEpistemicView → ⊥
laterKnowledgeDoesNotRewriteEarlierEpistemicView ()

sealedRefDoesNotAppearInOrdinaryProjection :
  SealedRefAppearsInOrdinaryProjection → ⊥
sealedRefDoesNotAppearInOrdinaryProjection ()

notVisibleDoesNotMeanFalse : NotVisibleMeansFalse → ⊥
notVisibleDoesNotMeanFalse ()

notSharedDoesNotMeanAbsentFromWorld :
  NotSharedMeansAbsentFromWorld → ⊥
notSharedDoesNotMeanAbsentFromWorld ()

roleVisibilityDoesNotCreateClaimTruth :
  RoleVisibilityCreatesClaimTruth → ⊥
roleVisibilityDoesNotCreateClaimTruth ()

minimumNecessaryProjectionDoesNotDeleteCanonicalSource :
  MinimumNecessaryProjectionDeletesCanonicalSource → ⊥
minimumNecessaryProjectionDoesNotDeleteCanonicalSource ()

knowledgeCutStringOrderingDoesNotCreateTemporalFact :
  KnowledgeCutStringOrderingCreatesTemporalFact → ⊥
knowledgeCutStringOrderingDoesNotCreateTemporalFact ()

contextAccessGrantDoesNotCreateSemanticAuthority :
  ContextAccessGrantCreatesSemanticAuthority → ⊥
contextAccessGrantDoesNotCreateSemanticAuthority ()

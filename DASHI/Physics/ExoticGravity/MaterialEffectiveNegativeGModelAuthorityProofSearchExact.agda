module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelAuthorityProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelProvenanceBidiExact as Provenance
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- MODEL-ORIGIN-INDEXED AUTHORITY SEARCH
--
-- Imported historical model forms need external source entitlement.  DASHI
-- derived models need exact internal proof lineage.  An unresolved origin must
-- be resolved before either authority route can be selected.
------------------------------------------------------------------------

data ModelAuthorityResidual : Set where
  missingModelOrigin : ModelAuthorityResidual
  missingExternalSourceEntitlement : ModelAuthorityResidual
  missingExternalExactLocator : ModelAuthorityResidual
  missingExternalSameModelFormIdentity : ModelAuthorityResidual
  missingInternalModuleIdentity : ModelAuthorityResidual
  missingInternalTheoremIdentity : ModelAuthorityResidual
  missingInternalScopeIdentity : ModelAuthorityResidual
  authorityContradictionOpen : ModelAuthorityResidual

firstAuthorityResidualForOrigin : Provenance.ModelOrigin → ModelAuthorityResidual
firstAuthorityResidualForOrigin Provenance.importedLiTorrHistoricalClaim =
  missingExternalSourceEntitlement
firstAuthorityResidualForOrigin Provenance.dashiDerivedEffectiveCouplingHypothesis =
  missingInternalModuleIdentity
firstAuthorityResidualForOrigin Provenance.modelOriginUnresolved =
  missingModelOrigin

producerForModelAuthorityResidual :
  ModelAuthorityResidual → Search.ProducerClass
producerForModelAuthorityResidual missingModelOrigin = Search.identityProducer
producerForModelAuthorityResidual missingExternalSourceEntitlement = Search.propositionSourceProducer
producerForModelAuthorityResidual missingExternalExactLocator = Search.discriminatorProducer
producerForModelAuthorityResidual missingExternalSameModelFormIdentity = Search.identityProducer
producerForModelAuthorityResidual missingInternalModuleIdentity = Search.identityProducer
producerForModelAuthorityResidual missingInternalTheoremIdentity = Search.identityProducer
producerForModelAuthorityResidual missingInternalScopeIdentity = Search.discriminatorProducer
producerForModelAuthorityResidual authorityContradictionOpen = Search.contradictionProducer

currentDASHIEffectiveGAuthorityResidual : ModelAuthorityResidual
currentDASHIEffectiveGAuthorityResidual =
  firstAuthorityResidualForOrigin Provenance.dashiDerivedEffectiveCouplingHypothesis

currentDASHIEffectiveGAuthorityStartsAtInternalIdentity :
  currentDASHIEffectiveGAuthorityResidual ≡ missingInternalModuleIdentity
currentDASHIEffectiveGAuthorityStartsAtInternalIdentity = refl

------------------------------------------------------------------------
-- Exact collision: a coarse phrase such as "Li-Torr/effective-G model" cannot
-- determine whether the authority task is external source acquisition or
-- internal theorem-lineage verification.
------------------------------------------------------------------------

data AuthorityFixture : Set where
  importedFixture dashiDerivedFixture : AuthorityFixture

data CoarseModelAuthoritySurface : Set where
  modelNeedsAuthority : CoarseModelAuthoritySurface

coarseObserve : AuthorityFixture → CoarseModelAuthoritySurface
coarseObserve _ = modelNeedsAuthority

fixtureOrigin : AuthorityFixture → Provenance.ModelOrigin
fixtureOrigin importedFixture = Provenance.importedLiTorrHistoricalClaim
fixtureOrigin dashiDerivedFixture = Provenance.dashiDerivedEffectiveCouplingHypothesis

fixtureFirstResidual : AuthorityFixture → ModelAuthorityResidual
fixtureFirstResidual fixture = firstAuthorityResidualForOrigin (fixtureOrigin fixture)

coarseCollision : coarseObserve importedFixture ≡ coarseObserve dashiDerivedFixture
coarseCollision = refl

coarseAuthoritySurfaceDoesNotDetermineProducerTask :
  fixtureFirstResidual importedFixture ≡ fixtureFirstResidual dashiDerivedFixture → ⊥
coarseAuthoritySurfaceDoesNotDetermineProducerTask ()

record ModelAuthorityProofSearchBoundary : Set where
  constructor model-authority-proof-search-boundary
  field
    importedAndInternalModelsUseSameAuthorityProducer : Bool
    importedModelNeedsSourceEntitlement : Bool
    internalModelNeedsFreshExternalCitation : Bool
    internalModelNeedsExactProofLineage : Bool
    unresolvedOriginMaySelectEitherRouteByGuess : Bool
    sourceEntitlementAutomaticallyProvesPhysicalCorrectness : Bool
    proofLineageAutomaticallyProvesPhysicalCorrectness : Bool

canonicalModelAuthorityProofSearchBoundary : ModelAuthorityProofSearchBoundary
canonicalModelAuthorityProofSearchBoundary =
  model-authority-proof-search-boundary false true false true false false false

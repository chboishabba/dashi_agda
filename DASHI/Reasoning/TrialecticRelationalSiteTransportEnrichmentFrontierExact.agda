module DASHI.Reasoning.TrialecticRelationalSiteTransportEnrichmentFrontierExact where

------------------------------------------------------------------------
-- RELATIONAL-SITE TRANSPORT ENRICHMENT FRONTIER
--
-- The existing invertible RelTransportHom family is indexed by exactly the
-- three relational edge patches AB/BC/CA.  The Grothendieck site has seven
-- objects: globalABC, three edges, and three vertices.
--
-- This owner proves that the existing edge-patch transport indexing cannot by
-- itself cover the whole site.  A genuine groupoid-valued presheaf therefore
-- needs new fibre-morphism structure at the global and vertex objects plus
-- restriction functors/coherence; the concrete C3 edge transition must not be
-- silently promoted into that stronger object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.RelationalSelfDescentExact as Existing
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site

------------------------------------------------------------------------
-- 1. Exact coverage supplied by the existing patch index.
------------------------------------------------------------------------

data ExistingTransportCoverage : Site.RelObj → Set where
  coversAB : ExistingTransportCoverage Site.edgeAB
  coversBC : ExistingTransportCoverage Site.edgeBC
  coversCA : ExistingTransportCoverage Site.edgeCA

coveredPatch :
  ∀ {object : Site.RelObj} →
  ExistingTransportCoverage object →
  Existing.RelationalPatch
coveredPatch coversAB = Existing.patchAB
coveredPatch coversBC = Existing.patchBC
coveredPatch coversCA = Existing.patchCA

coveredIdentityHom :
  ∀ {State : Set} {object : Site.RelObj} →
  (coverage : ExistingTransportCoverage object) →
  Groupoid.RelTransportHom
    State
    (coveredPatch coverage)
    (coveredPatch coverage)
coveredIdentityHom coverage =
  Groupoid.identityHom (coveredPatch coverage)

------------------------------------------------------------------------
-- 2. The whole seven-object site is not covered by that index.
------------------------------------------------------------------------

noExistingGlobalCoverage :
  ExistingTransportCoverage Site.globalABC → ⊥
noExistingGlobalCoverage ()

noExistingVertexACoverage :
  ExistingTransportCoverage Site.vertexA → ⊥
noExistingVertexACoverage ()

noExistingVertexBCoverage :
  ExistingTransportCoverage Site.vertexB → ⊥
noExistingVertexBCoverage ()

noExistingVertexCCoverage :
  ExistingTransportCoverage Site.vertexC → ⊥
noExistingVertexCCoverage ()

record ExistingTransportCoversWholeSite : Set where
  constructor existing-transport-covers-whole-site
  field
    coverage : (object : Site.RelObj) → ExistingTransportCoverage object

open ExistingTransportCoversWholeSite public

existingTransportCannotCoverWholeSite :
  ExistingTransportCoversWholeSite → ⊥
existingTransportCannotCoverWholeSite whole =
  noExistingGlobalCoverage (coverage whole Site.globalABC)

------------------------------------------------------------------------
-- 3. Explicit acquisition surface for genuine enrichment.
------------------------------------------------------------------------

record MissingSiteFiberMorphisms : Set₁ where
  field
    GlobalMorphisms : Set
    VertexAMorphisms : Set
    VertexBMorphisms : Set
    VertexCMorphisms : Set

    globalIdentity : GlobalMorphisms
    vertexAIdentity : VertexAMorphisms
    vertexBIdentity : VertexBMorphisms
    vertexCIdentity : VertexCMorphisms

open MissingSiteFiberMorphisms public

-- Merely inhabiting this carrier would still not prove a groupoid-valued
-- presheaf: composition, inverses, restriction functors and coherence remain
-- separate obligations.  The record identifies the first missing carrier cut.

data ExistingEdgeTransportAlreadyIsFullGroupoidValuedPresheaf : Set where

edgeTransportDoesNotAlreadySupplyFullPresheaf :
  ExistingEdgeTransportAlreadyIsFullGroupoidValuedPresheaf → ⊥
edgeTransportDoesNotAlreadySupplyFullPresheaf ()

record TrialecticRelationalSiteTransportEnrichmentBoundary : Set where
  constructor trialectic-relational-site-transport-enrichment-boundary
  field
    threeEdgeObjectsCovered : Bool
    existingTransportCoversAllSiteObjects : Bool
    globalObjectCoveredByExistingPatchIndex : Bool
    vertexObjectsCoveredByExistingPatchIndex : Bool
    newGlobalVertexFiberMorphismsRequired : Bool
    restrictionFunctorCoherenceRequired : Bool
    groupoidValuedPresheafConstructed : Bool
    certifiedHigherStackConstructed : Bool

open TrialecticRelationalSiteTransportEnrichmentBoundary public

canonicalTrialecticRelationalSiteTransportEnrichmentBoundary :
  TrialecticRelationalSiteTransportEnrichmentBoundary
canonicalTrialecticRelationalSiteTransportEnrichmentBoundary =
  trialectic-relational-site-transport-enrichment-boundary
    true
    false
    false
    false
    true
    true
    false
    false

module DASHI.Interop.SLRGWBSupervisedTypeClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBAmbiguityDirected100HopExact as GWB
import DASHI.Interop.SLRExternalOntologyEnrichmentRouterExact as External
import DASHI.Wikimedia.SensibLawNatClimateReviewHandoffExact as NatClimate
import DASHI.Ontology.LeanWikidataSourceSnapshot as LeanSnapshot
import DASHI.Ontology.LeanWikidataFullSourceManifest as LeanManifest

------------------------------------------------------------------------
-- GWB SUPERVISED WIKIDATA TYPE-CLOSURE FALLBACK
--
-- Production runtime:
--   chboishabba/slr
--   branch agent/gwb-supervised-type-closure-v1
--   source-written head fdf2281fa7fa830b1ee4f06dc95f782c603a47fe
--
-- SensibLaw donors:
--   docs/planning/wikidata_nat_cohort_d_type_probing_surface_20260402.md
--   docs/planning/wikidata_pnf_residual_review_example_20260429.md
--
-- Lean semantic reference:
--   chboishabba/dashi_lean4@349f9b7dd49a7f23bfbd7d9da60416afa5440ccf
--   Imported/RequestProject/Wikidata/Core.lean
--     Wikidata.isSubclassOf_iff
--     Wikidata.isInstanceOf_iff
--
-- The Lean theorem says the executable checker is exact RELATIVE TO ITS
-- SUPPLIED KB. It does not certify that a live fetched slice is globally
-- complete, simultaneous, reliable, authoritative or epistemically true.
------------------------------------------------------------------------

slrSupervisedTypeClosureHead : String
slrSupervisedTypeClosureHead =
  "fdf2281fa7fa830b1ee4f06dc95f782c603a47fe"

dashiLean4ReferenceHead : String
dashiLean4ReferenceHead =
  "349f9b7dd49a7f23bfbd7d9da60416afa5440ccf"

leanSubclassExactnessReference : String
leanSubclassExactnessReference =
  "Imported/RequestProject/Wikidata/Core.lean::Wikidata.isSubclassOf_iff"

leanInstanceExactnessReference : String
leanInstanceExactnessReference =
  "Imported/RequestProject/Wikidata/Core.lean::Wikidata.isInstanceOf_iff"

sensibLawNatTypeProbeReference : String
sensibLawNatTypeProbeReference =
  "SensibLaw/docs/planning/wikidata_nat_cohort_d_type_probing_surface_20260402.md"

sensibLawClimateResidualReference : String
sensibLawClimateResidualReference =
  "SensibLaw/docs/planning/wikidata_pnf_residual_review_example_20260429.md"

record SupervisedTypeClosureBoundary : Set where
  constructor supervised-type-closure-boundary
  field
    everyFetchedNodeRevisionPinned : Bool
    aggregateManifestRetainsPerNodeDigests : Bool
    p31SeedsInstanceTypeClosure : Bool
    p279SeedsSuperclassClosure : Bool
    recursiveP279TraversalIsBounded : Bool
    observedDirectSurfaceMayBeCompleteAtPinnedRevision : Bool
    observedAbsenceMeansGlobalAbsence : Bool
    globalOntologyCompletenessClaimed : Bool
    truncationMayPromoteClassification : Bool
    multiRevisionManifestIsSimultaneousSnapshot : Bool
    providerDispositionPaysResidual : Bool
    reviewRequiredForWorldDelta : Bool
    p31OnlyMayCreateInstanceShapedSuperclassPressure : Bool
    instanceShapedPressureIsAutomaticWrongType : Bool
    leanWorkerProvidesExecutableClosureExactness : Bool
    leanWorkerChecksLiveEvidenceAuthority : Bool
    reusesNatObservedAbsenceDiscipline : Bool
    reusesClimateHoldOnDimensionalMismatch : Bool
    providerCandidateOnly : Bool
    providerCreatesSemanticAuthority : Bool
    providerPromotesApplicability : Bool
    providerPromotesClaimTruth : Bool

open SupervisedTypeClosureBoundary public

canonicalSupervisedTypeClosureBoundary : SupervisedTypeClosureBoundary
canonicalSupervisedTypeClosureBoundary =
  supervised-type-closure-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    true
    true
    false
    true
    false
    true
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Existing owners remain authoritative for their own layers.
------------------------------------------------------------------------

gwbCampaignAnchor : GWB.GWB100HopCampaignBoundary
gwbCampaignAnchor = GWB.canonicalGWB100HopCampaign

externalOntologyAnchor : External.ExternalOntologyPolicy
externalOntologyAnchor = External.canonicalExternalOntologyPolicy

natClimateAnchor : NatClimate.NatClimateHandoffBoundary
natClimateAnchor = NatClimate.canonicalNatClimateHandoffBoundary

leanArchiveReference : String
leanArchiveReference = LeanSnapshot.archiveSha256

leanClassAlgebraReference : String
leanClassAlgebraReference = LeanManifest.sha256 LeanManifest.classAlgebraSource

------------------------------------------------------------------------
-- Hard non-collapse laws.
------------------------------------------------------------------------

data ObservedAbsenceEqualsGlobalAbsence : Set where
data BoundedClosureEqualsOntologyCompleteness : Set where
data MultiRevisionManifestEqualsSnapshot : Set where
data LeanClosureExactnessEqualsEvidenceAuthority : Set where
data P31OnlyEqualsWrongTypeFact : Set where
data ProviderDispositionEqualsResidualPayment : Set where
data ProviderCandidateEqualsSemanticTruth : Set where

observedAbsenceDoesNotEqualGlobalAbsence :
  ObservedAbsenceEqualsGlobalAbsence → ⊥
observedAbsenceDoesNotEqualGlobalAbsence ()

boundedClosureDoesNotEqualOntologyCompleteness :
  BoundedClosureEqualsOntologyCompleteness → ⊥
boundedClosureDoesNotEqualOntologyCompleteness ()

multiRevisionManifestDoesNotEqualSnapshot :
  MultiRevisionManifestEqualsSnapshot → ⊥
multiRevisionManifestDoesNotEqualSnapshot ()

leanClosureExactnessDoesNotCreateEvidenceAuthority :
  LeanClosureExactnessEqualsEvidenceAuthority → ⊥
leanClosureExactnessDoesNotCreateEvidenceAuthority ()

p31OnlyDoesNotCreateWrongTypeFact :
  P31OnlyEqualsWrongTypeFact → ⊥
p31OnlyDoesNotCreateWrongTypeFact ()

providerDispositionDoesNotPayResidual :
  ProviderDispositionEqualsResidualPayment → ⊥
providerDispositionDoesNotPayResidual ()

providerCandidateDoesNotCreateTruth :
  ProviderCandidateEqualsSemanticTruth → ⊥
providerCandidateDoesNotCreateTruth ()

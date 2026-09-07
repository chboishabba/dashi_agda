module DASHI.Wikimedia.SensibLawStatementBundleSparseReopenExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as Handoff
import DASHI.Wikimedia.NativeReferenceSemanticsExact as Ref

------------------------------------------------------------------------
-- FULL WIKIDATA STATEMENT-BUNDLE REVIEW UNIT
--
-- SensibLaw Nat/Climate donor:
-- migration review is over main snak + qualifiers + references + rank +
-- provenance, not a naked subject/property/value triple.
--
-- Rust implementation counterpart:
-- chboishabba/slr PR #10, crates/sl-source-handoff/src/bundle.rs
------------------------------------------------------------------------

data BundleCoordinateKind : Set where
  mainSnakCoordinate
  qualifierCoordinate
  referenceCoordinate
  rankCoordinate
  provenanceCoordinate
  : BundleCoordinateKind

record BundleCoordinate : Set where
  constructor bundle-coordinate
  field
    coordinateKind : BundleCoordinateKind
    stableReference : String
open BundleCoordinate public

data NativeRank : Set where
  preferredRank normalRank deprecatedRank unresolvedRank : NativeRank

record StatementBundleReview : Set where
  constructor statement-bundle-review
  field
    bundleId : String
    sourceUnitId : String
    subjectQid : Id.ItemId
    propertyId : Id.PropertyId
    mainSnakReference : String
    qualifierReferences : List String
    referenceReferences : List String
    rank : NativeRank
    provenanceReferences : List String
    disposition : Handoff.MigrationDisposition
    unresolvedReasons : List String
    createsWorldTruth : Bool
    createsWorldTruthIsFalse : createsWorldTruth ≡ false
    ownsSourceAuthority : Bool
    ownsSourceAuthorityIsFalse : ownsSourceAuthority ≡ false
    ownsSemanticPromotion : Bool
    ownsSemanticPromotionIsFalse : ownsSemanticPromotion ≡ false
open StatementBundleReview public

------------------------------------------------------------------------
-- Bounded Nat calibration.
------------------------------------------------------------------------

natBundle : StatementBundleReview
natBundle =
  statement-bundle-review
    "bundle:nat:q10403939:scope1:2018"
    "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"
    (Id.itemId "Q10403939")
    (Id.propertyId "P5991")
    "quantity:scope1:2018"
    ("P3831:scope1" ∷ "P459:ghg-protocol" ∷ "P580:2018" ∷ [])
    ("P854:https://example.test/report.pdf" ∷ [])
    normalRank
    ("source-unit:nat-p5991-p14143" ∷ [])
    Handoff.splitRequired
    ("scope/time decomposition unresolved" ∷ [])
    false refl
    false refl
    false refl

natBundleRemainsSplitRequired :
  disposition natBundle ≡ Handoff.splitRequired
natBundleRemainsSplitRequired = refl

------------------------------------------------------------------------
-- Finer coordinates preserve bundle-local invalidation targets.
------------------------------------------------------------------------

natMainSnak : BundleCoordinate
natMainSnak = bundle-coordinate mainSnakCoordinate "bundle:nat:q10403939:scope1:2018:quantity:scope1:2018"

natP459Qualifier : BundleCoordinate
natP459Qualifier = bundle-coordinate qualifierCoordinate "bundle:nat:q10403939:scope1:2018:P459:ghg-protocol"

natP854Reference : BundleCoordinate
natP854Reference = bundle-coordinate referenceCoordinate "bundle:nat:q10403939:scope1:2018:P854:https://example.test/report.pdf"

natRank : BundleCoordinate
natRank = bundle-coordinate rankCoordinate "bundle:nat:q10403939:scope1:2018:normal"

natProvenance : BundleCoordinate
natProvenance = bundle-coordinate provenanceCoordinate "bundle:nat:q10403939:scope1:2018:source-unit:nat-p5991-p14143"

------------------------------------------------------------------------
-- Typed dependency graph return.
------------------------------------------------------------------------

bundleCoordinateNode : BundleCoordinate → Graph.DependencyNode
bundleCoordinateNode coordinate =
  Graph.dependencyNode
    (stableReference coordinate)
    Graph.wikidataData
    "Wikidata statement-bundle review coordinate"
    false

referenceTransferConsumer : Graph.DependencyNode
referenceTransferConsumer =
  Graph.dependencyNode
    "consumer:nat-reference-transfer"
    Graph.dashiFormal
    "reviews transfer/preservation of source reference structure"
    false

semanticEquivalenceConsumer : Graph.DependencyNode
semanticEquivalenceConsumer =
  Graph.dependencyNode
    "consumer:nat-semantic-equivalence"
    Graph.dashiFormal
    "reviews mainsnak/property semantic equivalence"
    false

p854ReferenceDependency : Graph.DependencyEdge
p854ReferenceDependency =
  Graph.dependencyEdge
    (bundleCoordinateNode natP854Reference)
    referenceTransferConsumer
    Graph.evidenceRole
    true
    "reference-transfer consumer declares exact dependency on the P854 bundle coordinate"

mainSnakSemanticDependency : Graph.DependencyEdge
mainSnakSemanticDependency =
  Graph.dependencyEdge
    (bundleCoordinateNode natMainSnak)
    semanticEquivalenceConsumer
    Graph.definitionRole
    true
    "semantic-equivalence consumer declares dependency on the mainsnak coordinate"

record SparseBundleWake : Set where
  constructor sparse-bundle-wake
  field
    changedCoordinate : BundleCoordinate
    dependency : Graph.DependencyEdge
    exactSource : Graph.sourceNode dependency ≡ bundleCoordinateNode changedCoordinate
    required : Graph.requiredForTarget dependency ≡ true
    wokenConsumer : Graph.DependencyNode
    exactTarget : wokenConsumer ≡ Graph.targetNode dependency
    wakeReference : String
open SparseBundleWake public

p854ChangeWakesReferenceTransfer : SparseBundleWake
p854ChangeWakesReferenceTransfer =
  sparse-bundle-wake
    natP854Reference
    p854ReferenceDependency
    refl
    refl
    referenceTransferConsumer
    refl
    "SLR PR #10 sparse_wake_bundle_changes reference-coordinate calibration"

------------------------------------------------------------------------
-- Selective reopening firewalls.
------------------------------------------------------------------------

data ChangedReferenceWakesEveryBundleConsumer : Set where
data MissingDependencyMeansNegativeEvidence : Set where
data StatementBundleEqualsNakedTriple : Set where
data SplitRequiredMeansSourceFalse : Set where
data BundleReviewCreatesPromotion : Set where

changedReferenceDoesNotWakeEveryBundleConsumer :
  ChangedReferenceWakesEveryBundleConsumer → ⊥
changedReferenceDoesNotWakeEveryBundleConsumer ()

missingDependencyDoesNotMeanNegativeEvidence :
  MissingDependencyMeansNegativeEvidence → ⊥
missingDependencyDoesNotMeanNegativeEvidence ()

statementBundleDoesNotCollapseToNakedTriple :
  StatementBundleEqualsNakedTriple → ⊥
statementBundleDoesNotCollapseToNakedTriple ()

splitRequiredDoesNotMeanSourceFalse : SplitRequiredMeansSourceFalse → ⊥
splitRequiredDoesNotMeanSourceFalse ()

bundleReviewDoesNotCreatePromotion : BundleReviewCreatesPromotion → ⊥
bundleReviewDoesNotCreatePromotion ()

record StatementBundleSparseReopenBoundary : Set where
  constructor statement-bundle-sparse-reopen-boundary
  field
    fullBundleIsReviewUnit : Bool
    coordinatesRemainSeparatelyAddressable : Bool
    changedReferenceWakesAllConsumers : Bool
    missingDependencyIsNegativeEvidence : Bool
    bundleReviewCreatesAuthority : Bool
    sparseWakeReusesTypedDependencyGraph : Bool

canonicalStatementBundleSparseReopenBoundary : StatementBundleSparseReopenBoundary
canonicalStatementBundleSparseReopenBoundary =
  statement-bundle-sparse-reopen-boundary true true false false false true

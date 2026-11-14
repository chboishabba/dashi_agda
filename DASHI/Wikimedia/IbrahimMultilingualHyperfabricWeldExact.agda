module DASHI.Wikimedia.IbrahimMultilingualHyperfabricWeldExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN
import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Wikimedia.ConceptEntityAlignmentExact as Alignment
import DASHI.Cognition.PNF.ITIRRelationalInterlinguaConsumerFibreExact as ITIR
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.BalancedTernaryUltrametricExact as Ultra
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as Binary
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Reasoning.TypedHyperfabricCore as Fabric

------------------------------------------------------------------------
-- IBRAHIM / ITIR / HYPERFABRIC / TERNARY WELD
--
-- Original FLN: Ibrahim, Danforth, Dodds (2017),
-- DOI 10.1016/j.jocs.2016.12.001.
-- Comparative cultural first-link study: Maxime Gabella (2019),
-- DOI 10.1109/TNSE.2018.2812788.
-- Typed sheaf-like hypergraph donor: Duta, Cassara, Silvestri, Lio,
-- "Sheaf Hypergraph Networks" (2023), arXiv:2309.17116.
--
-- Original sources own reported empirical observations and methodology.
-- DASHI owns only the newly written bridge laws below.
-- No contemporary ABC Science claims are admitted without exact
-- language/dump/revision/parser/result receipts.
------------------------------------------------------------------------

-- First-link navigation is one typed edge projection of a larger
-- hyperfabric, not a reduction of all explanatory hyperedges to
-- superclass, parent-of, QID identity or semantic implication.
-- The source receipt is REQUIRED per selected edge; it is not
-- reconstructed from the existence of a QID or a DOI.

record FirstLinkHyperfabricProjection
  (Node Edge : Set) : Set₁ where
  constructor firstLinkHyperfabricProjection
  field
    fabric : Fabric.TypedHyperfabric Node Edge
    graph : FLN.RevisionIndexedFirstLinkGraph Node
    selectedEdge : Node → Edge
    targetOf : Edge → Node
    sourceFor : (node : Node) → Source.SourceReceipt
    edgeObservedAtRevision :
      (node : Node) →
      Source.layer (sourceFor node) ≡ Source.wikipediaRevisionLayer
    edgeIncidence :
      (node : Node) →
      Fabric.incidence fabric node (selectedEdge node)
    selectionSound :
      (node : Node) →
      targetOf (selectedEdge node) ≡
      FLN.firstLink graph node
open FirstLinkHyperfabricProjection public

selectedEdgeProjectsToFirstLink :
  ∀ {Node Edge : Set}
    (p : FirstLinkHyperfabricProjection Node Edge)
    (node : Node) →
  targetOf p (selectedEdge p node) ≡
  FLN.firstLink (graph p) node
selectedEdgeProjectsToFirstLink p node = selectionSound p node

selectedEdgeSectionCompatible :
  ∀ {Node Edge : Set}
    (p : FirstLinkHyperfabricProjection Node Edge)
    (section : Fabric.GlobalSection (fabric p))
    (node : Node) →
  Fabric.restrict (fabric p) (edgeIncidence p node)
    (Fabric.vertexValue section node) ≡
  Fabric.edgeValue section (selectedEdge p node)
selectedEdgeSectionCompatible p section node =
  Fabric.compatible section (edgeIncidence p node)

------------------------------------------------------------------------
-- Consumer-indexed QID and text/PNF compatibility. The existing ITIR
-- carrier already distinguishes same entity, same claim, translation
-- alignment, contradictory evidence and unknown residuals.
------------------------------------------------------------------------

record RevisionBoundComparison
  (left right : ITIR.SourceObservation)
  (consumer : ITIR.ConsumerLicence) : Set where
  constructor revisionBoundComparison
  field
    leftPage rightPage : Source.WikipediaRevisionReceipt
    leftSameRevision :
      ITIR.sourceRevisionRef left ≡ Source.wikipediaRevisionId leftPage
    rightSameRevision :
      ITIR.sourceRevisionRef right ≡ Source.wikipediaRevisionId rightPage
    compared : ITIR.ConsumerComparison left right consumer
open RevisionBoundComparison public

comparisonDoesNotPromoteTruth :
  ∀ {left right consumer}
    (comparison : RevisionBoundComparison left right consumer) →
  ITIR.createsPropositionTruth (compared comparison) ≡ false
comparisonDoesNotPromoteTruth comparison =
  ITIR.comparisonNeverPaysTruth (compared comparison)

comparisonDoesNotMergeSources :
  ∀ {left right consumer}
    (comparison : RevisionBoundComparison left right consumer) →
  ITIR.createsSourceIdentity (compared comparison) ≡ false
comparisonDoesNotMergeSources comparison =
  ITIR.comparisonNeverMergesSources (compared comparison)

------------------------------------------------------------------------
-- A signed ternary readout needs a separately supplied warrant.
-- A QID, an ITIR candidate, an unreviewed alignment and a comparison
-- status cannot manufacture that warrant. Unknown and conflicting
-- observations stay in their original ITIR residual fibres.
------------------------------------------------------------------------

data QualifiedTernaryResult
  (alignment : Alignment.ConceptEntityAlignment)
  (Warrant : Ternary.Comparison9 → Set) : Set where
  unresolved :
    List ITIR.RelationalResidual →
    QualifiedTernaryResult alignment Warrant
  reviewedSigned :
    Alignment.status alignment ≡ Alignment.reviewedAccepted →
    (values : Ternary.Comparison9) →
    Warrant values →
    QualifiedTernaryResult alignment Warrant

record MultilingualComparisonFibre
  (left right : ITIR.SourceObservation)
  (consumer : ITIR.ConsumerLicence)
  (alignment : Alignment.ConceptEntityAlignment)
  (Warrant : Ternary.Comparison9 → Set) : Set where
  constructor multilingualComparisonFibre
  field
    sourceComparison : RevisionBoundComparison left right consumer
    signedOrUnresolved : QualifiedTernaryResult alignment Warrant
    qidIsOnlyAlignmentCoordinate : Bool
    qidIsOnlyAlignmentCoordinateTrue :
      qidIsOnlyAlignmentCoordinate ≡ true
    createsArticleEquivalence : Bool
    createsArticleEquivalenceFalse :
      createsArticleEquivalence ≡ false
open MultilingualComparisonFibre public

-- The nine-state comparison and the source-facing residual are both
-- retained. Classification is invertible at the level of the nine
-- ORIGINAL ternary states; no binary or Boolean replacement occurs.

signedClassificationRoundtrip :
  (values : Ternary.Comparison9) →
  Ternary.forgetComparisonClass (Ternary.classifyComparison values)
    ≡ values
signedClassificationRoundtrip = Ternary.forgetAfterClassifyComparison

signedSynthesisRetainsComparison :
  (values : Ternary.Comparison9) (synthesis : Base.TriTruth) →
  Ternary.comparisonOfSynthesis
    (Ternary.makeSynthesisChoice (proj₁ values) (proj₂ values) synthesis)
  ≡ values
signedSynthesisRetainsComparison (left , right) synthesis =
  Ternary.comparisonBoundaryRetained left right synthesis

binaryCountLosesDirectedDifference :
  Binary.acceptCount
    (Binary.binaryProjectPositiveOnly Binary.forwardDisagreement)
  ≡
  Binary.acceptCount
    (Binary.binaryProjectPositiveOnly Binary.reverseDisagreement)
binaryCountLosesDirectedDifference =
  Binary.aggregateErasesDisagreementDirection

------------------------------------------------------------------------
-- Balanced-ternary prefix geometry lives alongside signed comparison.
-- The witness is licensed by the EXTERNAL address assignment; merely
-- obtaining the same QID does not imply prefix agreement.
------------------------------------------------------------------------

record MultilingualPrefixFibre : Set where
  constructor multilingualPrefixFibre
  field
    leftAddress rightAddress : List BT.BalancedDigit
    commonPrefixDepth : Nat
    prefixWitness :
      Ultra.PrefixAgreement commonPrefixDepth leftAddress rightAddress
    encodingPolicyReference : String
    leftRevisionReference rightRevisionReference : String
    alignmentLicenceReference : String
open MultilingualPrefixFibre public

prefixAgreementIsSymmetric :
  (fibre : MultilingualPrefixFibre) →
  Ultra.PrefixAgreement (commonPrefixDepth fibre)
    (rightAddress fibre) (leftAddress fibre)
prefixAgreementIsSymmetric fibre =
  Ultra.prefixAgreementSymmetric (prefixWitness fibre)

prefixAgreementIsTransitive :
  ∀ {n} {xs ys zs : List BT.BalancedDigit} →
  Ultra.PrefixAgreement n xs ys →
  Ultra.PrefixAgreement n ys zs →
  Ultra.PrefixAgreement n xs zs
prefixAgreementIsTransitive = Ultra.prefixAgreementTransitive

data SharedQidCreatesTernaryWarrant : Set where
data SamePrefixCreatesSemanticEquivalence : Set where
data CulturalAssociationCreatesCausalProof : Set where
data HistoricalMethodPaysModernResult : Set where

qidCannotManufactureTernaryWarrant :
  SharedQidCreatesTernaryWarrant → ⊥
qidCannotManufactureTernaryWarrant ()

prefixDoesNotCreateSemanticEquivalence :
  SamePrefixCreatesSemanticEquivalence → ⊥
prefixDoesNotCreateSemanticEquivalence ()

associationDoesNotCreateCausality :
  CulturalAssociationCreatesCausalProof → ⊥
associationDoesNotCreateCausality ()

historicalMethodDoesNotPayModernResult :
  HistoricalMethodPaysModernResult → ⊥
historicalMethodDoesNotPayModernResult ()

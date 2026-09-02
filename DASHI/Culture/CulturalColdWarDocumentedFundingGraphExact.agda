module DASHI.Culture.CulturalColdWarDocumentedFundingGraphExact where

open import DASHI.Core.Prelude

import DASHI.Culture.CulturalColdWarSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- DOCUMENTED HISTORICAL GRAPH
--
-- Only source-backed edges are constructors.  In particular there is no
-- constructor from CIA/CCF into MoMA or its International Program in this
-- fixture.  Absence here means "not derivable from the currently admitted
-- source graph", not a universal historical impossibility claim.
------------------------------------------------------------------------

data HistoricalActor : Set where
  cia
  congressForCulturalFreedom
  rockefellerBrothersFund
  museumOfModernArt
  momaInternationalProgram
  : HistoricalActor

data HistoricalExhibition : Set where
  newAmericanPainting1958to1959 : HistoricalExhibition

data HistoricalMovement : Set where
  abstractExpressionism : HistoricalMovement

data DocumentedFundingEdge : HistoricalActor → HistoricalActor → Set where
  ciaFundsCCF :
    DocumentedFundingEdge cia congressForCulturalFreedom
  rockefellerFundsInternationalProgram :
    DocumentedFundingEdge rockefellerBrothersFund momaInternationalProgram

infixr 5 _then_
data DocumentedFundingPath : HistoricalActor → HistoricalActor → Set where
  pathHere : ∀ {actor} → DocumentedFundingPath actor actor
  _then_ : ∀ {source middle target} →
    DocumentedFundingEdge source middle →
    DocumentedFundingPath middle target →
    DocumentedFundingPath source target

ciaToCCFPath : DocumentedFundingPath cia congressForCulturalFreedom
ciaToCCFPath = ciaFundsCCF then pathHere

rockefellerToInternationalProgramPath :
  DocumentedFundingPath rockefellerBrothersFund momaInternationalProgram
rockefellerToInternationalProgramPath =
  rockefellerFundsInternationalProgram then pathHere

------------------------------------------------------------------------
-- Exhibition and movement observations are separate relations.
------------------------------------------------------------------------

data OrganisedBy : HistoricalExhibition → HistoricalActor → Set where
  newAmericanPaintingOrganisedByInternationalProgram :
    OrganisedBy newAmericanPainting1958to1959 momaInternationalProgram

data MovementCirculatedBy : HistoricalMovement → HistoricalActor → Set where
  abstractExpressionismCirculatedByInternationalProgram :
    MovementCirculatedBy abstractExpressionism momaInternationalProgram

------------------------------------------------------------------------
-- Source receipts stay attached to the exact graph facts they motivate.
------------------------------------------------------------------------

record SourcedCIAtoCCFReceipt : Set where
  constructor sourced-cia-to-ccf-receipt
  field
    source : Atlas.HistoricalSourceClaim
    edge : DocumentedFundingEdge cia congressForCulturalFreedom

canonicalSourcedCIAtoCCFReceipt : SourcedCIAtoCCFReceipt
canonicalSourcedCIAtoCCFReceipt =
  sourced-cia-to-ccf-receipt Atlas.ciaCCFSource ciaFundsCCF

record SourcedRockefellerInternationalProgramReceipt : Set where
  constructor sourced-rockefeller-international-program-receipt
  field
    source : Atlas.HistoricalSourceClaim
    edge : DocumentedFundingEdge rockefellerBrothersFund momaInternationalProgram

canonicalSourcedRockefellerInternationalProgramReceipt :
  SourcedRockefellerInternationalProgramReceipt
canonicalSourcedRockefellerInternationalProgramReceipt =
  sourced-rockefeller-international-program-receipt
    Atlas.momaInternationalProgramFundingSource
    rockefellerFundsInternationalProgram

record SourcedNewAmericanPaintingOrganisationReceipt : Set where
  constructor sourced-new-american-painting-organisation-receipt
  field
    source : Atlas.HistoricalSourceClaim
    organised : OrganisedBy newAmericanPainting1958to1959 momaInternationalProgram

canonicalSourcedNewAmericanPaintingOrganisationReceipt :
  SourcedNewAmericanPaintingOrganisationReceipt
canonicalSourcedNewAmericanPaintingOrganisationReceipt =
  sourced-new-american-painting-organisation-receipt
    Atlas.newAmericanPaintingSource
    newAmericanPaintingOrganisedByInternationalProgram

record SourcedAbstractExpressionismCirculationReceipt : Set where
  constructor sourced-abstract-expressionism-circulation-receipt
  field
    source : Atlas.HistoricalSourceClaim
    circulated : MovementCirculatedBy abstractExpressionism momaInternationalProgram

canonicalSourcedAbstractExpressionismCirculationReceipt :
  SourcedAbstractExpressionismCirculationReceipt
canonicalSourcedAbstractExpressionismCirculationReceipt =
  sourced-abstract-expressionism-circulation-receipt
    Atlas.momaAbExInternationalProgramSource
    abstractExpressionismCirculatedByInternationalProgram

------------------------------------------------------------------------
-- Exact non-derivability in this admitted graph.
------------------------------------------------------------------------

ccfCannotReachInternationalProgramInDeclaredFundingGraph :
  DocumentedFundingPath congressForCulturalFreedom momaInternationalProgram → ⊥
ccfCannotReachInternationalProgramInDeclaredFundingGraph ()

ciaCannotReachInternationalProgramInDeclaredFundingGraph :
  DocumentedFundingPath cia momaInternationalProgram → ⊥
ciaCannotReachInternationalProgramInDeclaredFundingGraph
  (ciaFundsCCF then rest) =
  ccfCannotReachInternationalProgramInDeclaredFundingGraph rest

ciaCannotReachMoMAInDeclaredFundingGraph :
  DocumentedFundingPath cia museumOfModernArt → ⊥
ciaCannotReachMoMAInDeclaredFundingGraph
  (ciaFundsCCF then ())

------------------------------------------------------------------------
-- No-promotion claims: graph adjacency does not manufacture missing edges.
------------------------------------------------------------------------

data SharedColdWarContextCreatesFundingEdge : Set where
data CCFandMoMAActivityCreatesFundingPath : Set where
data AbstractExpressionistCirculationCreatesCIAFundingPath : Set where

sharedContextDoesNotCreateFundingEdge :
  SharedColdWarContextCreatesFundingEdge → ⊥
sharedContextDoesNotCreateFundingEdge ()

ccfAndMoMAActivityDoesNotCreateFundingPath :
  CCFandMoMAActivityCreatesFundingPath → ⊥
ccfAndMoMAActivityDoesNotCreateFundingPath ()

abstractExpressionistCirculationDoesNotCreateCIAFundingPath :
  AbstractExpressionistCirculationCreatesCIAFundingPath → ⊥
abstractExpressionistCirculationDoesNotCreateCIAFundingPath ()

record CulturalColdWarDocumentedFundingGraphBoundary : Set where
  constructor cultural-cold-war-documented-funding-graph-boundary
  field
    ciaToCCFEdgeOwned : Bool
    rockefellerToInternationalProgramEdgeOwned : Bool
    internationalProgramOrganisesNewAmericanPainting : Bool
    internationalProgramCirculatesAbstractExpressionism : Bool
    ciaToInternationalProgramPathDerivableHere : Bool
    ciaToMoMAPathDerivableHere : Bool
    missingEdgeMayBeCreatedBySharedContext : Bool
    nonDerivabilityIsUniversalHistoricalImpossibilityClaim : Bool

canonicalCulturalColdWarDocumentedFundingGraphBoundary :
  CulturalColdWarDocumentedFundingGraphBoundary
canonicalCulturalColdWarDocumentedFundingGraphBoundary =
  cultural-cold-war-documented-funding-graph-boundary
    true true true true false false false false

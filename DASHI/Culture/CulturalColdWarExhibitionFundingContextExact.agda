module DASHI.Culture.CulturalColdWarExhibitionFundingContextExact where

open import DASHI.Core.Prelude

import DASHI.Culture.CulturalColdWarDocumentedFundingGraphExact as Graph

------------------------------------------------------------------------
-- SAME-EXHIBITION FUNDING CONTEXT
--
-- This owner composes only already-admitted graph facts.  It does not add new
-- historical edges.  The selected exhibition remains literal throughout.
------------------------------------------------------------------------

record ExhibitionFundingContext
    (exhibition : Graph.HistoricalExhibition)
    (sponsor organiser : Graph.HistoricalActor) : Set where
  constructor exhibition-funding-context
  field
    fundingPath : Graph.DocumentedFundingPath sponsor organiser
    organisedBy : Graph.OrganisedBy exhibition organiser

open ExhibitionFundingContext public

newAmericanPaintingRockefellerContext :
  ExhibitionFundingContext
    Graph.newAmericanPainting1958to1959
    Graph.rockefellerBrothersFund
    Graph.momaInternationalProgram
newAmericanPaintingRockefellerContext =
  exhibition-funding-context
    Graph.rockefellerToInternationalProgramPath
    Graph.newAmericanPaintingOrganisedByInternationalProgram

------------------------------------------------------------------------
-- The analogous CIA context cannot be constructed from this declared graph.
------------------------------------------------------------------------

newAmericanPaintingCIAContextNotDerivableHere :
  ExhibitionFundingContext
    Graph.newAmericanPainting1958to1959
    Graph.cia
    Graph.momaInternationalProgram → ⊥
newAmericanPaintingCIAContextNotDerivableHere context =
  Graph.ciaCannotReachInternationalProgramInDeclaredFundingGraph
    (fundingPath context)

------------------------------------------------------------------------
-- Movement circulation can be paired with the same organising institution,
-- but this pairing still cannot manufacture a CIA funding path.
------------------------------------------------------------------------

record ExhibitionMovementContext
    (exhibition : Graph.HistoricalExhibition)
    (movement : Graph.HistoricalMovement)
    (organiser : Graph.HistoricalActor) : Set where
  constructor exhibition-movement-context
  field
    organised : Graph.OrganisedBy exhibition organiser
    circulated : Graph.MovementCirculatedBy movement organiser

open ExhibitionMovementContext public

newAmericanPaintingAbstractExpressionismContext :
  ExhibitionMovementContext
    Graph.newAmericanPainting1958to1959
    Graph.abstractExpressionism
    Graph.momaInternationalProgram
newAmericanPaintingAbstractExpressionismContext =
  exhibition-movement-context
    Graph.newAmericanPaintingOrganisedByInternationalProgram
    Graph.abstractExpressionismCirculatedByInternationalProgram

record RockefellerFundedAbstractExpressionistExhibitionContext : Set where
  constructor rockefeller-funded-abstract-expressionist-exhibition-context
  field
    funding :
      ExhibitionFundingContext
        Graph.newAmericanPainting1958to1959
        Graph.rockefellerBrothersFund
        Graph.momaInternationalProgram
    movement :
      ExhibitionMovementContext
        Graph.newAmericanPainting1958to1959
        Graph.abstractExpressionism
        Graph.momaInternationalProgram

canonicalRockefellerFundedAbstractExpressionistExhibitionContext :
  RockefellerFundedAbstractExpressionistExhibitionContext
canonicalRockefellerFundedAbstractExpressionistExhibitionContext =
  rockefeller-funded-abstract-expressionist-exhibition-context
    newAmericanPaintingRockefellerContext
    newAmericanPaintingAbstractExpressionismContext

------------------------------------------------------------------------
-- Explicit interpretation boundary.
------------------------------------------------------------------------

data RockefellerContextCreatesCIAContext : Set where
data SameMovementCreatesSameFundingProvenance : Set where

data HistoricalAdjacencyCreatesMissingEdge : Set where

rockefellerContextDoesNotCreateCIAContext :
  RockefellerContextCreatesCIAContext → ⊥
rockefellerContextDoesNotCreateCIAContext ()

sameMovementDoesNotCreateSameFundingProvenance :
  SameMovementCreatesSameFundingProvenance → ⊥
sameMovementDoesNotCreateSameFundingProvenance ()

historicalAdjacencyDoesNotCreateMissingEdge :
  HistoricalAdjacencyCreatesMissingEdge → ⊥
historicalAdjacencyDoesNotCreateMissingEdge ()

record CulturalColdWarExhibitionFundingContextBoundary : Set where
  constructor cultural-cold-war-exhibition-funding-context-boundary
  field
    sameExhibitionRockefellerContextConstructed : Bool
    sameExhibitionAbstractExpressionismContextConstructed : Bool
    ciaContextDerivableFromDeclaredGraph : Bool
    sharedMovementDeterminesFundingProvenance : Bool
    historicalAdjacencyCreatesMissingFundingEdge : Bool

canonicalCulturalColdWarExhibitionFundingContextBoundary :
  CulturalColdWarExhibitionFundingContextBoundary
canonicalCulturalColdWarExhibitionFundingContextBoundary =
  cultural-cold-war-exhibition-funding-context-boundary
    true true false false false

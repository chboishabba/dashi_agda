module DASHI.Ontology.WikidataWorkingGroupEntityScopeRegression where

------------------------------------------------------------------------
-- FOCUSED WIKIDATA WORKING-GROUP REGRESSION
--
-- Exercises the concrete distinctions raised in the 19 Aug 2026 ontology
-- working-group discussion without pulling the whole governance synthesis into
-- the public-facing ontology surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Ontology.WikidataBFOEntityScopeExact as BFO
import DASHI.Ontology.WikidataHigherOrderFictionContextExact as Higher

------------------------------------------------------------------------
-- BFO / Wikidata entity root.
------------------------------------------------------------------------

sameEntityEnglishLabel :
  BFO.rootLabel BFO.wikidataEntityQ35120
  ≡ BFO.rootLabel BFO.bfoEntityQ136433660
sameEntityEnglishLabel = BFO.entityLabelsCoincide

sameEntityLabelDoesNotDetermineScope :
  BFO.LabelOnlyScopeDecoder → ⊥
sameEntityLabelDoesNotDetermineScope =
  BFO.sameEntityLabelCannotDetermineBothScopes

bfoClassIdIsIdentifierStrengthOnly :
  BFO.supportsLanguage
    BFO.p12602BFOClassIdentifier
    BFO.identifierLookup
  ≡ true
bfoClassIdIsIdentifierStrengthOnly =
  BFO.p12602LicensesIdentifierLookup

bfoClassIdDoesNotMintSemanticEquivalence :
  BFO.supportsLanguage
    BFO.p12602BFOClassIdentifier
    BFO.semanticInterchange
  ≡ false
bfoClassIdDoesNotMintSemanticEquivalence =
  BFO.p12602DoesNotLicenseSemanticInterchange

exactMatchAndEquivalentClassRemainDifferentStrengths :
  BFO.supportsLanguage BFO.p2888ExactMatch BFO.classEquivalence
  ≡ false
exactMatchAndEquivalentClassRemainDifferentStrengths =
  BFO.p2888DoesNotBecomeEquivalentClassByType

noSingleBfoLinkLicensesDisjointnessTransport :
  (kind : BFO.BFOLinkKind) →
  BFO.supportsLanguage kind BFO.disjointnessTransport ≡ false
noSingleBfoLinkLicensesDisjointnessTransport =
  BFO.noSingleListedLinkLicensesDisjointnessTransport

------------------------------------------------------------------------
-- Higher-order / fictional scope.
------------------------------------------------------------------------

sameSecondOrderSurface :
  Higher.classOrder Higher.editorialSecondOrderState
  ≡ Higher.classOrder Higher.inWorldSecondOrderState
sameSecondOrderSurface = Higher.sameClassOrder

sameFictionalSecondOrderLabel :
  Higher.publicLabel Higher.editorialSecondOrderState
  ≡ Higher.publicLabel Higher.inWorldSecondOrderState
sameFictionalSecondOrderLabel = Higher.samePublicLabel

secondOrderDoesNotDetermineNarrativeDomain :
  Higher.OrderOnlyNarrativeDecoder → ⊥
secondOrderDoesNotDetermineNarrativeDomain =
  Higher.classOrderCannotDetermineNarrativeDomain

fictionalSecondOrderLabelDoesNotDetermineNarrativeDomain :
  Higher.LabelOnlyNarrativeDecoder → ⊥
fictionalSecondOrderLabelDoesNotDetermineNarrativeDomain =
  Higher.publicLabelCannotDetermineNarrativeDomain

classOrderCannotDetermineInspectionDecision :
  Higher.OrderOnlyDecisionDecoder → ⊥
classOrderCannotDetermineInspectionDecision =
  Higher.inspectionDecisionNotFactorableThroughClassOrder

record WorkingGroupEntityScopeBoundary : Set where
  constructor workingGroupEntityScopeBoundary
  field
    sameLabelMeansSameOntologyScope : Bool
    bfoIdentifierMeansExactMatch : Bool
    exactMatchMeansEquivalentClass : Bool
    secondOrderMeansFictional : Bool
    fictionalSecondOrderIsOneSemanticAtom : Bool
    outOfScopeMeansFalse : Bool
    keepOrderDomainApplicabilityOrthogonal : Bool

canonicalWorkingGroupEntityScopeBoundary : WorkingGroupEntityScopeBoundary
canonicalWorkingGroupEntityScopeBoundary =
  workingGroupEntityScopeBoundary
    false false false false false false true

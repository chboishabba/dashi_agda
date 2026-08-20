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
import DASHI.Ontology.WikidataBFOMappingInferenceLatticeExact as Mapping
import DASHI.Ontology.WikidataBFOApplicabilityFibreExact as Applicability
import DASHI.Ontology.WikidataBFOEntityRootMappingDiagnosticExact as Diagnostic
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
-- Query-indexed mapping inference: there is no one scalar strength order.
------------------------------------------------------------------------

p2888AndP1709AreQueryIncomparable₁ :
  Mapping.LicenceProfile.semanticInterchange
    (Mapping.profile BFO.p2888ExactMatch) ≡ true
  × Mapping.LicenceProfile.semanticInterchange
    (Mapping.profile BFO.p1709EquivalentClass) ≡ false
p2888AndP1709AreQueryIncomparable₁ =
  Mapping.p2888HasInterchangeWhereP1709DoesNot

p2888AndP1709AreQueryIncomparable₂ :
  Mapping.LicenceProfile.classEquivalence
    (Mapping.profile BFO.p1709EquivalentClass) ≡ true
  × Mapping.LicenceProfile.classEquivalence
    (Mapping.profile BFO.p2888ExactMatch) ≡ false
p2888AndP1709AreQueryIncomparable₂ =
  Mapping.p1709HasClassEquivalenceWhereP2888DoesNot

noSingleMappingPropertyCarriesFullClassAlgebra :
  (kind : BFO.BFOLinkKind) →
  Mapping.FullClassAlgebraLicence kind → ⊥
noSingleMappingPropertyCarriesFullClassAlgebra =
  Mapping.noSingleLinkHasFullClassAlgebraLicence

------------------------------------------------------------------------
-- Q35120 / Q136433660 ambiguity is attribution-local, not ontology refutation.
------------------------------------------------------------------------

canonicalRootPacketIsNotUniquelyResolved :
  Diagnostic.UniqueResolvedRoot Diagnostic.canonicalRootMappingPacket → ⊥
canonicalRootPacketIsNotUniquelyResolved =
  Diagnostic.canonicalPacketHasNoUniqueResolvedRoot

rootPacketFinalStatusIsUnresolved :
  Diagnostic.LayeredRootDiagnostic.finalStatus
    Diagnostic.canonicalLayeredRootDiagnostic
  ≡ Diagnostic.unresolved
rootPacketFinalStatusIsUnresolved =
  Diagnostic.ambiguousPacketRemainsUnresolved

transcriptionAmbiguityDoesNotRefuteSourceOntology :
  Diagnostic.LayeredRootDiagnostic.sourceOntologyStatus
    Diagnostic.canonicalLayeredRootDiagnostic
  ≡ Diagnostic.verified
transcriptionAmbiguityDoesNotRefuteSourceOntology =
  Diagnostic.transcriptionAmbiguityDoesNotBecomeSourceRefutation

------------------------------------------------------------------------
-- Applicability / non-binary evaluation ladder.
------------------------------------------------------------------------

frodoReferentSurvivesWikidataToBFOInspection :
  Applicability.referent Applicability.frodoWikidataInspection
  ≡ Applicability.referent Applicability.frodoBFOEntityInspection
frodoReferentSurvivesWikidataToBFOInspection =
  Applicability.frodoReferentPreservedAcrossLevels₀₁

frodoReferentSurvivesBFOToPartitionInspection :
  Applicability.referent Applicability.frodoBFOEntityInspection
  ≡ Applicability.referent Applicability.frodoBFOPartitionInspection
frodoReferentSurvivesBFOToPartitionInspection =
  Applicability.frodoReferentPreservedAcrossLevels₁₂

notEstablishedIsNotFalse :
  Applicability.BinaryDecoder.isFalse
    Applicability.safeEvaluationDecoder
    Applicability.notEstablished
  ≡ false
notEstablishedIsNotFalse = proj₂ Applicability.notEstablishedIsNeitherPositiveNorNegative

outOfScopeIsNotFalse :
  Applicability.BinaryDecoder.isFalse
    Applicability.safeEvaluationDecoder
    Applicability.outsideCommittedScope
  ≡ false
outOfScopeIsNotFalse = proj₂ Applicability.outsideScopeIsNeitherPositiveNorNegative

conflictingDerivationsCarryBothPolarities :
  Applicability.BinaryDecoder.isTrue
    Applicability.safeEvaluationDecoder
    Applicability.conflictingDerivations
  ≡ true
  × Applicability.BinaryDecoder.isFalse
    Applicability.safeEvaluationDecoder
    Applicability.conflictingDerivations
  ≡ true
conflictingDerivationsCarryBothPolarities =
  Applicability.conflictCarriesBothPolarities

------------------------------------------------------------------------
-- Higher-order / fictional scope: three distinct readings, one public label.
------------------------------------------------------------------------

sameSecondOrderSurfaceEditorialInWorld :
  Higher.classOrder Higher.editorialSecondOrderState
  ≡ Higher.classOrder Higher.inWorldSecondOrderState
sameSecondOrderSurfaceEditorialInWorld =
  Higher.sameClassOrderEditorialInWorld

sameSecondOrderSurfaceEditorialMemberClass :
  Higher.classOrder Higher.editorialSecondOrderState
  ≡ Higher.classOrder Higher.memberClassSecondOrderState
sameSecondOrderSurfaceEditorialMemberClass =
  Higher.sameClassOrderEditorialMemberClass

sameFictionalSecondOrderLabelEditorialInWorld :
  Higher.publicLabel Higher.editorialSecondOrderState
  ≡ Higher.publicLabel Higher.inWorldSecondOrderState
sameFictionalSecondOrderLabelEditorialInWorld =
  Higher.samePublicLabelEditorialInWorld

sameFictionalSecondOrderLabelEditorialMemberClass :
  Higher.publicLabel Higher.editorialSecondOrderState
  ≡ Higher.publicLabel Higher.memberClassSecondOrderState
sameFictionalSecondOrderLabelEditorialMemberClass =
  Higher.samePublicLabelEditorialMemberClass

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
    mappingStrengthIsSingleTotalOrder : Bool
    ambiguousRootPacketMeansSourceContradiction : Bool
    wikidataEntityImpliesBFOEntity : Bool
    notEstablishedMeansFalse : Bool
    outsideScopeMeansFalse : Bool
    conflictMeansUnknown : Bool
    secondOrderMeansFictional : Bool
    fictionalSecondOrderIsOneSemanticAtom : Bool
    memberClassesFictionalMeansMetaclassInWorldFictional : Bool
    keepOrderDomainApplicabilityOrthogonal : Bool
    preserveReferentAcrossInspectionLevels : Bool

canonicalWorkingGroupEntityScopeBoundary : WorkingGroupEntityScopeBoundary
canonicalWorkingGroupEntityScopeBoundary =
  workingGroupEntityScopeBoundary
    false false false false false false false false false false false false true true

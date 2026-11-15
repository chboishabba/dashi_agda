module DASHI.Ontology.OntologyCrosswalkStructuralValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Ontology.OntologyCrosswalkStructuralExact
import DASHI.Ontology.EducationOntologyMappingSSSOMExact as SSSOM

-- RED-first contract for the ontology-crosswalk max-cut.

labelsReallyCoincide :
  localName gsoEndurant ≡ localName dolceEndurant
labelsReallyCoincide = endurantLabelsCoincide

sameLabelStillNotSameConcept : gsoEndurant ≡ dolceEndurant → ⊥
sameLabelStillNotSameConcept = gsoDolceEndurantNotSameConcept

structuralMismatchBlocksStrongEquivalence :
  StrongEquivalence gsoEndurant dolceEndurant → ⊥
structuralMismatchBlocksStrongEquivalence =
  gsoDolceEndurantStrongEquivalenceImpossible

reportedEndurantRelationIsBridge :
  relation gsoDolceEndurantCrosswalk ≡ bridge
reportedEndurantRelationIsBridge = refl

qualityRowIsStillSourceObservedOnly :
  authority gsoDolceQualityCrosswalk ≡ sourceObservedOnly
qualityRowIsStillSourceObservedOnly = refl

qualitySourceRowCannotAssertTruth :
  CrosswalkTruthPermission (authority gsoDolceQualityCrosswalk) → ⊥
qualitySourceRowCannotAssertTruth = sourceObservationIsNotOntologyTruth

boundedQualityCompatibilityExists :
  StructuralCompatibility gsoQuality dolceQuality
boundedQualityCompatibilityExists = gsoDolceQualityStructuralCompatibility

boundedQualityCompatibilityDoesNotSelfPromote :
  StructuralCompatibility gsoQuality dolceQuality →
  CrosswalkTruthPermission sourceObservedOnly → ⊥
boundedQualityCompatibilityDoesNotSelfPromote _ = sourceObservationIsNotOntologyTruth

strongEquivalenceCarriesReviewedAdmission :
  {left right : CrosswalkConcept} →
  StrongEquivalence left right →
  CrosswalkTruthPermission reviewedAdmission
strongEquivalenceCarriesReviewedAdmission = reviewedPermission

bridgeCompilesConservatively :
  SSSOM.MappingPredicate
bridgeCompilesConservatively = compileRelationPredicate bridge

bridgeCompilesToLocalCorrespondence :
  compileRelationPredicate bridge ≡ SSSOM.localCorrespondence
bridgeCompilesToLocalCorrespondence = refl

strongEquivalenceRelationCompilesToOwlEquivalence :
  compileRelationPredicate equivalent ≡ SSSOM.owlEquivalentClass
strongEquivalenceRelationCompilesToOwlEquivalence = refl

endurantEnvelopeRemainsReviewOnly :
  SSSOM.reviewState (compileAssertionEnvelope gsoDolceEndurantCrosswalk)
  ≡ SSSOM.mappingForReviewOnly
endurantEnvelopeRemainsReviewOnly = refl

endurantEnvelopeCarriesUnresolvedConflict :
  SSSOM.finding (compileAssertionEnvelope gsoDolceEndurantCrosswalk)
  ≡ SSSOM.unresolvedMappingConflict
endurantEnvelopeCarriesUnresolvedConflict = refl

endurantCompiledPredicateRemainsBridgeLike :
  SSSOM.mappingPredicate
    (SSSOM.candidateMapping (compileAssertionEnvelope gsoDolceEndurantCrosswalk))
  ≡ SSSOM.localCorrespondence
endurantCompiledPredicateRemainsBridgeLike = refl

equivalenceIsLeftIdentity :
  composeRelation equivalent narrower ≡ narrower
equivalenceIsLeftIdentity = refl

equivalenceIsRightIdentity :
  composeRelation broader equivalent ≡ broader
equivalenceIsRightIdentity = refl

mixedDirectionsDoNotManufactureEquivalence :
  composeRelation narrower broader ≡ bridge
mixedDirectionsDoNotManufactureEquivalence = refl

weakBridgeRemainsWeakUnderComposition :
  composeRelation bridge equivalent ≡ bridge
weakBridgeRemainsWeakUnderComposition = refl

disjointDoesNotManufactureEquivalenceUnderComposition :
  composeRelation disjoint equivalent ≡ disjoint
disjointDoesNotManufactureEquivalenceUnderComposition = refl

sourceObservationCannotAssertTruth :
  CrosswalkTruthPermission sourceObservedOnly → ⊥
sourceObservationCannotAssertTruth = sourceObservationIsNotOntologyTruth

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

bridgeCompilesConservatively :
  SSSOM.MappingPredicate
bridgeCompilesConservatively = compileRelationPredicate bridge

bridgeCompilesToLocalCorrespondence :
  compileRelationPredicate bridge ≡ SSSOM.localCorrespondence
bridgeCompilesToLocalCorrespondence = refl

strongEquivalenceCompilesToOwlEquivalence :
  compileRelationPredicate equivalent ≡ SSSOM.owlEquivalentClass
strongEquivalenceCompilesToOwlEquivalence = refl

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

sourceObservationCannotAssertTruth :
  CrosswalkTruthPermission sourceObservedOnly → ⊥
sourceObservationCannotAssertTruth = sourceObservationIsNotOntologyTruth

module DASHI.Ontology.OntologyCrosswalkStructuralExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Ontology.EducationOntologyMappingSSSOMExact as SSSOM

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION BOUNDARY
--
-- Source page supplied by the user:
--   Wikidata user page "Ontology crosswalk"
--   https://www.wikidata.org/wiki/User:عثمان/Ontology_crosswalk
--
-- Bounded observations used by this module:
--   * the page compares several upper-ontology vocabularies;
--   * it places GSO and DOLCE notions with the same lexical label "Endurant"
--     into different surrounding structures;
--   * the page presents GSO Quality / Quality_Value alongside DOLCE Quality /
--     Quale correspondences.
--
-- DASHI owns every theorem below about typed relations, composition,
-- structural obstruction, conservative SSSOM compilation and authority.
-- The user page is not treated as OWL truth, a machine-checked alignment, or
-- authority to mutate Wikidata or any source ontology.
------------------------------------------------------------------------

data CrosswalkSourceClaim : Set where
  upperOntologyCrosswalkObserved : CrosswalkSourceClaim
  gsoDolceEndurantPlacementDifferenceObserved : CrosswalkSourceClaim
  gsoDolceQualityCorrespondenceObserved : CrosswalkSourceClaim

crosswalkSource : Transport.SourceBackedClaim
crosswalkSource = record
  { Transport.SourceClaim = CrosswalkSourceClaim
  ; Transport.sourceReceipt = upperOntologyCrosswalkObserved
  ; Transport.sourceName = "Wikidata user page: Ontology crosswalk"
  ; Transport.sourceLocator = "https://www.wikidata.org/wiki/User:عثمان/Ontology_crosswalk"
  ; Transport.reading = "bounded crosswalk observations only; local structural and governance theorems are DASHI-owned and do not promote the page into ontology truth"
  }

------------------------------------------------------------------------
-- TYPED ONTOLOGY / CONCEPT CARRIER
------------------------------------------------------------------------

data OntologyId : Set where
  wikidata : OntologyId
  bfo : OntologyId
  dolce : OntologyId
  gfo : OntologyId
  ufo : OntologyId
  gufO : OntologyId
  yamato : OntologyId
  gum : OntologyId
  gso : OntologyId

ontologyName : OntologyId → String
ontologyName wikidata = "Wikidata"
ontologyName bfo = "BFO"
ontologyName dolce = "DOLCE"
ontologyName gfo = "GFO"
ontologyName ufo = "UFO"
ontologyName gufO = "gUFO"
ontologyName yamato = "YAMATO"
ontologyName gum = "GUM"
ontologyName gso = "GSO"

-- Structural signatures deliberately encode only the distinctions paid by the
-- fixture. They are not complete definitions of the external ontologies.
data StructuralSignature : Set where
  genericEntityShape : StructuralSignature
  gsoEndurantContainsQualityAndAbstractShape : StructuralSignature
  dolceEndurantHasQualityAndAbstractAsSiblingShape : StructuralSignature
  qualityShape : StructuralSignature
  qualityValueQualeShape : StructuralSignature

record CrosswalkConcept : Set where
  constructor crosswalkConcept
  field
    ontology : OntologyId
    localName : String
    signature : StructuralSignature

open CrosswalkConcept public

gsoEndurant : CrosswalkConcept
gsoEndurant =
  crosswalkConcept gso "Endurant" gsoEndurantContainsQualityAndAbstractShape

dolceEndurant : CrosswalkConcept
dolceEndurant =
  crosswalkConcept dolce "Endurant" dolceEndurantHasQualityAndAbstractAsSiblingShape

gsoQuality : CrosswalkConcept
gsoQuality = crosswalkConcept gso "Quality" qualityShape

dolceQuality : CrosswalkConcept
dolceQuality = crosswalkConcept dolce "Quality" qualityShape

gsoQualityValue : CrosswalkConcept
gsoQualityValue = crosswalkConcept gso "Quality_Value" qualityValueQualeShape

dolceQuale : CrosswalkConcept
dolceQuale = crosswalkConcept dolce "Quale" qualityValueQualeShape

endurantLabelsCoincide : localName gsoEndurant ≡ localName dolceEndurant
endurantLabelsCoincide = refl

gsoDolceEndurantNotSameConcept : gsoEndurant ≡ dolceEndurant → ⊥
gsoDolceEndurantNotSameConcept ()

------------------------------------------------------------------------
-- RELATION ALGEBRA
--
-- Relations are intentionally richer than equality. Composition is
-- conservative: only identity-like equivalence and same-direction strict
-- refinement compose without loss. Mixed or weak relations fall back to a
-- bridge rather than manufacturing equivalence.
------------------------------------------------------------------------

data CrosswalkRelation : Set where
  equivalent : CrosswalkRelation
  narrower : CrosswalkRelation
  broader : CrosswalkRelation
  overlap : CrosswalkRelation
  disjoint : CrosswalkRelation
  bridge : CrosswalkRelation

equivalentNotBridge : equivalent ≡ bridge → ⊥
equivalentNotBridge ()

narrowerNotBroader : narrower ≡ broader → ⊥
narrowerNotBroader ()

disjointNotEquivalent : disjoint ≡ equivalent → ⊥
disjointNotEquivalent ()

composeRelation : CrosswalkRelation → CrosswalkRelation → CrosswalkRelation
composeRelation equivalent right = right
composeRelation left equivalent = left
composeRelation narrower narrower = narrower
composeRelation broader broader = broader
composeRelation _ _ = bridge

------------------------------------------------------------------------
-- AUTHORITY / PROVENANCE
------------------------------------------------------------------------

data CrosswalkAuthority : Set where
  sourceObservedOnly : CrosswalkAuthority
  localStructuralInterpretation : CrosswalkAuthority
  reviewedAdmission : CrosswalkAuthority

data CrosswalkTruthPermission : CrosswalkAuthority → Set where
  reviewedTruthPermission : CrosswalkTruthPermission reviewedAdmission

sourceObservationIsNotOntologyTruth :
  CrosswalkTruthPermission sourceObservedOnly → ⊥
sourceObservationIsNotOntologyTruth ()

localStructuralInterpretationIsNotOntologyTruth :
  CrosswalkTruthPermission localStructuralInterpretation → ⊥
localStructuralInterpretationIsNotOntologyTruth ()

record CrosswalkAssertion : Set where
  constructor crosswalkAssertion
  field
    leftConcept : CrosswalkConcept
    rightConcept : CrosswalkConcept
    relation : CrosswalkRelation
    authority : CrosswalkAuthority
    evidenceLocator : String
    evidenceReading : String

open CrosswalkAssertion public

------------------------------------------------------------------------
-- STRUCTURAL COMPATIBILITY != STRONG EQUIVALENCE
--
-- Matching the bounded signatures is only a compatibility receipt. Strong
-- equivalence additionally carries reviewed admission. This prevents the
-- positive Quality/Quale fixtures from self-promoting merely because this local
-- abstraction assigns them the same structural shape.
------------------------------------------------------------------------

record StructuralCompatibility (left right : CrosswalkConcept) : Set where
  constructor structuralCompatibility
  field
    sameSignature : signature left ≡ signature right

open StructuralCompatibility public

record StrongEquivalence (left right : CrosswalkConcept) : Set where
  constructor strongEquivalence
  field
    compatibility : StructuralCompatibility left right
    reviewedPermission : CrosswalkTruthPermission reviewedAdmission

open StrongEquivalence public

gsoDolceEndurantStructuralCompatibilityImpossible :
  StructuralCompatibility gsoEndurant dolceEndurant → ⊥
gsoDolceEndurantStructuralCompatibilityImpossible receipt
  with sameSignature receipt
... | ()

gsoDolceEndurantStrongEquivalenceImpossible :
  StrongEquivalence gsoEndurant dolceEndurant → ⊥
gsoDolceEndurantStrongEquivalenceImpossible receipt =
  gsoDolceEndurantStructuralCompatibilityImpossible (compatibility receipt)

gsoDolceQualityStructuralCompatibility :
  StructuralCompatibility gsoQuality dolceQuality
gsoDolceQualityStructuralCompatibility = structuralCompatibility refl

gsoDolceQualityValueQualeStructuralCompatibility :
  StructuralCompatibility gsoQualityValue dolceQuale
gsoDolceQualityValueQualeStructuralCompatibility = structuralCompatibility refl

------------------------------------------------------------------------
-- SOURCE-PAID FIXTURES + DASHI STRUCTURAL INTERPRETATION
------------------------------------------------------------------------

gsoDolceQualityCrosswalk : CrosswalkAssertion
gsoDolceQualityCrosswalk =
  crosswalkAssertion
    gsoQuality
    dolceQuality
    equivalent
    sourceObservedOnly
    "Wikidata User:عثمان/Ontology_crosswalk"
    "source page presents the two Quality notions as a direct correspondence; this row remains observation-level until independently admitted"

gsoDolceQualityValueQualeCrosswalk : CrosswalkAssertion
gsoDolceQualityValueQualeCrosswalk =
  crosswalkAssertion
    gsoQualityValue
    dolceQuale
    equivalent
    sourceObservedOnly
    "Wikidata User:عثمان/Ontology_crosswalk"
    "source page presents GSO Quality_Value alongside DOLCE Quale; this row remains observation-level until independently admitted"

gsoDolceEndurantCrosswalk : CrosswalkAssertion
gsoDolceEndurantCrosswalk =
  crosswalkAssertion
    gsoEndurant
    dolceEndurant
    bridge
    localStructuralInterpretation
    "Wikidata User:عثمان/Ontology_crosswalk"
    "same lexical label but incompatible bounded structural signatures; retain a bridge rather than promote equivalence"

------------------------------------------------------------------------
-- CONSERVATIVE SSSOM COMPILATION
------------------------------------------------------------------------

compileRelationPredicate : CrosswalkRelation → SSSOM.MappingPredicate
compileRelationPredicate equivalent = SSSOM.owlEquivalentClass
compileRelationPredicate narrower = SSSOM.rdfsSubClassOf
compileRelationPredicate broader = SSSOM.localCorrespondence
compileRelationPredicate overlap = SSSOM.localCorrespondence
compileRelationPredicate disjoint = SSSOM.localCorrespondence
compileRelationPredicate bridge = SSSOM.localCorrespondence

bridgeDoesNotCompileAsOwlEquivalence :
  compileRelationPredicate bridge ≡ SSSOM.owlEquivalentClass → ⊥
bridgeDoesNotCompileAsOwlEquivalence ()

mixedRefinementDoesNotComposeToEquivalence :
  composeRelation narrower broader ≡ equivalent → ⊥
mixedRefinementDoesNotComposeToEquivalence ()

-- Full compilation preserves the source-side concept labels, ontology names,
-- relation tag and evidence reading. It deliberately creates a review surface,
-- not an admitted ontology assertion.
compileAssertionMapping : CrosswalkAssertion → SSSOM.SSSOMMapping
compileAssertionMapping assertion =
  SSSOM.sssomMapping
    (localName (leftConcept assertion))
    (compileRelationPredicate (relation assertion))
    (localName (rightConcept assertion))
    SSSOM.importedSourceAssertion
    "DASHI ontology crosswalk compiler"
    ""
    0
    (ontologyName (ontology (leftConcept assertion)))
    "source-version-unspecified"
    (ontologyName (ontology (rightConcept assertion)))
    "source-version-unspecified"
    "2026-10-13"
    (evidenceReading assertion)

findingForRelation : CrosswalkRelation → SSSOM.MappingReviewFinding
findingForRelation equivalent = SSSOM.noObservedMappingConflict
findingForRelation narrower = SSSOM.noObservedMappingConflict
findingForRelation broader = SSSOM.unresolvedMappingConflict
findingForRelation overlap = SSSOM.unresolvedMappingConflict
findingForRelation disjoint = SSSOM.unresolvedMappingConflict
findingForRelation bridge = SSSOM.unresolvedMappingConflict

compileAssertionEnvelope : CrosswalkAssertion → SSSOM.MappingReviewEnvelope
compileAssertionEnvelope assertion =
  SSSOM.mappingReviewEnvelope
    (compileAssertionMapping assertion)
    SSSOM.mappingForReviewOnly
    (findingForRelation (relation assertion))
    (evidenceLocator assertion ∷ evidenceReading assertion ∷ [])

compiledEnvelopeCannotAssertTruth :
  (assertion : CrosswalkAssertion) →
  SSSOM.MappingTruthPermission
    (SSSOM.reviewState (compileAssertionEnvelope assertion)) → ⊥
compiledEnvelopeCannotAssertTruth assertion =
  SSSOM.mappingCannotAssertOntologyTruth

------------------------------------------------------------------------
-- MAX-CUT STATUS
------------------------------------------------------------------------

record OntologyCrosswalkStatus : Set where
  constructor ontologyCrosswalkStatus
  field
    typedOntologyCarrierOwned : Bool
    relationKindsRemainDistinct : Bool
    lexicalIdentityNotConceptIdentity : Bool
    structuralCompatibilitySeparatedFromEquivalence : Bool
    structuralMismatchBlocksStrongEquivalence : Bool
    sourceObservationSeparatedFromTruth : Bool
    conservativeRelationCompositionOwned : Bool
    conservativeSSSOMCompilationOwned : Bool
    reviewOnlyEnvelopeCompilationOwned : Bool
    gsoDolceEndurantObstructionOwned : Bool

    typedOntologyCarrierOwnedIsTrue : typedOntologyCarrierOwned ≡ true
    relationKindsRemainDistinctIsTrue : relationKindsRemainDistinct ≡ true
    lexicalIdentityNotConceptIdentityIsTrue : lexicalIdentityNotConceptIdentity ≡ true
    structuralCompatibilitySeparatedFromEquivalenceIsTrue :
      structuralCompatibilitySeparatedFromEquivalence ≡ true
    structuralMismatchBlocksStrongEquivalenceIsTrue :
      structuralMismatchBlocksStrongEquivalence ≡ true
    sourceObservationSeparatedFromTruthIsTrue :
      sourceObservationSeparatedFromTruth ≡ true
    conservativeRelationCompositionOwnedIsTrue :
      conservativeRelationCompositionOwned ≡ true
    conservativeSSSOMCompilationOwnedIsTrue :
      conservativeSSSOMCompilationOwned ≡ true
    reviewOnlyEnvelopeCompilationOwnedIsTrue :
      reviewOnlyEnvelopeCompilationOwned ≡ true
    gsoDolceEndurantObstructionOwnedIsTrue :
      gsoDolceEndurantObstructionOwned ≡ true

open OntologyCrosswalkStatus public

canonicalOntologyCrosswalkStatus : OntologyCrosswalkStatus
canonicalOntologyCrosswalkStatus =
  ontologyCrosswalkStatus
    true true true true true true true true true true
    refl refl refl refl refl refl refl refl refl refl

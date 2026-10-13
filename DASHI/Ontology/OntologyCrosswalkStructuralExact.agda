module DASHI.Ontology.OntologyCrosswalkStructuralExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
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

-- Structural signatures deliberately encode only the distinctions paid by the
-- fixture.  They are not complete definitions of the external ontologies.
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
-- Relations are intentionally richer than equality.  Composition is
-- conservative: only identity-like equivalence and same-direction strict
-- refinement compose without loss.  Mixed or weak relations fall back to a
-- bridge rather than manufacturing equivalence.
------------------------------------------------------------------------

data CrosswalkRelation : Set where
  equivalent : CrosswalkRelation
  narrower : CrosswalkRelation
  broader : CrosswalkRelation
  overlap : CrosswalkRelation
  disjoint : CrosswalkRelation
  bridge : CrosswalkRelation

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
-- STRONG EQUIVALENCE REQUIRES STRUCTURAL COMPATIBILITY
------------------------------------------------------------------------

record StrongEquivalence (left right : CrosswalkConcept) : Set where
  constructor strongEquivalence
  field
    structuralCompatibility : signature left ≡ signature right

open StrongEquivalence public

gsoDolceEndurantStrongEquivalenceImpossible :
  StrongEquivalence gsoEndurant dolceEndurant → ⊥
gsoDolceEndurantStrongEquivalenceImpossible receipt
  with structuralCompatibility receipt
... | ()

qualityStructuralCompatibility : signature gsoQuality ≡ signature dolceQuality
qualityStructuralCompatibility = refl

qualityValueQualeStructuralCompatibility :
  signature gsoQualityValue ≡ signature dolceQuale
qualityValueQualeStructuralCompatibility = refl

-- These are structural compatibility receipts for the deliberately bounded
-- fixture, not assertions that the external classes are globally OWL-equivalent.
gsoDolceQualityStrongCompatibility : StrongEquivalence gsoQuality dolceQuality
gsoDolceQualityStrongCompatibility = strongEquivalence refl

gsoDolceQualityValueQualeStrongCompatibility :
  StrongEquivalence gsoQualityValue dolceQuale
gsoDolceQualityValueQualeStrongCompatibility = strongEquivalence refl

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
--
-- Only the relation tag is compiled here.  Provenance, authority and admission
-- remain separate obligations in the existing SSSOM/repair pipeline.
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

------------------------------------------------------------------------
-- MAX-CUT STATUS
------------------------------------------------------------------------

record OntologyCrosswalkStatus : Set where
  constructor ontologyCrosswalkStatus
  field
    typedOntologyCarrierOwned : Bool
    relationKindsRemainDistinct : Bool
    lexicalIdentityNotConceptIdentity : Bool
    structuralMismatchBlocksStrongEquivalence : Bool
    sourceObservationSeparatedFromTruth : Bool
    conservativeRelationCompositionOwned : Bool
    conservativeSSSOMCompilationOwned : Bool
    gsoDolceEndurantObstructionOwned : Bool

    typedOntologyCarrierOwnedIsTrue : typedOntologyCarrierOwned ≡ true
    relationKindsRemainDistinctIsTrue : relationKindsRemainDistinct ≡ true
    lexicalIdentityNotConceptIdentityIsTrue : lexicalIdentityNotConceptIdentity ≡ true
    structuralMismatchBlocksStrongEquivalenceIsTrue :
      structuralMismatchBlocksStrongEquivalence ≡ true
    sourceObservationSeparatedFromTruthIsTrue :
      sourceObservationSeparatedFromTruth ≡ true
    conservativeRelationCompositionOwnedIsTrue :
      conservativeRelationCompositionOwned ≡ true
    conservativeSSSOMCompilationOwnedIsTrue :
      conservativeSSSOMCompilationOwned ≡ true
    gsoDolceEndurantObstructionOwnedIsTrue :
      gsoDolceEndurantObstructionOwned ≡ true

open OntologyCrosswalkStatus public

canonicalOntologyCrosswalkStatus : OntologyCrosswalkStatus
canonicalOntologyCrosswalkStatus =
  ontologyCrosswalkStatus
    true true true true true true true true
    refl refl refl refl refl refl refl refl

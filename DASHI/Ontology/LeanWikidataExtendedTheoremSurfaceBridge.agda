module DASHI.Ontology.LeanWikidataExtendedTheoremSurfaceBridge where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge

------------------------------------------------------------------------
-- Semantic anchors for source modules that were previously present only in
-- the whole-source manifest.  These are selected for cross-boundary meaning,
-- not to wrap every internal Lean lemma one-for-one.
------------------------------------------------------------------------

conceptClosureIdempotent : LeanTheoremContract
conceptClosureIdempotent =
  leanTheoremContract conceptsSource
    "Wikidata.Ontology.extentClosure_idem"
    "formal-concept extent closure is idempotent"
    semanticExactness

conceptExtensionNotInjective : LeanTheoremContract
conceptExtensionNotInjective =
  leanTheoremContract conceptsSource
    "Wikidata.ConceptExample.extension_not_injective"
    "equal instance extensions need not identify classes"
    negativeConstraintTheorem

exampleInstanceNotTransitive : LeanTheoremContract
exampleInstanceNotTransitive =
  leanTheoremContract examplesSource
    "Wikidata.Examples.instanceOf_not_transitive"
    "worked ontology demonstrates that instance-of is not transitive"
    negativeConstraintTheorem

exampleIncompatibleMerge : LeanTheoremContract
exampleIncompatibleMerge =
  leanTheoremContract examplesSource
    "Wikidata.Examples.incompatible_merge"
    "worked merge exposes incompatible source combination"
    diagnosticExactness

matchingTransitive : LeanTheoremContract
matchingTransitive =
  leanTheoremContract matchingSource
    "Wikidata.KeyTable.matchWith_trans"
    "functional/injective key matching composes transitively under its hypotheses"
    identityTransport

mergeEntailmentTransitive : LeanTheoremContract
mergeEntailmentTransitive =
  leanTheoremContract mergeSource
    "Wikidata.KB.entails_trans"
    "KB entailment composes transitively"
    preservationTheorem

mergeEntailsLeft : LeanTheoremContract
mergeEntailsLeft =
  leanTheoremContract mergeSource
    "Wikidata.KB.merge_entails_left"
    "well-formed merge entails its left input"
    preservationTheorem

propertyHoldsMinimal : LeanTheoremContract
propertyHoldsMinimal =
  leanTheoremContract propertiesSource
    "Wikidata.PropertyLayer.holds_minimal"
    "property semantic closure is the least relation closed under declared rules"
    semanticExactness

propertyInverseExact : LeanTheoremContract
propertyInverseExact =
  leanTheoremContract propertiesSource
    "Wikidata.PropertyLayer.holds_inverse_iff"
    "inverse-property semantics reverses subject and object exactly"
    semanticExactness

propertyStrictOrder : LeanTheoremContract
propertyStrictOrder =
  leanTheoremContract propertyConstraintsSource
    "Wikidata.PropertyLayer.isStrictOrder_of_irrefl_trans"
    "irreflexive transitive property induces a strict order"
    negativeConstraintTheorem

propertyEngineExact : LeanTheoremContract
propertyEngineExact =
  leanTheoremContract propertyEngineSource
    "Wikidata.PKB.relatedB_iff_holds"
    "executable property relation agrees with abstract property semantics"
    checkerExactness

quantityScaleConsistency : LeanTheoremContract
quantityScaleConsistency =
  leanTheoremContract quantitiesSource
    "Wikidata.Quantity.consistent_scale_iff"
    "quantity consistency is preserved/reflected by positive unit scaling"
    semanticExactness

quantityKmMetreExample : LeanTheoremContract
quantityKmMetreExample =
  leanTheoremContract quantitiesSource
    "Wikidata.QuantityExample.km_eq_thousandM"
    "worked unit system equates one kilometre with one thousand metres"
    semanticExactness

reachabilityExact : LeanTheoremContract
reachabilityExact =
  leanTheoremContract reachabilitySource
    "Reach.mem_reach_iff"
    "finite executable reachability agrees with reflexive-transitive generation"
    checkerExactness

selfDescriptionValid : LeanTheoremContract
selfDescriptionValid =
  leanTheoremContract selfDescriptionSource
    "Wikidata.KB.selfDescription_valid"
    "generated ontology self-description is valid"
    preservationTheorem

selfDescriptionKnowsOntology : LeanTheoremContract
selfDescriptionKnowsOntology =
  leanTheoremContract selfDescriptionSource
    "Wikidata.KB.selfDescription_knows_ontology"
    "self-description contains an ontology-level knowledge witness"
    semanticExactness

statementRequirementTransitive : LeanTheoremContract
statementRequirementTransitive =
  leanTheoremContract statementConstraintsSource
    "Wikidata.PropertyLayer.RequiresStatement.trans"
    "statement-requirement constraints compose transitively"
    structuralTheorem

statementConflictExecutable : LeanTheoremContract
statementConflictExecutable =
  leanTheoremContract statementConstraintsSource
    "Wikidata.PKB.conflictsWith_of_conflictsWithB"
    "executable statement conflict checker yields abstract conflict semantics"
    checkerSoundness

subsumptionLcsSound : LeanTheoremContract
subsumptionLcsSound =
  leanTheoremContract subsumptionSource
    "Wikidata.KB.isLCS_of_lcs?_eq_some"
    "computed least common superclass result is semantically sound"
    checkerSoundness

taxonomyAcyclic : LeanTheoremContract
taxonomyAcyclic =
  leanTheoremContract taxonomySource
    "Wikidata.Taxonomy.parentTaxon_acyclic"
    "worked parent-taxon relation is acyclic under its constraint hypotheses"
    negativeConstraintTheorem

termUniqueLookup : LeanTheoremContract
termUniqueLookup =
  leanTheoremContract termsSource
    "Wikidata.TermStore.byLabelDesc_subsingleton"
    "label plus description lookup is subsingleton under uniqueness"
    identityTransport

termAmbiguityRejected : LeanTheoremContract
termAmbiguityRejected =
  leanTheoremContract termsSource
    "Wikidata.TermExample.mercuryBad_not_uniqueOk"
    "worked ambiguous term store explicitly fails uniqueness"
    negativeConstraintTheorem

timeCoarseningCompatible : LeanTheoremContract
timeCoarseningCompatible =
  leanTheoremContract timeValuesSource
    "Wikidata.TimeValue.compatible_coarsen"
    "a time value remains compatible with its precision coarsening"
    contextPreservation

timeCompatibilityNotTransitive : LeanTheoremContract
timeCompatibilityNotTransitive =
  leanTheoremContract timeValuesSource
    "Wikidata.TimeExample.compatible_not_transitive"
    "worked time-value compatibility relation is not transitive"
    negativeConstraintTheorem

upperNoVariableClassOrder : LeanTheoremContract
upperNoVariableClassOrder =
  leanTheoremContract upperOntologySource
    "Wikidata.Upper.no_variable_order_class"
    "upper ontology rules exclude variable-order class confusion"
    negativeConstraintTheorem

upperPartNotSingleValued : LeanTheoremContract
upperPartNotSingleValued =
  leanTheoremContract upperOntologySource
    "Wikidata.Upper.partOf_not_singleValued"
    "worked part-of property is explicitly not single-valued"
    negativeConstraintTheorem

extendedTheoremContracts : List LeanTheoremContract
extendedTheoremContracts =
  conceptClosureIdempotent ∷ conceptExtensionNotInjective ∷
  exampleInstanceNotTransitive ∷ exampleIncompatibleMerge ∷
  matchingTransitive ∷ mergeEntailmentTransitive ∷ mergeEntailsLeft ∷
  propertyHoldsMinimal ∷ propertyInverseExact ∷ propertyStrictOrder ∷ propertyEngineExact ∷
  quantityScaleConsistency ∷ quantityKmMetreExample ∷ reachabilityExact ∷
  selfDescriptionValid ∷ selfDescriptionKnowsOntology ∷
  statementRequirementTransitive ∷ statementConflictExecutable ∷ subsumptionLcsSound ∷
  taxonomyAcyclic ∷ termUniqueLookup ∷ termAmbiguityRejected ∷
  timeCoarseningCompatible ∷ timeCompatibilityNotTransitive ∷
  upperNoVariableClassOrder ∷ upperPartNotSingleValued ∷ []

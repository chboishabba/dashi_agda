module DASHI.Ontology.EducationViaOntologyCompletionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _++_)

open import DASHI.Ontology.EducationViaOntologyExact public

record CourseOntologyPatch (prior : CourseOntology) : Set where
  constructor courseOntologyPatch
  field
    conceptAdditions : List String
    propertyAdditions : List String
    relationAdditions : List String
    patchProvenance : List String
open CourseOntologyPatch public

applyCourseOntologyPatch :
  {prior : CourseOntology} → CourseOntologyPatch prior → CourseOntology
applyCourseOntologyPatch {prior} patch =
  courseOntology
    (discipline prior)
    (modules prior)
    (concepts prior ++ conceptAdditions patch)
    (properties prior ++ propertyAdditions patch)
    (relations prior ++ relationAdditions patch)
    (sourceReferences prior ++ patchProvenance patch)
    (suc (revision prior))

patchConceptSnapshot :
  {prior : CourseOntology} → (patch : CourseOntologyPatch prior) →
  concepts (applyCourseOntologyPatch patch)
  ≡ concepts prior ++ conceptAdditions patch
patchConceptSnapshot patch = refl

patchPropertySnapshot :
  {prior : CourseOntology} → (patch : CourseOntologyPatch prior) →
  properties (applyCourseOntologyPatch patch)
  ≡ properties prior ++ propertyAdditions patch
patchPropertySnapshot patch = refl

patchRelationSnapshot :
  {prior : CourseOntology} → (patch : CourseOntologyPatch prior) →
  relations (applyCourseOntologyPatch patch)
  ≡ relations prior ++ relationAdditions patch
patchRelationSnapshot patch = refl

patchPreservesProvenance :
  {prior : CourseOntology} → (patch : CourseOntologyPatch prior) →
  sourceReferences (applyCourseOntologyPatch patch)
  ≡ sourceReferences prior ++ patchProvenance patch
patchPreservesProvenance patch = refl

patchAdvancesRevision :
  {prior : CourseOntology} → (patch : CourseOntologyPatch prior) →
  revision (applyCourseOntologyPatch patch) ≡ suc (revision prior)
patchAdvancesRevision patch = refl

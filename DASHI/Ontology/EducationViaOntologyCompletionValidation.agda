module DASHI.Ontology.EducationViaOntologyCompletionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])

open import DASHI.Ontology.EducationViaOntologyCompletionExact

samplePrior : CourseOntology
samplePrior = courseOntology "discipline" [] ("old" ∷ []) [] [] [] 0

samplePatch : CourseOntologyPatch samplePrior
samplePatch = courseOntologyPatch ("new" ∷ []) [] [] ("source" ∷ [])

patchPreservesOldAndAddsNew :
  concepts (applyCourseOntologyPatch samplePatch) ≡ ("old" ∷ "new" ∷ [])
patchPreservesOldAndAddsNew = refl

patchAdvancesRevision :
  revision (applyCourseOntologyPatch samplePatch) ≡ 1
patchAdvancesRevision = refl

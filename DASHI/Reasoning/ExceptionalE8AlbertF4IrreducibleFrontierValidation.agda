module DASHI.Reasoning.ExceptionalE8AlbertF4IrreducibleFrontierValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.ExceptionalE8AlbertF4IrreducibleFrontierExact as Cut

singleInputFrontier : Cut.originalQFrontierIsOneDependentInput Cut.canonicalBoundary ≡ true
singleInputFrontier = refl

threeConclusionsRemain : Cut.threeNamedClassificationConclusionsStillUnpaid Cut.canonicalBoundary ≡ true
threeConclusionsRemain = refl

notThreeIndependentLeaves : Cut.threeNamedConclusionsAreIndependentResearchLeaves Cut.canonicalBoundary ≡ false
notThreeIndependentLeaves = refl

finalWitnessStillOpen : Cut.finalDependentClassificationWitnessPaid Cut.canonicalBoundary ≡ false
finalWitnessStillOpen = refl

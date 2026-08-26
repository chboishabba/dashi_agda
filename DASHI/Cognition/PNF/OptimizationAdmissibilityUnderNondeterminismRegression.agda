{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.OptimizationAdmissibilityUnderNondeterminismRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.OptimizationAdmissibilityUnderNondeterminismExact

------------------------------------------------------------------------
-- Finite witness matching the migration-062 failure shape.
------------------------------------------------------------------------

data Unit : Set where
  unit : Unit

data Demand : Set where
  demand38 : Demand

data Candidate : Set where
  object22 object23 : Candidate

data Observation : Set where
  selected22 selected23 : Observation

legacySpecification : RelationalSpecification Demand Candidate Observation
legacySpecification = record
  { Admissible = λ where
      demand38 object22 → Unit
      demand38 object23 → Unit
  ; observe = λ where
      object22 → selected22
      object23 → selected23
  }

legacyChooses22 : SoundImplementation legacySpecification
legacyChooses22 = record
  { run = λ _ → object22
  ; sound = λ _ → unit
  }

optimizedAlsoChooses22 : SoundImplementation legacySpecification
optimizedAlsoChooses22 = record
  { run = λ _ → object22
  ; sound = λ _ → unit
  }

chosenTraceParity : TraceParity legacySpecification legacyChooses22 optimizedAlsoChooses22
chosenTraceParity = record
  { agreesOnChosenRuns = λ _ → refl
  }

------------------------------------------------------------------------
-- Yet another sound legacy execution may choose the other tied candidate.
------------------------------------------------------------------------

legacyChooses23 : SoundImplementation legacySpecification
legacyChooses23 = record
  { run = λ _ → object23
  ; sound = λ _ → unit
  }

selected22IsNotSelected23 : selected22 ≡ selected23 → ⊥
selected22IsNotSelected23 ()

legacyRelationIsConsumerNondeterministic : ConsumerDeterministic legacySpecification → ⊥
legacyRelationIsConsumerNondeterministic deterministic =
  selected22IsNotSelected23
    (sameObservation deterministic demand38 object22 object23 unit unit)

------------------------------------------------------------------------
-- Deterministically retaining object22 narrows the relation.  Because object23
-- was originally admissible and consumer-visible, this is not a conservative
-- optimization.  It is a semantic policy refinement.
------------------------------------------------------------------------

deterministic22Specification : RelationalSpecification Demand Candidate Observation
deterministic22Specification = record
  { Admissible = λ where
      demand38 object22 → Unit
      demand38 object23 → ⊥
  ; observe = λ where
      object22 → selected22
      object23 → selected23
  }

choose22RefinesLegacy : RelationRefinement legacySpecification deterministic22Specification
choose22RefinesLegacy = record
  { refinedIsOriginal = λ where
      demand38 object22 proof → unit
      demand38 object23 ()
  }

choose22IsNotConsumerConservative :
  ConsumerConservativeRefinement choose22RefinesLegacy → ⊥
choose22IsNotConsumerConservative conservative =
  selected22IsNotSelected23
    (eliminatedChoicesAreInvisible conservative
      demand38 object23 object22 unit unit)

------------------------------------------------------------------------
-- Therefore a faster deterministic tie-break does not become an optimization
-- merely because it is stable or reproduces one historical persisted winner.
------------------------------------------------------------------------

data StableTieBreakIsOptimizationPermission : Set where

stableTieBreakDoesNotManufactureOptimization :
  StableTieBreakIsOptimizationPermission → ⊥
stableTieBreakDoesNotManufactureOptimization ()

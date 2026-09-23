module DASHI.Biology.Evolution.EvolutionaryWorldCouplingTheoryBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural

------------------------------------------------------------------------
-- EVOLUTIONARY WORLD COUPLING WITHOUT PROPOSITIONAL THEORY
--
-- Selection/development/ecological feedback couple populations to actual
-- environmental conditions. No field in EvolutionarySystem requires that an
-- organism possess a symbolic theory of the environmental regularity.
------------------------------------------------------------------------

record EvolutionaryCouplingReceipt
    (E : Evolution.EvolutionarySystem) : Set₁ where
  open Evolution.EvolutionarySystem E
  constructor evolutionary-coupling-receipt
  field
    environment : Environment
    phenotype : Phenotype
    fitness : Fitness
    fitnessIsEnvironmentCoupled : select environment phenotype ≡ fitness
    couplingReference : String

open EvolutionaryCouplingReceipt public

data AdaptationRequiresExplicitTheoryPermission : Set where
data FitnessImpliesAgentBeliefPermission : Set where
data EvolutionImpliesGoalDirectedIntentPermission : Set where

adaptationDoesNotRequireExplicitTheory :
  AdaptationRequiresExplicitTheoryPermission → ⊥
adaptationDoesNotRequireExplicitTheory ()

fitnessDoesNotManufactureAgentBelief :
  FitnessImpliesAgentBeliefPermission → ⊥
fitnessDoesNotManufactureAgentBelief ()

evolutionDoesNotManufactureGoalDirectedIntent :
  EvolutionImpliesGoalDirectedIntentPermission → ⊥
evolutionDoesNotManufactureGoalDirectedIntent ()

worldBoundary : World.WorldRepresentationBoundary
worldBoundary = World.canonicalWorldRepresentationBoundary

naturalBoundary : Natural.NaturalSystemsBoundary
naturalBoundary = Natural.canonicalNaturalSystemsBoundary

record EvolutionaryWorldCouplingBoundary : Set where
  constructor evolutionary-world-coupling-boundary
  field
    environmentalConstraintCanShapePhenotypeWithoutSymbolicTheory : Bool
    environmentalConstraintCanShapePhenotypeWithoutSymbolicTheoryIsTrue :
      environmentalConstraintCanShapePhenotypeWithoutSymbolicTheory ≡ true
    adaptationIsEvidenceOrganismHoldsPropositionalTheory : Bool
    adaptationIsEvidenceOrganismHoldsPropositionalTheoryIsFalse :
      adaptationIsEvidenceOrganismHoldsPropositionalTheory ≡ false
    evolutionaryFitMakesTheoryWorldIdentity : Bool
    evolutionaryFitMakesTheoryWorldIdentityIsFalse :
      evolutionaryFitMakesTheoryWorldIdentity ≡ false
    selectionIsGoalDirectedUnderstanding : Bool
    selectionIsGoalDirectedUnderstandingIsFalse :
      selectionIsGoalDirectedUnderstanding ≡ false

open EvolutionaryWorldCouplingBoundary public

canonicalEvolutionaryWorldCouplingBoundary : EvolutionaryWorldCouplingBoundary
canonicalEvolutionaryWorldCouplingBoundary =
  evolutionary-world-coupling-boundary
    true refl
    false refl
    false refl
    false refl

module DASHI.Education.FollowThroughFidelityConfoundingExact where

-- Synthetic observational collision: association is not causal identification.
-- Independent DASHI mathematics; not an Abt / House study estimate.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as INF

data World : Set where
  confounded : World
  beneficial : World

data ObservedTable : Set where
  sameFidelityOutcomeAssociation : ObservedTable

data InterventionEffect : Set where
  zeroEffect : InterventionEffect
  positiveEffect : InterventionEffect

observed : World → ObservedTable
observed confounded = sameFidelityOutcomeAssociation
observed beneficial = sameFidelityOutcomeAssociation

causalEffect : World → InterventionEffect
causalEffect confounded = zeroEffect
causalEffect beneficial = positiveEffect

effectDiffers : causalEffect confounded ≡ causalEffect beneficial → ⊥
effectDiffers ()

observationCannotIdentifyCausalEffectWitness :
  INF.NonFactorabilityWitness observed causalEffect
observationCannotIdentifyCausalEffectWitness =
  INF.nonFactorabilityWitness confounded beneficial refl effectDiffers

observationCannotIdentifyCausalEffect :
  INF.FactorsThrough observed causalEffect → ⊥
observationCannotIdentifyCausalEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    observationCannotIdentifyCausalEffectWitness

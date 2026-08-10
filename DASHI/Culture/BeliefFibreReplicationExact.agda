module DASHI.Culture.BeliefFibreReplicationExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION / INTERPRETIVE BOUNDARY
--
-- Formalize only the dynamical statement behind the phrase "they do not have
-- to believe it to replicate it": a fine state can carry an auxiliary belief
-- coordinate in the fibre while its projected material/institutional update is
-- independent of that coordinate.
--
-- This is a generic product-transition theorem.  It does not assert that any
-- actual political system, ideology, population, or person satisfies the
-- hypothesis.  Those would require empirical models and evidence not supplied
-- by this formal layer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record FibreInsensitiveDynamics (Material Belief : Set) : Set₁ where
  constructor fibreInsensitiveDynamics
  field
    materialStep : Material → Material
    beliefStep : Material → Belief → Belief

open FibreInsensitiveDynamics public

FineState : Set → Set → Set
FineState Material Belief = Material × Belief

projectMaterial :
  ∀ {Material Belief} → FineState Material Belief → Material
projectMaterial = proj₁

stepFine :
  ∀ {Material Belief} →
  FibreInsensitiveDynamics Material Belief →
  FineState Material Belief → FineState Material Belief
stepFine dynamics (material , belief) =
  materialStep dynamics material
  , beliefStep dynamics material belief

-- Different belief states over the same coarse material state produce exactly
-- the same projected material successor.
beliefLiesInTransitionFibre :
  ∀ {Material Belief}
    (dynamics : FibreInsensitiveDynamics Material Belief)
    (material : Material) (belief₁ belief₂ : Belief) →
  projectMaterial (stepFine dynamics (material , belief₁))
  ≡ projectMaterial (stepFine dynamics (material , belief₂))
beliefLiesInTransitionFibre dynamics material belief₁ belief₂ = refl

-- The result is intentionally conditional on the chosen dynamics.  A different
-- model may allow the belief coordinate to feed back into the coarse update;
-- that stronger architecture is not ruled out by this witness.

record BeliefFibreClaimScope : Set where
  constructor beliefFibreClaimScope
  field
    genericFibreInsensitiveDynamicsConstructed : Bool
    genericFibreInsensitiveDynamicsConstructedIsTrue :
      genericFibreInsensitiveDynamicsConstructed ≡ true

    allSocialSystemsProvedBeliefInsensitive : Bool
    allSocialSystemsProvedBeliefInsensitiveIsFalse :
      allSocialSystemsProvedBeliefInsensitive ≡ false

    empiricalPoliticalClaimEstablished : Bool
    empiricalPoliticalClaimEstablishedIsFalse :
      empiricalPoliticalClaimEstablished ≡ false

canonicalBeliefFibreClaimScope : BeliefFibreClaimScope
canonicalBeliefFibreClaimScope =
  beliefFibreClaimScope true refl false refl false refl

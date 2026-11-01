module DASHI.Core.EnergeticNeutrality where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)

------------------------------------------------------------------------
-- Neutrality is kept ternary.  Energetic vacuum is not introduced as a
-- fourth Trit constructor; it is evidence carried by a neutral site inside
-- a non-flat neighbourhood/action field.

data ActiveGradient : Trit → Set where
  descending : ActiveGradient neg
  ascending  : ActiveGradient pos

record EnergeticVacuum : Set where
  constructor energeticVacuum
  field
    centre : Trit
    centre-is-neutral : centre ≡ zer
    gradient : Trit
    gradient-is-active : ActiveGradient gradient

open EnergeticVacuum public

record StructuralNull : Set where
  constructor structuralNull
  field
    nullCentre : Trit
    nullCentre-is-neutral : nullCentre ≡ zer

open StructuralNull public

-- Both surfaces project to the same observable Trit at the centre.
projectVacuum : EnergeticVacuum → Trit
projectVacuum v = centre v

projectNull : StructuralNull → Trit
projectNull n = nullCentre n

vacuum-projects-to-neutral : ∀ v → projectVacuum v ≡ zer
vacuum-projects-to-neutral v = centre-is-neutral v

null-projects-to-neutral : ∀ n → projectNull n ≡ zer
null-projects-to-neutral n = nullCentre-is-neutral n

-- Their distinction is in the witness layer: a vacuum has an active
-- surrounding gradient, while a structural null carries no such witness.
leftVacuum : EnergeticVacuum
leftVacuum = energeticVacuum zer refl neg descending

rightVacuum : EnergeticVacuum
rightVacuum = energeticVacuum zer refl pos ascending

flatNull : StructuralNull
flatNull = structuralNull zer refl

------------------------------------------------------------------------
-- Involution fixes the neutral centre and reverses the gradient.

invertActiveGradient : ∀ {g} → ActiveGradient g → ActiveGradient (inv g)
invertActiveGradient descending = ascending
invertActiveGradient ascending = descending

invertVacuum : EnergeticVacuum → EnergeticVacuum
invertVacuum (energeticVacuum .zer refl g active) =
  energeticVacuum zer refl (inv g) (invertActiveGradient active)

invertVacuum-centre-fixed : ∀ v → centre (invertVacuum v) ≡ centre v
invertVacuum-centre-fixed (energeticVacuum .zer refl neg descending) = refl
invertVacuum-centre-fixed (energeticVacuum .zer refl pos ascending) = refl

invertVacuum-involutive-gradient : ∀ v → gradient (invertVacuum (invertVacuum v)) ≡ gradient v
invertVacuum-involutive-gradient (energeticVacuum .zer refl neg descending) = refl
invertVacuum-involutive-gradient (energeticVacuum .zer refl pos ascending) = refl

------------------------------------------------------------------------
-- Minimal neighbourhood interface for the action-gradient reading.
-- The system is dynamically flat only when no ActiveGradient witness exists.

record NeutralSiteDynamics : Set where
  constructor neutralSiteDynamics
  field
    site : Trit
    site-is-neutral : site ≡ zer
    localSlope : Trit

open NeutralSiteDynamics public

data VacuumClassification : NeutralSiteDynamics → Set where
  structurallyFlat : VacuumClassification (neutralSiteDynamics zer refl zer)
  energeticallyDescending : VacuumClassification (neutralSiteDynamics zer refl neg)
  energeticallyAscending : VacuumClassification (neutralSiteDynamics zer refl pos)

classification-exhaustive :
  ∀ (d : NeutralSiteDynamics) → VacuumClassification d
classification-exhaustive (neutralSiteDynamics .zer refl neg) = energeticallyDescending
classification-exhaustive (neutralSiteDynamics .zer refl zer) = structurallyFlat
classification-exhaustive (neutralSiteDynamics .zer refl pos) = energeticallyAscending

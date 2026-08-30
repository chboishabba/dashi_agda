module DASHI.Physics.Closure.NSTriadKNRapidCascadePersistenceTargetRound277Exact where

------------------------------------------------------------------------
-- ROUND277 / CORRECTED RAPID-CASCADE RIGIDITY TARGET
--
-- R276 shows only L2 collapse along a high-frequency sequence.  That is not a
-- contradiction for a dissipative equation.  To rule out the cascade branch
-- using the existing finite-dissipation budget, one needs a persistence/local
-- constancy statement strong enough to convert repeated high-frequency
-- concentration into a non-summable amount of gradient dissipation.
--
-- Sufficient shape:
--   N(t_n) -> infinity,
--   on a parabolic window of length >= c / N(t_n)^2,
--   ||grad u||_2^2 >= c' N(t_n) K_c,
-- and the selected windows contain a disjoint subfamily whose total lower
-- dissipation diverges.
--
-- The last disjoint-window/divergence conclusion is NOT automatic from mere
-- unboundedness of N(t).  It is the genuine rapid-cascade rigidity theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record RapidCascadeDissipationPersistence {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics
    escapingFrequencySequence : Set ℓ
    localConstancyAtParabolicScale : Set ℓ
    gradientLowerBoundOnPersistenceWindow : Set ℓ
    disjointPersistenceSubfamily : Set ℓ
    persistenceWindowsForceInfiniteDissipation : Set ℓ
    canonicalFiniteTotalDissipation : Set ℓ
    contradiction :
      persistenceWindowsForceInfiniteDissipation →
      canonicalFiniteTotalDissipation → ⊥

open RapidCascadeDissipationPersistence public

rapidCascadeImpossible :
  ∀ {ℓ} {CriticalDynamics : Set ℓ} →
  RapidCascadeDissipationPersistence CriticalDynamics → ⊥
rapidCascadeImpossible A = contradiction A
  (persistenceWindowsForceInfiniteDissipation A)
  (canonicalFiniteTotalDissipation A)

round277L2CollapseIsInsufficient : Bool
round277L2CollapseIsInsufficient = true

round277NeedsParabolicPersistencePlusNonSummableDissipation : Bool
round277NeedsParabolicPersistencePlusNonSummableDissipation = true

round277RapidCascadeRigidityClosed : Bool
round277RapidCascadeRigidityClosed = false

round277PackageAClosed : Bool
round277PackageAClosed = false

round277RapidCascadeRigidityClosedIsFalse :
  round277RapidCascadeRigidityClosed ≡ false
round277RapidCascadeRigidityClosedIsFalse = refl

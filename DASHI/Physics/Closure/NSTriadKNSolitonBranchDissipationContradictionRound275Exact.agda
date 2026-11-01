module DASHI.Physics.Closure.NSTriadKNSolitonBranchDissipationContradictionRound275Exact where

------------------------------------------------------------------------
-- ROUND275 / GLOBAL BOUNDED-FREQUENCY BRANCH VS FINITE TOTAL DISSIPATION
--
-- If Round274 supplies a positive gradient-energy floor on an infinite
-- lifespan, then cumulative dissipation grows without bound.  Canonical G2
-- supplies a finite total dissipation budget.  Their incompatibility rules out
-- the bounded-frequency global branch.
--
-- The infinite-time integration/Archimedean passage is analytic/order theory;
-- this module names that exact receipt rather than hiding it in 'soliton'.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record GlobalBoundedFrequencyDissipationContradiction {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics
    globalInfiniteLifespan : Set ℓ
    positiveDissipationFloor : Set ℓ
    canonicalFiniteTotalDissipation : Set ℓ
    floorForcesUnboundedCumulativeDissipation : Set ℓ
    finiteAndUnboundedDissipationContradict :
      canonicalFiniteTotalDissipation →
      floorForcesUnboundedCumulativeDissipation → ⊥

open GlobalBoundedFrequencyDissipationContradiction public

boundedFrequencyBranchImpossible :
  ∀ {ℓ} {CriticalDynamics : Set ℓ} →
  GlobalBoundedFrequencyDissipationContradiction CriticalDynamics → ⊥
boundedFrequencyBranchImpossible A =
  finiteAndUnboundedDissipationContradict A
    (canonicalFiniteTotalDissipation A)
    (floorForcesUnboundedCumulativeDissipation A)

round275CanonicalG2IsTheFiniteDissipationConsumer : Bool
round275CanonicalG2IsTheFiniteDissipationConsumer = true

round275BoundedFrequencyBranchContradictionConditionalCompilerClosed : Bool
round275BoundedFrequencyBranchContradictionConditionalCompilerClosed = true

round275PhysicalAnalyticContradictionInstanceClosed : Bool
round275PhysicalAnalyticContradictionInstanceClosed = false

round275PackageAClosed : Bool
round275PackageAClosed = false

round275PhysicalAnalyticContradictionInstanceClosedIsFalse :
  round275PhysicalAnalyticContradictionInstanceClosed ≡ false
round275PhysicalAnalyticContradictionInstanceClosedIsFalse = refl

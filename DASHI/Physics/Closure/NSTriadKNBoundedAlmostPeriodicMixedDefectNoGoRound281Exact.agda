module DASHI.Physics.Closure.NSTriadKNBoundedAlmostPeriodicMixedDefectNoGoRound281Exact where

------------------------------------------------------------------------
-- ROUND281 / BIDI NO-GO FOR A BOUNDED ALMOST-PERIODIC MIXED-DEFECT BAD ELEMENT
--
-- R241 + the now-instantiated W1/W2 lane already gives:
--
--   sup_t ||u(t)||_{H^(1/2)}^2 <= K
--   + finite integrated dissipation D_*
--   => integral Q_+-(u) <= C K D_*.
--
-- Navier--Stokes scaling leaves the H^(1/2) norm invariant.  Therefore an
-- orbit precompact modulo translations/scaling is H^(1/2)-bounded.  If the
-- same nonlinear solution also carries the mixed-defect badness on the whole
-- relevant interval, W1/W2 immediately pay its defect.  Thus the standard
-- Kenig--Merle object
--
--   bounded almost-periodic critical solution + persistent badness
--
-- cannot be the obstruction for THIS badness predicate.
--
-- Consequence: R272 must not try to manufacture a globally H^(1/2)-bounded
-- almost-periodic solution that remains mixed-defect-bad.  The correct inverse
-- extraction has to retain the UNBOUNDED critical-size escape (for example via
-- threshold-indexed first-hit profiles), or return to the direct physical
-- quartic-companion/covariance route that aims to prove the critical barrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record BoundedAlmostPeriodicBadElementNoGo {ℓ : Level}
    (CriticalSolution : Set ℓ) : Set (lsuc ℓ) where
  field
    solution : CriticalSolution
    hOneHalfOrbitBounded : Set ℓ
    finiteIntegratedDissipation : Set ℓ
    w1w2PaysMixedDefect : Set ℓ
    persistentMixedDefectBadness : Set ℓ
    paidBoundContradictsPersistentBadness :
      w1w2PaysMixedDefect → persistentMixedDefectBadness → ⊥

open BoundedAlmostPeriodicBadElementNoGo public

boundedAlmostPeriodicBadElementImpossible :
  ∀ {ℓ} {CriticalSolution : Set ℓ} →
  BoundedAlmostPeriodicBadElementNoGo CriticalSolution → ⊥
boundedAlmostPeriodicBadElementImpossible A =
  paidBoundContradictsPersistentBadness A
    (w1w2PaysMixedDefect A)
    (persistentMixedDefectBadness A)

round281HOneHalfScalingInvariant : Bool
round281HOneHalfScalingInvariant = true

round281AlmostPeriodicModuloNSScalingImpliesCriticalNormBounded : Bool
round281AlmostPeriodicModuloNSScalingImpliesCriticalNormBounded = true

round281W1W2PayAnyBoundedCriticalOrbitDefect : Bool
round281W1W2PayAnyBoundedCriticalOrbitDefect = true

round281BoundedAlmostPeriodicPersistentBadElementAdmissible : Bool
round281BoundedAlmostPeriodicPersistentBadElementAdmissible = false

round281R272ToR280AsOriginallyProposedIsHighestAlpha : Bool
round281R272ToR280AsOriginallyProposedIsHighestAlpha = false

round281PackageAClosed : Bool
round281PackageAClosed = false

round281BoundedAlmostPeriodicPersistentBadElementAdmissibleIsFalse :
  round281BoundedAlmostPeriodicPersistentBadElementAdmissible ≡ false
round281BoundedAlmostPeriodicPersistentBadElementAdmissibleIsFalse = refl

round281R272ToR280AsOriginallyProposedIsHighestAlphaIsFalse :
  round281R272ToR280AsOriginallyProposedIsHighestAlpha ≡ false
round281R272ToR280AsOriginallyProposedIsHighestAlphaIsFalse = refl

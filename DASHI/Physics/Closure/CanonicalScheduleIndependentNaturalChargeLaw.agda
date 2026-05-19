module DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeLaw where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalClosureFibreEigenShadowObstruction as CCFEO
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

------------------------------------------------------------------------
-- Smallest honest schedule-independent quotient law over the canonical
-- gauge/matter bundle.
--
-- This file does not widen the conserved quantity beyond the currently
-- transported coarse quotient.  The quotient-visible charge is exactly the
-- coarse package already known to factor through the live shift schedule:
--
--   Gauge × basin × motif
--
-- The law below packages:
-- * a schedule-facing source factorization;
-- * a schedule-facing evolve factorization;
-- * the induced schedule-independent natural/conserved law on the bundle
--   carrier itself.
--
-- It also re-exports the existing eigen-shadow obstruction so downstream code
-- cannot silently treat richer channels as if they already descended to this
-- quotient.

record CanonicalScheduleIndependentNaturalChargeLaw : Setω where
  field
    Quotient : Set
    charge : AGMB.Carrier CA.canonicalAbstractGaugeMatterBundle → Quotient
    scheduleCharge : CA.CanonicalShiftCarrier → Quotient

    source-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      charge x ≡ scheduleCharge (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))

    evolve-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      charge (CA.canonicalClosureDynamics x)
        ≡
      scheduleCharge (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))

    schedule-independent-natural-law :
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      charge x ≡ charge (CA.canonicalClosureDynamics x)

canonicalScheduleIndependentNaturalChargeLaw :
  CanonicalScheduleIndependentNaturalChargeLaw
canonicalScheduleIndependentNaturalChargeLaw =
  record
    { Quotient = CA.CanonicalCoarseConservedCharge
    ; charge = CA.canonicalCoarseConservedChargeOf
    ; scheduleCharge = CA.projectTransportedShiftCoarseCharge
    ; source-to-schedule = CA.canonicalSourceCoarseCharge-to-schedule
    ; evolve-to-schedule = CA.canonicalClosureCoarseCharge-to-schedule
    ; schedule-independent-natural-law =
        CA.canonicalCoarseConservedChargePreserved
    }

eigenShadowWideningObstructed :
  CCFEO.sameFibre⇒sameEigenShadow-obstructed → ⊥
eigenShadowWideningObstructed =
  CCFEO.sameFibre⇒sameEigenShadow-obstructed-false

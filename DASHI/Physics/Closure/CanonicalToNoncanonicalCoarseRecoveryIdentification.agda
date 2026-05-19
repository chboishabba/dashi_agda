module DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans; cong)
open import Data.Product using (proj₁; proj₂)

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

------------------------------------------------------------------------
-- First explicit identification surface between the canonical closure-side
-- preserved coarse carrier and the first noncanonical continuum carrier.
--
-- This is intentionally narrow:
-- - it does not claim a broad continuum-limit theorem,
-- - it does not remove dependence on the coarse carrier,
-- - it only identifies the current canonical coarse recovery data with the
--   first noncanonical continuum scale on transported admissible states.

CanonicalCarrier : Set
CanonicalCarrier = CCGP.Carrier PGCT.canonicalConstraintGaugePackage

noncanonicalMdl :
  SCOT.ShiftContractMdlRefinedContinuumCarrier → Nat
noncanonicalMdl q = proj₁ (proj₂ (proj₂ q))

record CanonicalToNoncanonicalCoarseRecoveryIdentification : Setω where
  field
    canonicalTransportBackedNaturalCoarse :
      CAMI.CanonicalTransportBackedNaturalCoarseTheorem

    noncanonicalContinuum :
      AGMB.ContinuumWitness SCOT.shiftContractObservableBundle

    transportedScheduleToNoncanonicalContinuum :
      ∀ x →
      CAMI.projectTransportedShiftCoarseCharge
        (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState x))
        ≡
      SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x)

    sourceCoarseToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CAMI.canonicalCoarseConservedChargeOf x
        ≡
      SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x)

    evolveCoarseToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CAMI.canonicalCoarseConservedChargeOf (CAMI.canonicalClosureDynamics x)
        ≡
      SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x)

    coarsePreservationWithoutSchedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CAMI.canonicalCoarseConservedChargeOf x
        ≡
      CAMI.canonicalCoarseConservedChargeOf
        (CAMI.canonicalClosureDynamics x)

    sourceGaugeToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      proj₁ (CAMI.canonicalCoarseConservedChargeOf x)
        ≡
      proj₁ (SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x))

    sourceBasinToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      proj₁ (proj₂ (CAMI.canonicalCoarseConservedChargeOf x))
        ≡
      proj₁ (proj₂ (SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x)))

    sourceMotifToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      proj₂ (proj₂ (CAMI.canonicalCoarseConservedChargeOf x))
        ≡
      proj₂ (proj₂ (SCOT.shiftContractObservableContinuumScale
        (CAMI.canonicalTransportState x)))

canonicalToNoncanonicalCoarseRecoveryIdentification :
  CanonicalToNoncanonicalCoarseRecoveryIdentification
canonicalToNoncanonicalCoarseRecoveryIdentification =
  record
    { canonicalTransportBackedNaturalCoarse =
        CAMI.canonicalTransportBackedNaturalCoarseTheorem
    ; noncanonicalContinuum =
        SCOT.shiftContractObservableContinuumWitness
    ; transportedScheduleToNoncanonicalContinuum =
        λ _ → refl
    ; sourceCoarseToNoncanonicalContinuum =
        λ x ax →
          trans
            (CAMI.canonicalSourceCoarseCharge-to-schedule x ax)
            refl
    ; evolveCoarseToNoncanonicalContinuum =
        λ x ax →
          trans
            (CAMI.canonicalClosureCoarseCharge-to-schedule x ax)
            refl
    ; coarsePreservationWithoutSchedule =
        CAMI.canonicalCoarseConservedChargePreserved
    ; sourceGaugeToNoncanonicalContinuum =
        λ x ax →
          cong proj₁
            (trans
              (CAMI.canonicalSourceCoarseCharge-to-schedule x ax)
              refl)
    ; sourceBasinToNoncanonicalContinuum =
        λ x ax →
          cong (λ q → proj₁ (proj₂ q))
            (trans
              (CAMI.canonicalSourceCoarseCharge-to-schedule x ax)
              refl)
    ; sourceMotifToNoncanonicalContinuum =
        λ x ax →
          cong (λ q → proj₂ (proj₂ q))
            (trans
              (CAMI.canonicalSourceCoarseCharge-to-schedule x ax)
              refl)
    }

record CanonicalToNoncanonicalMdlRefinedRecoveryIdentification : Setω where
  field
    coarseRecovery :
      CanonicalToNoncanonicalCoarseRecoveryIdentification

    sourceMdlToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CAMI.canonicalMdlLevel x
        ≡
      noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState x))

    evolveMdlToNoncanonicalContinuum :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CAMI.canonicalMdlLevel (CAMI.canonicalClosureDynamics x)
        ≡
      noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState x))

mdlRefinedRecoveryIdentificationFromMdlHypotheses :
  ((x : CanonicalCarrier) →
   SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
   CAMI.canonicalMdlLevel x
     ≡
   noncanonicalMdl
     (SCOT.shiftContractObservableMdlRefinedContinuumScale
       (CAMI.canonicalTransportState x)))
  →
  ((x : CanonicalCarrier) →
   SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
   CAMI.canonicalMdlLevel (CAMI.canonicalClosureDynamics x)
     ≡
   noncanonicalMdl
     (SCOT.shiftContractObservableMdlRefinedContinuumScale
       (CAMI.canonicalTransportState x)))
  →
  CanonicalToNoncanonicalMdlRefinedRecoveryIdentification
mdlRefinedRecoveryIdentificationFromMdlHypotheses sourceMdl evolveMdl =
  record
    { coarseRecovery = canonicalToNoncanonicalCoarseRecoveryIdentification
    ; sourceMdlToNoncanonicalContinuum = sourceMdl
    ; evolveMdlToNoncanonicalContinuum = evolveMdl
    }

canonicalToNoncanonicalMdlRefinedRecoveryIdentificationFromHypotheses :
  ((x : CanonicalCarrier) →
   SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
   CAMI.canonicalMdlLevel x
     ≡
   noncanonicalMdl
     (SCOT.shiftContractObservableMdlRefinedContinuumScale
       (CAMI.canonicalTransportState x)))
  →
  ((x : CanonicalCarrier) →
   SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
   CAMI.canonicalMdlLevel (CAMI.canonicalClosureDynamics x)
     ≡
   noncanonicalMdl
     (SCOT.shiftContractObservableMdlRefinedContinuumScale
       (CAMI.canonicalTransportState x)))
  →
  CanonicalToNoncanonicalMdlRefinedRecoveryIdentification
canonicalToNoncanonicalMdlRefinedRecoveryIdentificationFromHypotheses =
  mdlRefinedRecoveryIdentificationFromMdlHypotheses

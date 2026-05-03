module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

------------------------------------------------------------------------
-- MDL seam tightening above the coarse canonical-to-noncanonical recovery.
--
-- The current sharpest theorem move is not a full MDL-refined recovery proof.
-- It is a blocker reduction:
-- - the noncanonical target side is already definitionally fixed,
-- - the evolve-side MDL equality follows from canonical MDL preservation,
-- - so the live blocker reduces to one source-side transported-schedule MDL
--   obligation.

transportedScheduleMdl :
  CNCRI.CanonicalCarrier → Set
transportedScheduleMdl x =
  CAMI.canonicalMdlLevel x
    ≡
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe
      SRGOI.shiftRGSurface
      (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState x)))

canonicalMdlLevelPreserved :
  ∀ x →
  CAMI.canonicalMdlLevel x
    ≡
  CAMI.canonicalMdlLevel (CAMI.canonicalClosureDynamics x)
canonicalMdlLevelPreserved x =
  cong
    (λ q → proj₁ (proj₂ (proj₂ q)))
    (CAMI.canonicalConservedChargePreserved x)
  where
  open import Data.Product using (proj₁; proj₂)

record CanonicalToNoncanonicalMdlSourceScheduleObligation : Setω where
  field
    sourceMdlToTransportedSchedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      transportedScheduleMdl x

    transportedScheduleMdlToNoncanonicalContinuum :
      ∀ x →
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState x)))
        ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState x))

sourceScheduleObligation-to-MdlRefinedRecovery :
  CanonicalToNoncanonicalMdlSourceScheduleObligation →
  CNCRI.CanonicalToNoncanonicalMdlRefinedRecoveryIdentification
sourceScheduleObligation-to-MdlRefinedRecovery src =
  CNCRI.canonicalToNoncanonicalMdlRefinedRecoveryIdentificationFromHypotheses
    sourceEq
    evolveEq
  where
  open CanonicalToNoncanonicalMdlSourceScheduleObligation src

  sourceEq :
    ∀ x →
    SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
    CAMI.canonicalMdlLevel x
      ≡
    CNCRI.noncanonicalMdl
      (SCOT.shiftContractObservableMdlRefinedContinuumScale
        (CAMI.canonicalTransportState x))
  sourceEq x ax =
    trans
      (sourceMdlToTransportedSchedule x ax)
      (transportedScheduleMdlToNoncanonicalContinuum x)

  evolveEq :
    ∀ x →
    SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
    CAMI.canonicalMdlLevel (CAMI.canonicalClosureDynamics x)
      ≡
    CNCRI.noncanonicalMdl
      (SCOT.shiftContractObservableMdlRefinedContinuumScale
        (CAMI.canonicalTransportState x))
  evolveEq x ax =
    trans
      (sym (canonicalMdlLevelPreserved x))
      (sourceEq x ax)

module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCurrentCarrierObstruction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as Align
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Sharper current-carrier obstruction for the MDL/CR seam.
--
-- The existing canonical carrier has three points.  None is an aligned
-- current noncanonical MDL channel:
-- * `CR` has source-to-schedule, but schedule-to-current-noncanonical is
--   obstructed.
-- * `CP` and `CC` have schedule-to-current-noncanonical by the sibling
--   blocker module, but source-to-schedule is obstructed.

record CurrentCarrierAlignedMdlChannel
  (x : CNCRI.CanonicalCarrier)
  : Set where
  field
    sourceToSchedule :
      Seam.transportedScheduleMdl x

    scheduleToCurrentNoncanonical :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState x)))
        ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState x))

currentCarrierAlignedMdlChannel-obstructed :
  (x : CNCRI.CanonicalCarrier) →
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
  CurrentCarrierAlignedMdlChannel x →
  ⊥
currentCarrierAlignedMdlChannel-obstructed CI.CR _ aligned =
  Align.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
    (CurrentCarrierAlignedMdlChannel.scheduleToCurrentNoncanonical aligned)
currentCarrierAlignedMdlChannel-obstructed CI.CP admissible aligned =
  Source.sourceCanonicalToScheduleMdl-CP-obstructed
    admissible
    (CurrentCarrierAlignedMdlChannel.sourceToSchedule aligned)
currentCarrierAlignedMdlChannel-obstructed CI.CC admissible aligned =
  Source.sourceCanonicalToScheduleMdl-CC-obstructed
    admissible
    (CurrentCarrierAlignedMdlChannel.sourceToSchedule aligned)

record CanonicalToNoncanonicalMdlCurrentCarrierObstruction : Set where
  field
    noCurrentAlignedCarrier :
      (x : CNCRI.CanonicalCarrier) →
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState x) →
      CurrentCarrierAlignedMdlChannel x →
      ⊥

canonicalToNoncanonicalMdlCurrentCarrierObstruction :
  CanonicalToNoncanonicalMdlCurrentCarrierObstruction
canonicalToNoncanonicalMdlCurrentCarrierObstruction =
  record
    { noCurrentAlignedCarrier =
        currentCarrierAlignedMdlChannel-obstructed
    }

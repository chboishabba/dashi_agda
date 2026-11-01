module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlBranchResolved where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as Coarse
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as Target
import DASHI.Physics.Closure.RGObservableInvariance as RGOI
import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- MDL seam resolution by honest case split.
--
-- The old desired global object is impossible on the current carrier:
--   * CR has source canonical-to-schedule MDL.
--   * CP and CC have schedule-to-noncanonical MDL alignment.
--   * CR has an explicit schedule-to-noncanonical obstruction.
--
-- Therefore the blocker is not fixed by forcing a bigger equality.  It is
-- fixed by replacing the false global theorem target with the branch-resolved
-- theorem below, and by exposing the no-global theorem as a real result.

noGlobalMdlSourceScheduleObligation :
  Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation → ⊥
noGlobalMdlSourceScheduleObligation full =
  Target.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
    (Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation.transportedScheduleMdlToNoncanonicalContinuum
      full
      CI.CR)

record CanonicalToNoncanonicalMdlBranchResolved : Setω where
  field
    sourceCanonicalToSchedule-CR :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
      Seam.transportedScheduleMdl CI.CR

    sourceCanonicalToSchedule-CP-obstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CP) →
      Seam.transportedScheduleMdl CI.CP →
      ⊥

    sourceCanonicalToSchedule-CC-obstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CC) →
      Seam.transportedScheduleMdl CI.CC →
      ⊥

    scheduleToNoncanonical-CP :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CP)))
      ≡
      Coarse.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState CI.CP))

    scheduleToNoncanonical-CC :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CC)))
      ≡
      Coarse.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState CI.CC))

    scheduleToNoncanonical-CR-obstructed :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CR)))
      ≡
      Coarse.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState CI.CR))
      →
      ⊥

    fullGlobalSeamImpossible :
      Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation → ⊥

canonicalToNoncanonicalMdlBranchResolved :
  CanonicalToNoncanonicalMdlBranchResolved
canonicalToNoncanonicalMdlBranchResolved = record
  { sourceCanonicalToSchedule-CR =
      Source.sourceCanonicalToScheduleMdl-CR
  ; sourceCanonicalToSchedule-CP-obstructed =
      Source.sourceCanonicalToScheduleMdl-CP-obstructed
  ; sourceCanonicalToSchedule-CC-obstructed =
      Source.sourceCanonicalToScheduleMdl-CC-obstructed
  ; scheduleToNoncanonical-CP =
      Target.transportedScheduleMdlToNoncanonicalContinuum-CP
  ; scheduleToNoncanonical-CC =
      Target.transportedScheduleMdlToNoncanonicalContinuum-CC
  ; scheduleToNoncanonical-CR-obstructed =
      Target.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
  ; fullGlobalSeamImpossible =
      noGlobalMdlSourceScheduleObligation
  }

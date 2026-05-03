module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetRequirement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Alternative honest way to break the MDL blockage on CR.
--
-- Since the existing CR schedule-to-current-noncanonical target is obstructed,
-- a CR theorem must either:
--   1. change the target channel, or
--   2. provide a new noncanonical MDL projection for CR.
--
-- This module states that retargeting obligation.  It does not pretend the
-- current target aligns.

record CanonicalToNoncanonicalMdlCRRetargetRequirement : Setω where
  field
    crAdmissible :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR)

    replacementNoncanonicalMdlCR : Nat

    replacementIsScheduleVisible :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CR)))
      ≡
      replacementNoncanonicalMdlCR

    replacementIsSourceVisible :
      CAMI.canonicalMdlLevel CI.CR
      ≡
      replacementNoncanonicalMdlCR

    retargetBoundary : List String

record CanonicalToNoncanonicalMdlCRRetargetTheorem : Setω where
  field
    requirement : CanonicalToNoncanonicalMdlCRRetargetRequirement

    sourceToReplacementCR :
      CAMI.canonicalMdlLevel CI.CR
      ≡
      CanonicalToNoncanonicalMdlCRRetargetRequirement.replacementNoncanonicalMdlCR
        requirement

    scheduleToReplacementCR :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CR)))
      ≡
      CanonicalToNoncanonicalMdlCRRetargetRequirement.replacementNoncanonicalMdlCR
        requirement

crRetargetRequirementToTheorem :
  (req : CanonicalToNoncanonicalMdlCRRetargetRequirement) →
  CanonicalToNoncanonicalMdlCRRetargetTheorem
crRetargetRequirementToTheorem req =
  record
    { requirement = req
    ; sourceToReplacementCR =
        CanonicalToNoncanonicalMdlCRRetargetRequirement.replacementIsSourceVisible req
    ; scheduleToReplacementCR =
        CanonicalToNoncanonicalMdlCRRetargetRequirement.replacementIsScheduleVisible req
    }

currentCRSourceBridge :
  (req : CanonicalToNoncanonicalMdlCRRetargetRequirement) →
  Seam.transportedScheduleMdl CI.CR
currentCRSourceBridge req =
  Source.sourceCanonicalToScheduleMdl-CR
    (CanonicalToNoncanonicalMdlCRRetargetRequirement.crAdmissible req)

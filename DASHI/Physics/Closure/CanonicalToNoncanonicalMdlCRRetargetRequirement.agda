module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetRequirement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRAdmissibilityWitness as CRWitness
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- First non-vacuous continuum blocker route after the CR-only mismatch split.
--
-- The current target channel is explicitly obstructed on `CR`, so the honest
-- next local move is not another global alignment theorem. It is a pure
-- requirement describing what a replacement `CR` noncanonical MDL target would
-- have to provide in order to collapse the live cross-channel mismatch.

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

transportedScheduleMdlCR :
  Nat
transportedScheduleMdlCR =
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe
      SRGOI.shiftRGSurface
      (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CR)))

crTransportedScheduleRetargetRequirement :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
  CanonicalToNoncanonicalMdlCRRetargetRequirement
crTransportedScheduleRetargetRequirement admissible =
  record
    { crAdmissible = admissible
    ; replacementNoncanonicalMdlCR = transportedScheduleMdlCR
    ; replacementIsScheduleVisible = refl
    ; replacementIsSourceVisible =
        Source.sourceCanonicalToScheduleMdl-CR admissible
    ; retargetBoundary =
        "CR retarget keeps the already-witnessed transported schedule MDL channel as the replacement target"
        ∷ "It does not prove the obstructed current noncanonical continuum target aligns"
        ∷ "Any stronger retarget still has to be justified locally as a better noncanonical MDL channel"
        ∷ []
    }

canonicalCRTransportedScheduleRetargetRequirement :
  CanonicalToNoncanonicalMdlCRRetargetRequirement
canonicalCRTransportedScheduleRetargetRequirement =
  crTransportedScheduleRetargetRequirement
    CRWitness.canonicalTransportStateCR-shiftRGAdmissible

canonicalCRTransportedScheduleRetargetTheorem :
  CanonicalToNoncanonicalMdlCRRetargetTheorem
canonicalCRTransportedScheduleRetargetTheorem =
  crRetargetRequirementToTheorem
    canonicalCRTransportedScheduleRetargetRequirement

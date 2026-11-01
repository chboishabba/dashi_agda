module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlAlignedChannelRequirement where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

------------------------------------------------------------------------
-- The actual MDL blockage breaker.
--
-- Existing current split:
--   * CR has source canonical-to-schedule MDL;
--   * CP/CC have schedule-to-noncanonical MDL alignment;
--   * the old all-carrier source-schedule obligation is impossible.
--
-- So the missing ingredient is not another package.  It is one aligned channel
-- where source-to-schedule and schedule-to-noncanonical are both available for
-- the same carrier, or else an explicitly new target channel replacing the
-- obstructed CR noncanonical MDL target.

record CanonicalToNoncanonicalMdlAlignedChannelRequirement : Setω where
  field
    carrier : CNCRI.CanonicalCarrier

    admissible :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState carrier)

    sourceCanonicalToSchedule :
      CAMI.canonicalMdlLevel carrier
      ≡
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState carrier)))

    scheduleToNoncanonical :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState carrier)))
      ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState carrier))

    nonClaimBoundary : List String

record CanonicalToNoncanonicalMdlAlignedChannelTheorem : Setω where
  field
    requirement : CanonicalToNoncanonicalMdlAlignedChannelRequirement

    sourceToNoncanonical :
      CAMI.canonicalMdlLevel
        (CanonicalToNoncanonicalMdlAlignedChannelRequirement.carrier requirement)
      ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState
            (CanonicalToNoncanonicalMdlAlignedChannelRequirement.carrier requirement)))

open import Relation.Binary.PropositionalEquality using (trans)

alignedChannelRequirementToTheorem :
  (req : CanonicalToNoncanonicalMdlAlignedChannelRequirement) →
  CanonicalToNoncanonicalMdlAlignedChannelTheorem
alignedChannelRequirementToTheorem req =
  record
    { requirement = req
    ; sourceToNoncanonical =
        trans
          (CanonicalToNoncanonicalMdlAlignedChannelRequirement.sourceCanonicalToSchedule req)
          (CanonicalToNoncanonicalMdlAlignedChannelRequirement.scheduleToNoncanonical req)
    }

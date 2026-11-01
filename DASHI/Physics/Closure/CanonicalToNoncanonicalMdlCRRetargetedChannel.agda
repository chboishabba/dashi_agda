module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Positive retargeted channel after the current-carrier obstruction.
--
-- This is not the old current noncanonical continuum target.  It names the
-- transported schedule MDL readout as the replacement noncanonical MDL channel.
-- The new inhabited leg is schedule visibility for every current carrier.
-- Source visibility remains classified: `CR` is inhabited, `CP`/`CC` are
-- obstructed by the existing source-to-schedule blockers.

transportedScheduleMdlChannel :
  CNCRI.CanonicalCarrier → Nat
transportedScheduleMdlChannel x =
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe
      SRGOI.shiftRGSurface
      (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState x)))

record CanonicalToNoncanonicalMdlCRRetargetedChannel : Set where
  field
    replacementNoncanonicalMdl :
      CNCRI.CanonicalCarrier → Nat

    scheduleVisible :
      ∀ x →
      transportedScheduleMdlChannel x
        ≡
      replacementNoncanonicalMdl x

    sourceVisibleCR :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
      CAMI.canonicalMdlLevel CI.CR
        ≡
      replacementNoncanonicalMdl CI.CR

    sourceVisibleCP-obstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CP) →
      CAMI.canonicalMdlLevel CI.CP
        ≡
      replacementNoncanonicalMdl CI.CP
      →
      ⊥

    sourceVisibleCC-obstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CC) →
      CAMI.canonicalMdlLevel CI.CC
        ≡
      replacementNoncanonicalMdl CI.CC
      →
      ⊥

canonicalToNoncanonicalMdlCRRetargetedChannel :
  CanonicalToNoncanonicalMdlCRRetargetedChannel
canonicalToNoncanonicalMdlCRRetargetedChannel =
  record
    { replacementNoncanonicalMdl =
        transportedScheduleMdlChannel
    ; scheduleVisible =
        λ _ → refl
    ; sourceVisibleCR =
        Source.sourceCanonicalToScheduleMdl-CR
    ; sourceVisibleCP-obstructed =
        Source.sourceCanonicalToScheduleMdl-CP-obstructed
    ; sourceVisibleCC-obstructed =
        Source.sourceCanonicalToScheduleMdl-CC-obstructed
    }

retargetedChannelScheduleLegCR :
  transportedScheduleMdlChannel CI.CR
    ≡
  CanonicalToNoncanonicalMdlCRRetargetedChannel.replacementNoncanonicalMdl
    canonicalToNoncanonicalMdlCRRetargetedChannel
    CI.CR
retargetedChannelScheduleLegCR =
  CanonicalToNoncanonicalMdlCRRetargetedChannel.scheduleVisible
    canonicalToNoncanonicalMdlCRRetargetedChannel
    CI.CR

retargetedChannelSourceLegCR :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
  Seam.transportedScheduleMdl CI.CR
retargetedChannelSourceLegCR =
  Source.sourceCanonicalToScheduleMdl-CR

record CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption : Setω where
  field
    acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget :
      (channel : CanonicalToNoncanonicalMdlCRRetargetedChannel) →
      Set

record CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted : Setω where
  field
    channel :
      CanonicalToNoncanonicalMdlCRRetargetedChannel

    policyAssumption :
      CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption

    acceptedAsIntendedNoncanonicalMdlTarget :
      CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption.acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget
        policyAssumption
        channel

    acceptedReplacementIsTransportedSchedule :
      ∀ x →
      transportedScheduleMdlChannel x
        ≡
      CanonicalToNoncanonicalMdlCRRetargetedChannel.replacementNoncanonicalMdl
        channel
        x

canonicalToNoncanonicalMdlCRRetargetPolicyAccepted :
  (policyAssumption : CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption) →
  CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption.acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget
    policyAssumption
    canonicalToNoncanonicalMdlCRRetargetedChannel →
  CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalToNoncanonicalMdlCRRetargetPolicyAccepted policyAssumption accepted =
  record
    { channel =
        canonicalToNoncanonicalMdlCRRetargetedChannel
    ; policyAssumption =
        policyAssumption
    ; acceptedAsIntendedNoncanonicalMdlTarget =
        accepted
    ; acceptedReplacementIsTransportedSchedule =
        CanonicalToNoncanonicalMdlCRRetargetedChannel.scheduleVisible
          canonicalToNoncanonicalMdlCRRetargetedChannel
    }

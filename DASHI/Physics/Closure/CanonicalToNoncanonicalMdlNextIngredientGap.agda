module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlNextIngredientGap where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as Source
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRChannelMismatchFamily as CRMismatch
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCurrentCarrierObstruction as CurrentCarrier
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetRequirement as CRRetarget
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as RetargetedChannel
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlGlobalObligationImpossible as GlobalImpossible
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as C2NMST
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractMdlLevelOrbitSummaryControlAttempt as SCMLOCA
open import DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge as SCMPB
open import DASHI.Physics.Closure.ShiftContractMdlLevelPrimeOrOrbitControl as SCMPOC
open import DASHI.Physics.Closure.ShiftContractMdlLevelWitnessSourceAudit as SCMWSA
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Next honest route beyond the current MDL seam blocker.
--
-- What is already established:
-- * the evolve-side MDL equality is not an independent blocker;
-- * a source-side obligation plus a scheduled-MDL alignment obligation
--   suffice to recover the full MDL-refined seam;
-- * the noncanonical side already has a theorem-bearing mdl-level/p2 bridge,
--   but not a positive same-surface witness that closes the alignment seam.
--
-- So the current blocker splits into two bounded sublanes:
-- 1. CR retarget: canonical source -> transported schedule MDL, used as the
--    replacement CR noncanonical MDL target;
-- 2. aligned channel: find one carrier where canonical source -> schedule and
--    schedule -> noncanonical both hold.
--
-- The old global source-schedule obligation is recorded as impossible, not as
-- a remaining target.

record CanonicalToNoncanonicalMdlCRRetargetPolicyIngredient : Setω where
  field
    policyAssumption :
      RetargetedChannel.CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption

    acceptsRetargetedChannel :
      RetargetedChannel.CanonicalToNoncanonicalMdlCRRetargetPolicyAssumption.acceptsTransportedScheduleAsIntendedNoncanonicalMdlTarget
        policyAssumption
        RetargetedChannel.canonicalToNoncanonicalMdlCRRetargetedChannel

record CanonicalToNoncanonicalMdlNextIngredientGap : Setω where
  field
    rejectedGlobalObligationImpossible :
      C2NMST.CanonicalToNoncanonicalMdlSourceScheduleObligation →
      ⊥

    oldSeamReductionIfGlobalWereAvailable :
      C2NMST.CanonicalToNoncanonicalMdlSourceScheduleObligation →
      CNCRI.CanonicalToNoncanonicalMdlRefinedRecoveryIdentification

    crChannelMismatch :
      CRMismatch.CanonicalToNoncanonicalMdlCRChannelMismatchFamily

    crRetargetTheorem :
      CRRetarget.CanonicalToNoncanonicalMdlCRRetargetTheorem

    crRetargetedChannel :
      RetargetedChannel.CanonicalToNoncanonicalMdlCRRetargetedChannel

    crRetargetPolicyAcceptanceFromIngredient :
      CanonicalToNoncanonicalMdlCRRetargetPolicyIngredient →
      RetargetedChannel.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    currentCarrierObstruction :
      CurrentCarrier.CanonicalToNoncanonicalMdlCurrentCarrierObstruction

    currentCRScheduleAlignmentObstructed :
      RGOI.RGObservable.mdlLevel
        (RGOI.RGObservableSurface.observe
          SRGOI.shiftRGSurface
          (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CR)))
        ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState CI.CR))
      →
      ⊥

    sourceScheduleCPObstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CP) →
      C2NMST.transportedScheduleMdl CI.CP →
      ⊥

    sourceScheduleCCObstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CC) →
      C2NMST.transportedScheduleMdl CI.CC →
      ⊥

    noncanonicalMdlPrimeBridge :
      SCMPB.ShiftContractMdlLevelP2PrimeBridge

    noncanonicalPrimeOrOrbitControl :
      SCMPOC.ShiftContractMdlLevelPrimeOrOrbitControlAttempt

    noncanonicalOrbitSummaryControl :
      SCMLOCA.ShiftContractMdlLevelOrbitSummaryControlAttempt

    witnessSourceAudit :
      SCMWSA.ShiftContractMdlLevelWitnessSourceAudit

canonicalToNoncanonicalMdlNextIngredientGap :
  CanonicalToNoncanonicalMdlNextIngredientGap
canonicalToNoncanonicalMdlNextIngredientGap =
  record
    { rejectedGlobalObligationImpossible =
        GlobalImpossible.oldGlobalSourceScheduleObligationImpossible
    ; oldSeamReductionIfGlobalWereAvailable =
        C2NMST.sourceScheduleObligation-to-MdlRefinedRecovery
    ; crChannelMismatch =
        CRMismatch.canonicalToNoncanonicalMdlCRChannelMismatchFamily
    ; crRetargetTheorem =
        CRRetarget.canonicalCRTransportedScheduleRetargetTheorem
    ; crRetargetedChannel =
        RetargetedChannel.canonicalToNoncanonicalMdlCRRetargetedChannel
    ; crRetargetPolicyAcceptanceFromIngredient =
        λ ingredient →
          RetargetedChannel.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
            (CanonicalToNoncanonicalMdlCRRetargetPolicyIngredient.policyAssumption ingredient)
            (CanonicalToNoncanonicalMdlCRRetargetPolicyIngredient.acceptsRetargetedChannel ingredient)
    ; currentCarrierObstruction =
        CurrentCarrier.canonicalToNoncanonicalMdlCurrentCarrierObstruction
    ; currentCRScheduleAlignmentObstructed =
        CRMismatch.CanonicalToNoncanonicalMdlCRChannelMismatchFamily.scheduleToNoncanonicalCR-obstructed
          CRMismatch.canonicalToNoncanonicalMdlCRChannelMismatchFamily
    ; sourceScheduleCPObstructed =
        Source.sourceCanonicalToScheduleMdl-CP-obstructed
    ; sourceScheduleCCObstructed =
        Source.sourceCanonicalToScheduleMdl-CC-obstructed
    ; noncanonicalMdlPrimeBridge =
        SCMPB.canonicalShiftContractMdlLevelP2PrimeBridge
    ; noncanonicalPrimeOrOrbitControl =
        SCMPOC.canonicalShiftContractMdlLevelPrimeOrOrbitControlAttempt
    ; noncanonicalOrbitSummaryControl =
        SCMLOCA.canonicalShiftContractMdlLevelOrbitSummaryControlAttempt
    ; witnessSourceAudit =
        SCMWSA.canonicalShiftContractMdlLevelWitnessSourceAudit
    }

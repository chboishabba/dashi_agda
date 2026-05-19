module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRCrossChannelObstruction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as CCSMSB
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as C2NMST
open import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as C2NSMAB
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Remaining continuum blocker after the carrier split:
-- * source canonical-to-schedule MDL is already bridged on `CR`;
-- * schedule-to-noncanonical MDL alignment is obstructed on `CR`;
-- so the live blocker is exactly the `CR` cross-channel mismatch.

record CanonicalToNoncanonicalMdlCRCrossChannelObstruction : Set where
  field
    sourceBridgeCR :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
      C2NMST.transportedScheduleMdl CI.CR

    scheduleAlignmentCR-obstructed :
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

    sourceToNoncanonicalCR-obstructed :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
      CAMI.canonicalMdlLevel CI.CR
        ≡
      CNCRI.noncanonicalMdl
        (SCOT.shiftContractObservableMdlRefinedContinuumScale
          (CAMI.canonicalTransportState CI.CR))
      →
      ⊥

canonicalToNoncanonicalMdlCRCrossChannelObstruction :
  CanonicalToNoncanonicalMdlCRCrossChannelObstruction
canonicalToNoncanonicalMdlCRCrossChannelObstruction =
  record
    { sourceBridgeCR = CCSMSB.sourceCanonicalToScheduleMdl-CR
    ; scheduleAlignmentCR-obstructed =
        C2NSMAB.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
    ; sourceToNoncanonicalCR-obstructed =
        λ ax eq →
          C2NSMAB.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
            (trans
              (CCSMSB.sourceCanonicalToScheduleMdl-CR ax)
              eq)
    }

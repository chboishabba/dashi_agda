module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRChannelMismatchFamily where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge as CCSMSB
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRCrossChannelObstruction as C2NMCR
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as C2NMST
open import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as C2NSMAB
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Channel-classified view of the remaining CR continuum blocker.
--
-- The live mismatch is no longer a generic seam failure. On `CR`:
-- * canonical source MDL agrees with transported schedule MDL;
-- * transported schedule MDL does not agree with noncanonical continuum MDL;
-- * therefore canonical source MDL does not agree with noncanonical continuum
--   MDL.

data MdlChannel : Set where
  canonicalSource : MdlChannel
  transportedSchedule : MdlChannel
  noncanonicalContinuum : MdlChannel

record CanonicalToNoncanonicalMdlCRChannelMismatchFamily : Set where
  field
    leftChannel : MdlChannel
    middleChannel : MdlChannel
    rightChannel : MdlChannel

    sourceToScheduleCR :
      SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
      C2NMST.transportedScheduleMdl CI.CR

    scheduleToNoncanonicalCR-obstructed :
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

canonicalToNoncanonicalMdlCRChannelMismatchFamily :
  CanonicalToNoncanonicalMdlCRChannelMismatchFamily
canonicalToNoncanonicalMdlCRChannelMismatchFamily =
  record
    { leftChannel = canonicalSource
    ; middleChannel = transportedSchedule
    ; rightChannel = noncanonicalContinuum
    ; sourceToScheduleCR = CCSMSB.sourceCanonicalToScheduleMdl-CR
    ; scheduleToNoncanonicalCR-obstructed =
        C2NSMAB.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
    ; sourceToNoncanonicalCR-obstructed =
        C2NMCR.CanonicalToNoncanonicalMdlCRCrossChannelObstruction.sourceToNoncanonicalCR-obstructed
          C2NMCR.canonicalToNoncanonicalMdlCRCrossChannelObstruction
    }

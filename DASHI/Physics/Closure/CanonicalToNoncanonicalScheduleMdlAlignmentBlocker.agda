module DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalCoarseRecoveryIdentification as CNCRI
open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Remaining noncanonical-side MDL blocker from the continuum seam board.
--
-- The target side is the MDL-refined noncanonical continuum scale, whose MDL
-- component is built from the same scheduled observable channel used by the
-- transported schedule surface. On the bounded canonical carrier, the
-- alignment closes on `CP` and `CC`, while `CR` is explicitly obstructed.

transportedScheduleMdlToNoncanonicalContinuum-CP :
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe
      SRGOI.shiftRGSurface
      (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CP)))
    ≡
  CNCRI.noncanonicalMdl
    (SCOT.shiftContractObservableMdlRefinedContinuumScale
      (CAMI.canonicalTransportState CI.CP))
transportedScheduleMdlToNoncanonicalContinuum-CP = refl

transportedScheduleMdlToNoncanonicalContinuum-CC :
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe
      SRGOI.shiftRGSurface
      (SRGOI.shiftCoarseAlt (CAMI.canonicalTransportState CI.CC)))
    ≡
  CNCRI.noncanonicalMdl
    (SCOT.shiftContractObservableMdlRefinedContinuumScale
      (CAMI.canonicalTransportState CI.CC))
transportedScheduleMdlToNoncanonicalContinuum-CC = refl

transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed :
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
transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed ()

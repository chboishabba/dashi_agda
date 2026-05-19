module DASHI.Physics.Closure.CanonicalP2KeyScheduleBridgeObstruction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryControlAttempt as SCEC
open import DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge as SCMPB
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeLaw as CSINCL

------------------------------------------------------------------------
-- First-class obstruction surface for the missing positive `p2` carrier /
-- schedule bridge.
--
-- What the current repo does have:
-- * a schedule-independent coarse natural charge law, and
-- * a strengthened mdl-level × π-max prime-field bridge that carries `p2`
--   orbit-summary control on the shift-contract side.
--
-- What it still does not have:
-- * a positive canonical carrier / transported schedule bridge for that `p2`
--   key.
--
-- The obstruction is honest and narrow: the current normalized
-- eigenShadow × π-max surface is too weak to force the `p2` orbit summary on
-- canonical fibres.

record CanonicalP2KeyScheduleBridgeObstruction : Setω where
  field
    baseLaw :
      CSINCL.CanonicalScheduleIndependentNaturalChargeLaw

    normalizedSurfaceTooWeak :
      (∀ {q} →
        (x y : CCF.CanonicalFibre q) →
        SCEC.canonicalNormalizedEigenShadow (CCF.carrier x)
          ≡
        SCEC.canonicalNormalizedEigenShadow (CCF.carrier y) →
        FOS.profileSummaryAt p2 (CCFF.primeField x)
          ≡
        FOS.profileSummaryAt p2 (CCFF.primeField y)) →
      ⊥

    mdlPrimeBridgeAvailable :
      SCMPB.ShiftContractMdlLevelP2PrimeBridge

canonicalP2KeyScheduleBridgeObstruction :
  CanonicalP2KeyScheduleBridgeObstruction
canonicalP2KeyScheduleBridgeObstruction =
  record
    { baseLaw = CSINCL.canonicalScheduleIndependentNaturalChargeLaw
    ; normalizedSurfaceTooWeak =
        SCEC.canonicalSameSurfaceButNoP2OrbitSummaryControl
    ; mdlPrimeBridgeAvailable =
        SCMPB.canonicalShiftContractMdlLevelP2PrimeBridge
    }

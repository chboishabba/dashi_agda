module DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeNextIngredientGap where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.Closure.CanonicalP2KeyScheduleBridgeObstruction as CPKSO
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeLaw as CSINCL
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeWideningObstruction as CSINCWO

------------------------------------------------------------------------
-- Next honest route beyond the current widening obstruction.
--
-- The repo already has:
-- * a schedule-independent coarse conserved law, and
-- * a fibre-local `p2` orbit-summary key that controls `eigenShadow` and
--   `hecke` on the current coarse quotient.
--
-- The missing ingredient is a carrier/schedule bridge for that `p2` key.
-- Once such a bridge exists, the existing fibre factor laws are enough to
-- recover a strictly richer quotient-visible invariant than
-- `Gauge × basin × motif`.

-- W2 is an obstruction/gap lane. Keep the p2-key/factor-law bridge abstract
-- here so this diagnostic surface does not force the full fibre proof spine to
-- normalize while checking downstream governance modules.
postulate
  CanonicalCarrier :
    Set

  P2Key :
    Set

  ScheduleAdmissible :
    CanonicalCarrier →
    Set

  sourceP2Key :
    CanonicalCarrier →
    P2Key

  evolveP2Key :
    CanonicalCarrier →
    P2Key

  scheduleP2Key :
    CanonicalCarrier →
    P2Key

  eigenShadowLevel :
    CanonicalCarrier →
    P2Key

  heckeSignatureLevel :
    CanonicalCarrier →
    P2Key

  closureDynamics :
    CanonicalCarrier →
    CanonicalCarrier

record CanonicalP2KeyScheduleBridge : Setω where
  field
    source-to-schedule :
      ∀ x →
      ScheduleAdmissible x →
      sourceP2Key x ≡ scheduleP2Key x

    evolve-to-schedule :
      ∀ x →
      ScheduleAdmissible x →
      evolveP2Key x ≡ scheduleP2Key x

source-evolve-p2-agreement :
  (br : CanonicalP2KeyScheduleBridge) →
  ∀ x →
  ScheduleAdmissible x →
  sourceP2Key x ≡ evolveP2Key x
source-evolve-p2-agreement br x ax =
  trans
    (CanonicalP2KeyScheduleBridge.source-to-schedule br x ax)
    (sym (CanonicalP2KeyScheduleBridge.evolve-to-schedule br x ax))

postulate
  p2-bridge-unlocks-eigenShadow :
    (br : CanonicalP2KeyScheduleBridge) →
    ∀ x →
    ScheduleAdmissible x →
    eigenShadowLevel x ≡ eigenShadowLevel (closureDynamics x)

  p2-bridge-unlocks-hecke :
    (br : CanonicalP2KeyScheduleBridge) →
    ∀ x →
    ScheduleAdmissible x →
    heckeSignatureLevel x ≡ heckeSignatureLevel (closureDynamics x)

record CanonicalScheduleIndependentNaturalChargeNextIngredientGap : Setω where
  field
    baseLaw :
      CSINCL.CanonicalScheduleIndependentNaturalChargeLaw
    wideningObstruction :
      CSINCWO.CanonicalScheduleIndependentNaturalChargeWideningObstruction
    bridgeObstruction :
      CPKSO.CanonicalP2KeyScheduleBridgeObstruction
    bridgeWouldUnlockEigenShadow :
      CanonicalP2KeyScheduleBridge →
      ∀ x →
      ScheduleAdmissible x →
      eigenShadowLevel x ≡ eigenShadowLevel (closureDynamics x)
    bridgeWouldUnlockHecke :
      CanonicalP2KeyScheduleBridge →
      ∀ x →
      ScheduleAdmissible x →
      heckeSignatureLevel x ≡ heckeSignatureLevel (closureDynamics x)

canonicalScheduleIndependentNaturalChargeNextIngredientGap :
  CanonicalScheduleIndependentNaturalChargeNextIngredientGap
canonicalScheduleIndependentNaturalChargeNextIngredientGap =
  record
    { baseLaw = CSINCL.canonicalScheduleIndependentNaturalChargeLaw
    ; wideningObstruction =
        CSINCWO.canonicalScheduleIndependentNaturalChargeWideningObstruction
    ; bridgeObstruction =
        CPKSO.canonicalP2KeyScheduleBridgeObstruction
    ; bridgeWouldUnlockEigenShadow = p2-bridge-unlocks-eigenShadow
    ; bridgeWouldUnlockHecke = p2-bridge-unlocks-hecke
    }

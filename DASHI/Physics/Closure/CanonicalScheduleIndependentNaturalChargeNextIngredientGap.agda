module DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeNextIngredientGap where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalChamberToShiftWitnessBridgeInstance as CCW
open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.CanonicalClosureFibreOrbitSummaryControl as CCFOC
open import DASHI.Physics.Closure.CanonicalClosureShiftScheduleBridge as CCSB
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.CanonicalP2KeyScheduleBridgeObstruction as CPKSO
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeLaw as CSINCL
open import DASHI.Physics.Closure.CanonicalScheduleIndependentNaturalChargeWideningObstruction as CSINCWO
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryControlAttempt as SCEC
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI

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

CanonicalCarrier : Set
CanonicalCarrier = CCGP.Carrier PGCT.canonicalConstraintGaugePackage

sourceFibre :
  (x : CanonicalCarrier) →
  CCF.CanonicalFibre (CCF.π x)
sourceFibre x = x , refl

evolveFibre :
  (x : CanonicalCarrier) →
  CCF.CanonicalFibre (CCF.π x)
evolveFibre x =
  CA.canonicalClosureDynamics x
  , sym (CCSB.closureMotifObservablePreserved x)

sourceP2Key :
  CanonicalCarrier →
  FOS.DefectOrbitSummary
sourceP2Key x = CCFOC.p2-key (sourceFibre x)

evolveP2Key :
  CanonicalCarrier →
  FOS.DefectOrbitSummary
evolveP2Key x = CCFOC.p2-key (evolveFibre x)

scheduleP2Key :
  CanonicalCarrier →
  FOS.DefectOrbitSummary
scheduleP2Key x =
  FOS.profileSummaryAt p2
    (SRGOI.shiftPrimeEmbedding
      (SRGOI.canonicalShiftHeckeState
        (SRGOI.shiftCoarseAlt (CA.canonicalTransportState x))))

record CanonicalP2KeyScheduleBridge : Setω where
  field
    source-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      sourceP2Key x ≡ scheduleP2Key x

    evolve-to-schedule :
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      evolveP2Key x ≡ scheduleP2Key x

source-evolve-p2-agreement :
  (br : CanonicalP2KeyScheduleBridge) →
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  sourceP2Key x ≡ evolveP2Key x
source-evolve-p2-agreement br x ax =
  trans
    (CanonicalP2KeyScheduleBridge.source-to-schedule br x ax)
    (sym (CanonicalP2KeyScheduleBridge.evolve-to-schedule br x ax))

p2-bridge-unlocks-eigenShadow :
  (br : CanonicalP2KeyScheduleBridge) →
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  CA.canonicalEigenShadowLevel x
    ≡
  CA.canonicalEigenShadowLevel (CA.canonicalClosureDynamics x)
p2-bridge-unlocks-eigenShadow br x ax =
  CCFOC.P2EigenShadowFactorLaw.eigenShadow-from-key
    (CCFOC.canonicalP2EigenShadowFactorLaw {q = CCF.π x})
    (sourceFibre x)
    (evolveFibre x)
    (source-evolve-p2-agreement br x ax)

p2-bridge-unlocks-hecke :
  (br : CanonicalP2KeyScheduleBridge) →
  ∀ x →
  SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
  CA.canonicalSignatureLevel x
    ≡
  CA.canonicalSignatureLevel (CA.canonicalClosureDynamics x)
p2-bridge-unlocks-hecke br x ax =
  CCFOC.P2HeckeFactorLaw.hecke-from-key
    (CCFOC.canonicalP2HeckeFactorLaw {q = CCF.π x})
    (sourceFibre x)
    (evolveFibre x)
    (source-evolve-p2-agreement br x ax)

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
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      CA.canonicalEigenShadowLevel x
        ≡
      CA.canonicalEigenShadowLevel (CA.canonicalClosureDynamics x)
    bridgeWouldUnlockHecke :
      CanonicalP2KeyScheduleBridge →
      ∀ x →
      SRGOI.shiftRGAdmissible (CA.canonicalTransportState x) →
      CA.canonicalSignatureLevel x
        ≡
      CA.canonicalSignatureLevel (CA.canonicalClosureDynamics x)

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

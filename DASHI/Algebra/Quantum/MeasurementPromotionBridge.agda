module DASHI.Algebra.Quantum.MeasurementPromotionBridge where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Algebra.QuantumInterface as Legacy

------------------------------------------------------------------------
-- Quantum-inside-DASHI bridge.
--
-- The carrier and reversible evolution remain latent. Measurement creates a
-- classical candidate record. Promotion is a later governance proposition:
-- carrier-native candidacy AND sufficient MDL evidence.
------------------------------------------------------------------------

record ReversibleEvolution {ℓ : Level} (QState : Set ℓ) : Set ℓ where
  field
    step : QState → QState
    inv : QState → QState
    left : ∀ state → inv (step state) ≡ state
    right : ∀ state → step (inv state) ≡ state

open ReversibleEvolution public

record MeasurementOp
  {ℓq ℓd : Level}
  (QState : Set ℓq)
  (Datum : Set ℓd)
  : Set (ℓq ⊔ ℓd) where
  field
    project : QState → QState
    project-idempotent : ∀ state → project (project state) ≡ project state
    measure : QState → Datum

open MeasurementOp public

record MeasurementRecord
  {ℓq ℓd : Level}
  {QState : Set ℓq}
  {Datum : Set ℓd}
  (measurement : MeasurementOp QState Datum)
  : Set (ℓq ⊔ ℓd) where
  field
    latentBefore : QState
    latentProjected : QState
    datum : Datum
    projectedCorrect :
      latentProjected ≡ MeasurementOp.project measurement latentBefore
    datumCorrect :
      datum ≡ MeasurementOp.measure measurement latentBefore

open MeasurementRecord public

runMeasurement :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    (measurement : MeasurementOp QState Datum) →
    QState →
    MeasurementRecord measurement
runMeasurement measurement state =
  record
    { latentBefore = state
    ; latentProjected = MeasurementOp.project measurement state
    ; datum = MeasurementOp.measure measurement state
    ; projectedCorrect = Agda.Builtin.Equality.refl
    ; datumCorrect = Agda.Builtin.Equality.refl
    }

------------------------------------------------------------------------
-- Post-measurement MDL evidence.
--
-- Avoid truncated subtraction on Nat. Positive evidence is represented by the
-- proposition
--
--   structured + selection/search + required margin ≤ null.
--
-- Thus the promotability gap lives over measured classical evidence, never raw
-- amplitudes.
------------------------------------------------------------------------

record MDLEvidenceLedger : Set where
  field
    nullCodeLength : Nat
    structuredCodeLength : Nat
    selectionCost : Nat
    minimumGain : Nat

open MDLEvidenceLedger public

EvidenceSufficient : MDLEvidenceLedger → Set
EvidenceSufficient ledger =
  structuredCodeLength ledger
  + selectionCost ledger
  + minimumGain ledger
  ≤ nullCodeLength ledger

record PromotionPolicy
  {ℓq ℓd : Level}
  {QState : Set ℓq}
  {Datum : Set ℓd}
  (measurement : MeasurementOp QState Datum)
  : Set (lsuc (ℓq ⊔ ℓd)) where
  field
    Candidate : MeasurementRecord measurement → Set (ℓq ⊔ ℓd)
    evidenceLedger : MeasurementRecord measurement → MDLEvidenceLedger

open PromotionPolicy public

Promoted :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    {measurement : MeasurementOp QState Datum} →
    PromotionPolicy measurement →
    MeasurementRecord measurement →
    Set (ℓq ⊔ ℓd)
Promoted policy record =
  Candidate policy record
  × EvidenceSufficient (evidenceLedger policy record)

promote :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    {measurement : MeasurementOp QState Datum}
    (policy : PromotionPolicy measurement)
    (record : MeasurementRecord measurement) →
    Candidate policy record →
    EvidenceSufficient (evidenceLedger policy record) →
    Promoted policy record
promote policy record candidate sufficient = candidate , sufficient

promotion-fail-closed-candidate :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    {measurement : MeasurementOp QState Datum}
    (policy : PromotionPolicy measurement)
    (record : MeasurementRecord measurement) →
    Promoted policy record →
    Candidate policy record
promotion-fail-closed-candidate policy record = proj₁

promotion-fail-closed-evidence :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    {measurement : MeasurementOp QState Datum}
    (policy : PromotionPolicy measurement)
    (record : MeasurementRecord measurement) →
    Promoted policy record →
    EvidenceSufficient (evidenceLedger policy record)
promotion-fail-closed-evidence policy record = proj₂

------------------------------------------------------------------------
-- Full executable seam: latent input → reversible step → measurement record.
-- Promotion remains deliberately outside this pipeline record.
------------------------------------------------------------------------

record QuantumMeasurementPipeline
  {ℓq ℓd : Level}
  {QState : Set ℓq}
  {Datum : Set ℓd}
  (evolution : ReversibleEvolution QState)
  (measurement : MeasurementOp QState Datum)
  : Set (ℓq ⊔ ℓd) where
  field
    stateIn : QState
    stateEvolved : QState
    measurementRecord : MeasurementRecord measurement
    evolvedCorrect : stateEvolved ≡ ReversibleEvolution.step evolution stateIn
    recordStartsAtEvolved :
      MeasurementRecord.latentBefore measurementRecord ≡ stateEvolved

open QuantumMeasurementPipeline public

runPipeline :
  ∀ {ℓq ℓd}
    {QState : Set ℓq}
    {Datum : Set ℓd}
    (evolution : ReversibleEvolution QState)
    (measurement : MeasurementOp QState Datum) →
    QState →
    QuantumMeasurementPipeline evolution measurement
runPipeline evolution measurement state =
  record
    { stateIn = state
    ; stateEvolved = ReversibleEvolution.step evolution state
    ; measurementRecord =
        runMeasurement measurement (ReversibleEvolution.step evolution state)
    ; evolvedCorrect = Agda.Builtin.Equality.refl
    ; recordStartsAtEvolved = Agda.Builtin.Equality.refl
    }

------------------------------------------------------------------------
-- Compatibility adapters for the existing bundled QuantumSys contract.
------------------------------------------------------------------------

legacyEvolution :
  ∀ {ℓ} →
  (system : Legacy.QuantumSys ℓ) →
  ReversibleEvolution (Legacy.QuantumSys.QState system)
legacyEvolution system =
  record
    { step = Legacy.QuantumSys.step system
    ; inv = Legacy.QuantumSys.inv system
    ; left = Legacy.QuantumSys.left system
    ; right = Legacy.QuantumSys.right system
    }

legacyMeasurement :
  ∀ {ℓ} →
  (system : Legacy.QuantumSys ℓ) →
  MeasurementOp
    (Legacy.QuantumSys.QState system)
    (Legacy.QuantumSys.QState system)
legacyMeasurement system =
  record
    { project = Legacy.QuantumSys.meas system
    ; project-idempotent = Legacy.QuantumSys.meas-idem system
    ; measure = Legacy.QuantumSys.meas system
    }

bridgeReading : String
bridgeReading =
  "QState remains latent; reversible evolution precedes measurement; measurement yields candidate classical evidence; promotion requires carrier-native candidacy and sufficient post-measurement MDL evidence."

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRGReopeningDobrushinExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact as Dobrushin

asDobrushinKernel :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Dobrushin.FiniteDobrushinKernel Fine Coarse
asDobrushinKernel step = record
  { Dobrushin.FiniteDobrushinKernel.fineStates =
      Reopen.fineStates step
  ; Dobrushin.FiniteDobrushinKernel.kernel =
      Reopen.reopeningKernel step
  }

reopeningTransportIsDobrushinTransport :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    observable coarse →
  Reopen.transportObservable step observable coarse
  ≡ Dobrushin.transport (asDobrushinKernel step) observable coarse
reopeningTransportIsDobrushinTransport step observable coarse = refl

reopeningRowL1Distance :
  ∀ {Fine Coarse} →
  Reopen.FiniteRGReopeningStep Fine Coarse →
  Coarse → Coarse → ℚ
reopeningRowL1Distance step =
  Dobrushin.rowDistance (asDobrushinKernel step)

reopeningTransportOscillationBelowRowL1 :
  ∀ {Fine Coarse}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (observable : Reopen.Observable Fine)
    majorant →
  0ℚ ≤ majorant →
  (∀ fine → ∣ observable fine ∣ ≤ majorant) →
  ∀ left right →
  ∣ Reopen.transportObservable step observable left
    - Reopen.transportObservable step observable right ∣
  ≤ majorant * reopeningRowL1Distance step left right
reopeningTransportOscillationBelowRowL1
    step observable majorant majorantNN bounded left right =
  Dobrushin.transportOscillationBelowRowDistance
    (asDobrushinKernel step)
    observable majorant majorantNN bounded left right

record PhysicalReopeningRowEnvelope
    {Fine Coarse : Set}
    (step : Reopen.FiniteRGReopeningStep Fine Coarse)
    (Distance : Coarse → Coarse → Set) : Set₁ where
  field
    envelope : ∀ {left right} → Distance left right → ℚ
    rowL1BelowEnvelope : ∀ {left right}
      (distance : Distance left right) →
      reopeningRowL1Distance step left right ≤ envelope distance

open PhysicalReopeningRowEnvelope public

reopeningTransportOscillationBelowEnvelope :
  ∀ {Fine Coarse}
    {step : Reopen.FiniteRGReopeningStep Fine Coarse}
    {Distance : Coarse → Coarse → Set}
    (rowEnvelope : PhysicalReopeningRowEnvelope step Distance)
    (observable : Reopen.Observable Fine)
    majorant →
  0ℚ ≤ majorant →
  (∀ fine → ∣ observable fine ∣ ≤ majorant) →
  ∀ {left right} (distance : Distance left right) →
  ∣ Reopen.transportObservable step observable left
    - Reopen.transportObservable step observable right ∣
  ≤ majorant * envelope rowEnvelope distance
reopeningTransportOscillationBelowEnvelope
    {step = step}
    rowEnvelope observable majorant majorantNN bounded distance =
  let
    base =
      reopeningTransportOscillationBelowRowL1
        step observable majorant majorantNN bounded _ _
  in
  ℚP.≤-trans base
    (Dobrushin.transportOscillationBelowEnvelope
      (record
        { Dobrushin.DobrushinRowEnvelope.envelope =
            envelope rowEnvelope
        ; Dobrushin.DobrushinRowEnvelope.rowDistanceBelowEnvelope =
            rowL1BelowEnvelope rowEnvelope
        })
      observable majorant majorantNN bounded distance)
  where
  import Data.Rational.Properties as ℚP

finiteRGReopeningDobrushinSameObjectLevel : ProofLevel
finiteRGReopeningDobrushinSameObjectLevel = machineChecked

finiteRGReopeningOscillationCompilerLevel : ProofLevel
finiteRGReopeningOscillationCompilerLevel = machineChecked

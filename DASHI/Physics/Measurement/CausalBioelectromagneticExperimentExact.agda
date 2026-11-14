module DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact where

-- Reusable typed source -> electromagnetic field -> sensor observation.
-- Separates model composition from claim-specific empirical adequacy.
-- This is not an empirical reconstruction or a solved inverse problem.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

record BioEMForward {ℓ : Level}
  (Intervention Current MagneticField : Set ℓ) : Set ℓ where
  field
    currentFromIntervention : Intervention → Current
    fieldFromCurrent : Current → MagneticField
open BioEMForward public

record MagneticReadout {ℓ : Level}
  (MagneticField Datum : Set ℓ) : Set ℓ where
  field
    observation : MagneticField → Datum
open MagneticReadout public

predictedDatum :
  ∀ {ℓ} {U J B Y : Set ℓ} →
  BioEMForward U J B → MagneticReadout B Y → U → Y
predictedDatum f m u =
  observation m (fieldFromCurrent f (currentFromIntervention f u))

modelCompositionExact :
  ∀ {ℓ} {U J B Y : Set ℓ}
  (f : BioEMForward U J B) (m : MagneticReadout B Y) (u : U) →
  predictedDatum f m u ≡
  observation m (fieldFromCurrent f (currentFromIntervention f u))
modelCompositionExact f m u = refl

-- This is where actual measured data must enter. Neither its existence nor
-- its agreement with a model is inferred from the model's own definition.
record CalibrationReceipt {ℓ : Level}
  {U J B Y : Set ℓ}
  (f : BioEMForward U J B)
  (m : MagneticReadout B Y)
  : Set (lsuc ℓ) where
  field
    actualDatum : U → Y
    AdequateFor : U → Set ℓ
    justifiedAgreement :
      (u : U) → AdequateFor u →
      actualDatum u ≡ predictedDatum f m u
open CalibrationReceipt public

calibratedComposition :
  ∀ {ℓ} {U J B Y : Set ℓ}
  {f : BioEMForward U J B} {m : MagneticReadout B Y} →
  (c : CalibrationReceipt f m) (u : U) →
  AdequateFor c u →
  actualDatum c u ≡
  observation m (fieldFromCurrent f (currentFromIntervention f u))
calibratedComposition c u adequate = justifiedAgreement c u adequate

-- Observational equivalence is weaker than equality of biological sources.
observationallyEquivalent :
  ∀ {ℓ} {U J B Y : Set ℓ} →
  BioEMForward U J B → MagneticReadout B Y → U → U → Set ℓ
observationallyEquivalent f m u v =
  predictedDatum f m u ≡ predictedDatum f m v

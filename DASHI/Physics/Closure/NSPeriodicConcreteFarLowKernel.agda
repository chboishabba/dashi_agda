module DASHI.Physics.Closure.NSPeriodicConcreteFarLowKernel where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Schur
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A literal support-masked weighted kernel.
------------------------------------------------------------------------

record SupportedWeightedKernel
    {r c : Level}
    (A : AbsorptionArithmetic)
    (Row : Set r)
    (Column : Set c) : Set (r ⊔ c) where
  field
    support : Row → Column → Bool
    rawMajorant : Row → Column → Scalar A

open SupportedWeightedKernel public

maskedEntry :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  SupportedWeightedKernel A Row Column → Row → Column → Scalar A
maskedEntry {A = A} K row column with support K row column
... | true = rawMajorant K row column
... | false = zero A

weightedKernel :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  SupportedWeightedKernel A Row Column → Schur.WeightedKernel A Row Column
weightedKernel K = record { entryMajorant = maskedEntry K }

unsupportedEntryZero :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : SupportedWeightedKernel A Row Column) →
  ∀ row column → support K row column ≡ false →
  maskedEntry K row column ≡ zero A
unsupportedEntryZero {A = A} K row column support-false
  with support K row column
... | false = refl
... | true with support-false
...   | ()

concreteFarLowKernelLevel : ProofLevel
concreteFarLowKernelLevel = machineChecked

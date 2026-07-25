module DASHI.Physics.Closure.NSPeriodicFarLowKernelZeroExtension where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List; _++_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicConcreteFarLowKernel as Kernel
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Schur
open import DASHI.Physics.YangMills.CompactLieProofLevel

rowZeroExtension :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : Kernel.SupportedWeightedKernel A Row Column) →
  ∀ row oldColumns newColumns →
  (∀ column → Kernel.support K row column ≡ false) →
  Schur.weightedRowSum (Kernel.weightedKernel K) row (oldColumns ++ newColumns)
  ≡ Schur.weightedRowSum (Kernel.weightedKernel K) row oldColumns
rowZeroExtension {A = A} K row oldColumns newColumns unsupported =
  Schur.rowSumZeroExtensionInvariant
    (Kernel.weightedKernel K) row oldColumns newColumns
    (λ column → Kernel.unsupportedEntryZero K row column (unsupported column))

columnZeroExtension :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : Kernel.SupportedWeightedKernel A Row Column) →
  ∀ column oldRows newRows →
  (∀ row → Kernel.support K row column ≡ false) →
  Schur.weightedColumnSum (Kernel.weightedKernel K) column (oldRows ++ newRows)
  ≡ Schur.weightedColumnSum (Kernel.weightedKernel K) column oldRows
columnZeroExtension {A = A} K column oldRows newRows unsupported =
  Schur.columnSumZeroExtensionInvariant
    (Kernel.weightedKernel K) column oldRows newRows
    (λ row → Kernel.unsupportedEntryZero K row column (unsupported row))

farLowKernelZeroExtensionLevel : ProofLevel
farLowKernelZeroExtensionLevel = machineChecked

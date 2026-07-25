module DASHI.Physics.Closure.NSPeriodicFarLowRowMajorantFold where

open import Agda.Primitive using (Level)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (_++_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicConcreteFarLowKernel as Kernel
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Schur
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One authoritative literal row fold for the support-masked kernel.
------------------------------------------------------------------------

farLowRowMajorantFold :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  Kernel.SupportedWeightedKernel A Row Column →
  Row → List Column → Scalar A
farLowRowMajorantFold K = Schur.weightedRowSum (Kernel.weightedKernel K)

farLowRowFoldAppend :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : Kernel.SupportedWeightedKernel A Row Column) →
  ∀ row left right →
  farLowRowMajorantFold K row (left ++ right) ≡
  _+_ A (farLowRowMajorantFold K row left) (farLowRowMajorantFold K row right)
farLowRowFoldAppend {A = A} K row left right =
  Schur.sumByAppend (Kernel.maskedEntry K row) left right

farLowRowMajorantFoldLevel : ProofLevel
farLowRowMajorantFoldLevel = machineChecked

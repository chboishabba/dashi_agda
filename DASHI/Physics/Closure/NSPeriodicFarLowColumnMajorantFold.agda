module DASHI.Physics.Closure.NSPeriodicFarLowColumnMajorantFold where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (_++_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicConcreteFarLowKernel as Kernel
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Schur
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One authoritative literal column fold for the support-masked kernel.
------------------------------------------------------------------------

farLowColumnMajorantFold :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  Kernel.SupportedWeightedKernel A Row Column →
  Column → List Row → Scalar A
farLowColumnMajorantFold K = Schur.weightedColumnSum (Kernel.weightedKernel K)

farLowColumnFoldAppend :
  ∀ {r c} {A : AbsorptionArithmetic} {Row : Set r} {Column : Set c} →
  (K : Kernel.SupportedWeightedKernel A Row Column) →
  ∀ column left right →
  farLowColumnMajorantFold K column (left ++ right) ≡
  _+_ A
    (farLowColumnMajorantFold K column left)
    (farLowColumnMajorantFold K column right)
farLowColumnFoldAppend {A = A} K column left right =
  Schur.sumByAppend (λ row → Kernel.maskedEntry K row column) left right

farLowColumnMajorantFoldLevel : ProofLevel
farLowColumnMajorantFoldLevel = machineChecked

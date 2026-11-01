module DASHI.Physics.Closure.NSPeriodicFarHighFiniteTail where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFiniteWeightedSchurKernel as Fold
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal finite high-shell tail indices and fold.
------------------------------------------------------------------------

tailIndices : Nat → Nat → List Nat
tailIndices start zero = []
tailIndices start (suc count) = start ∷ tailIndices (suc start) count

length : ∀ {i} {A : Set i} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

tailIndicesLength : ∀ start count → length (tailIndices start count) ≡ count
tailIndicesLength start zero = refl
tailIndicesLength start (suc count) =
  congSuc (tailIndicesLength (suc start) count)
  where
  congSuc : ∀ {a b} → a ≡ b → suc a ≡ suc b
  congSuc refl = refl

finiteTail :
  ∀ {A : AbsorptionArithmetic} →
  (Nat → Scalar A) → Nat → Nat → Scalar A
finiteTail term start count = Fold.sumBy term (tailIndices start count)

farHighFiniteTailLevel : ProofLevel
farHighFiniteTailLevel = machineChecked

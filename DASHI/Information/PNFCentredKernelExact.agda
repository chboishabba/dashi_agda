module DASHI.Information.PNFCentredKernelExact where

-- Constructive kernel equality, not just a dimension count:
-- the whole centred n-row operator and its n-1-row tail have
-- identical null vectors, directly from the source mean certificate.
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredRankFactorisationExact as Factor
import DASHI.Information.PNFCentredLinearRankExact as Linear

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

ActionZero :
  (K : Ring.ExactOrderedCommutativeRing) →
  {n : Nat} → (Fin n → SOf K) → Set
ActionZero K {n} f =
  (r : Fin n) → f r ≡ Scalar.zero (Ring.orderedScalar K)

reconstructZeroSumOfZeroTail :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  (a : Fin k → SOf K) →
  ActionZero K a →
  ActionZero K (Factor.reconstructZeroSum K a)
reconstructZeroSumOfZeroTail K a zeroTail zero =
  trans
    (cong (Scalar.neg (Ring.orderedScalar K))
      (trans
        (Ring.sumFinCong (Ring.orderedScalar K) zeroTail)
        (Ring.sumFinAllZero K)))
    (Ring.negZero K)
reconstructZeroSumOfZeroTail K a zeroTail (suc t) =
  zeroTail t

-- Exact equivalence: a vector annihilates the full centred matrix iff
-- it annihilates the tail matrix of n−1 observation rows.
tailKernelImpliesFullKernel :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  (v : Fin p → SOf K) →
  ActionZero K (Linear.tailAction K M v) →
  ActionZero K (Linear.centredAction K M v)
tailKernelImpliesFullKernel K M v zeroTail r =
  trans
    (sym (Linear.centredActionFactorsThroughTail K M v r))
    (reconstructZeroSumOfZeroTail K (Linear.tailAction K M v) zeroTail r)

fullKernelImpliesTailKernel :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  (v : Fin p → SOf K) →
  ActionZero K (Linear.centredAction K M v) →
  ActionZero K (Linear.tailAction K M v)
fullKernelImpliesTailKernel K M v zeroFull t =
  zeroFull (suc t)

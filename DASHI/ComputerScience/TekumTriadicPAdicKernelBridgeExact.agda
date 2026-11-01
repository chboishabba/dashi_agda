module DASHI.ComputerScience.TekumTriadicPAdicKernelBridgeExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.ComputerScience.TekumTruncationRoundingExact as Tekum

------------------------------------------------------------------------
-- Exact carrier weld: the Tekum Vec presentation and the canonical triadic
-- p-adic Kernel presentation are the same finite trit word up to constructors.

toKernel : ∀ {n} → Vec Trit.Trit n → PAdic.Kernel n
toKernel [] = PAdic.[]ᵥ
toKernel (t ∷ ts) = t PAdic.∷ᵥ toKernel ts

fromKernel : ∀ {n} → PAdic.Kernel n → Vec Trit.Trit n
fromKernel PAdic.[]ᵥ = []
fromKernel (t PAdic.∷ᵥ ts) = t ∷ fromKernel ts

fromToKernel :
  ∀ {n} (xs : Vec Trit.Trit n) →
  fromKernel (toKernel xs) ≡ xs
fromToKernel [] = refl
fromToKernel (t ∷ ts)
  rewrite fromToKernel ts = refl

toFromKernel :
  ∀ {n} (xs : PAdic.Kernel n) →
  toKernel (fromKernel xs) ≡ xs
toFromKernel PAdic.[]ᵥ = refl
toFromKernel (t PAdic.∷ᵥ ts)
  rewrite toFromKernel ts = refl

truncateKernelTwo :
  ∀ {n} → PAdic.Kernel (suc (suc n)) → PAdic.Kernel n
truncateKernelTwo (a PAdic.∷ᵥ b PAdic.∷ᵥ rest) = rest

truncateCommutesWithCarrierWeld :
  ∀ {n} (xs : Vec Trit.Trit (suc (suc n))) →
  toKernel (Tekum.truncateTwo xs)
  ≡ truncateKernelTwo (toKernel xs)
truncateCommutesWithCarrierWeld (a ∷ b ∷ rest) = refl

truncateKernelFourDirect :
  ∀ {n} →
  PAdic.Kernel (suc (suc (suc (suc n)))) →
  PAdic.Kernel n
truncateKernelFourDirect
  (a PAdic.∷ᵥ b PAdic.∷ᵥ c PAdic.∷ᵥ d PAdic.∷ᵥ rest) = rest

kernelTwoStepProjectionComposes :
  ∀ {n}
  (xs : PAdic.Kernel (suc (suc (suc (suc n))))) →
  truncateKernelTwo (truncateKernelTwo xs)
  ≡ truncateKernelFourDirect xs
kernelTwoStepProjectionComposes
  (a PAdic.∷ᵥ b PAdic.∷ᵥ c PAdic.∷ᵥ d PAdic.∷ᵥ rest) = refl

record TekumPAdicKernelBoundary : Set where
  constructor tekumPAdicKernelBoundary
  field
    vecKernelBijectionPaid : Bool
    twoTritPrecisionProjectionCommutes : Bool
    nestedProjectionCompositionPaid : Bool
    pAdicValuationIdentityClaimed : Bool

canonicalTekumPAdicKernelBoundary : TekumPAdicKernelBoundary
canonicalTekumPAdicKernelBoundary =
  tekumPAdicKernelBoundary true true true false

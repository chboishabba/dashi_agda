module DASHI.Core.MinimalKernelAlgebraTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Core.MinimalKernelAlgebra

------------------------------------------------------------------------
-- Canonical finite witness: Trit with trivial geometry action and identity K.
------------------------------------------------------------------------

unitSymmetry : SymmetryAction ⊤ Trit
unitSymmetry = record
  { identity = tt
  ; compose = λ _ _ → tt
  ; act = λ _ t → t
  ; leftIdentity = λ _ → refl
  ; rightIdentity = λ _ → refl
  ; associative = λ _ _ _ → refl
  ; identityActs = λ _ → refl
  ; composeActs = λ _ _ _ → refl
  }

identityTritKernelAlgebra : MinimalKernelAlgebra ⊤ Trit
identityTritKernelAlgebra = record
  { symmetry = unitSymmetry
  ; involution = inv
  ; kernel = λ t → t
  ; involutionLaw = λ where
      neg → refl
      zer → refl
      pos → refl
  ; kernelSymmetryEquivariant = λ _ _ → refl
  ; kernelInvolutionEquivariant = λ _ → refl
  }

supportSignNegativeRoundTrip :
  decodeSupportSign (encodeSupportSign neg) ≡ neg
supportSignNegativeRoundTrip = refl

supportSignZeroRoundTrip :
  decodeSupportSign (encodeSupportSign zer) ≡ zer
supportSignZeroRoundTrip = refl

supportSignPositiveRoundTrip :
  decodeSupportSign (encodeSupportSign pos) ≡ pos
supportSignPositiveRoundTrip = refl

maskIsDerivedAtZero : activityMask zer ≡ false
maskIsDerivedAtZero = refl

maskIsDerivedAtPositive : activityMask pos ≡ true
maskIsDerivedAtPositive = refl

sampleWord : KernelWord ⊤
sampleWord =
  symmetryGenerator tt ∷
  kernelGenerator ∷
  involutionGenerator ∷
  []

sampleWordOnNegative :
  evaluateWord identityTritKernelAlgebra sampleWord neg ≡ pos
sampleWordOnNegative = refl

------------------------------------------------------------------------
-- Equality quotient and exact identity RG square.
------------------------------------------------------------------------

equalityEquivalence : Equivalence Trit
equalityEquivalence = record
  { _≈_ = _≡_
  ; reflexive = λ _ → refl
  ; symmetric = sym
  ; transitive = trans
  }

identityQuotientCompatibility :
  QuotientCompatible identityTritKernelAlgebra equalityEquivalence
identityQuotientCompatibility = record
  { kernelCompatible = λ proof → proof
  ; involutionCompatible = λ proof → cong inv proof
  ; symmetryCompatible = λ _ proof → proof
  }

identityRGStep :
  QuotientRGStep identityTritKernelAlgebra identityTritKernelAlgebra
identityRGStep = record
  { coarseGrain = λ t → t
  ; quotientObserve = λ t → t
  ; commutesAfterQuotient = λ _ → refl
  }

constantActionDescent : ActionDescent identityTritKernelAlgebra
constantActionDescent = record
  { Cost = Nat
  ; _≤cost_ = _≡_
  ; action = λ _ → 0
  ; kernelNonIncreasing = λ _ → refl
  }

module DASHI.Analysis.RiemannG21PrimePairKernelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- G21 relational prime-pair admission gate.
--
-- The literal future specialization is expected to arise only after the two
-- explicit-formula channels are expanded before majorization.  For a
-- derivative/contrastive channel the hoped-for pair structure contains a
-- factor like log(n/m), hence vanishes on the diagonal.  This module does not
-- assert that literal identity yet; it defines exact algebraic certificates
-- that any proposed pair kernel must pass.
------------------------------------------------------------------------

record FinitePrimePairKernel : Set₁ where
  field
    PrimeIndex : Set
    kernelCode : PrimeIndex → PrimeIndex → Nat

    diagonalZero :
      (p : PrimeIndex) → kernelCode p p ≡ 0

    swapSymmetric :
      (p q : PrimeIndex) → kernelCode p q ≡ kernelCode q p

    kernelReading : String

open FinitePrimePairKernel public

record RectangleNonseparabilityWitness
    (surface : FinitePrimePairKernel) : Set where
  field
    a b c d : PrimeIndex surface
    rectangleEqualityImpossible :
      kernelCode surface a c + kernelCode surface b d
      ≡
      kernelCode surface a d + kernelCode surface b c
      → ⊥

open RectangleNonseparabilityWitness public

record RankOneMinorObstruction
    (surface : FinitePrimePairKernel) : Set where
  field
    a b c d : PrimeIndex surface
    rankOneMinorEqualityImpossible :
      kernelCode surface a c * kernelCode surface b d
      ≡
      kernelCode surface a d * kernelCode surface b c
      → ⊥

open RankOneMinorObstruction public

record PrimePairRelationalAdmission : Set₁ where
  field
    kernel : FinitePrimePairKernel
    rectangleObstruction : RectangleNonseparabilityWitness kernel
    rankOneObstruction : RankOneMinorObstruction kernel
    admissionReading : String

open PrimePairRelationalAdmission public

------------------------------------------------------------------------
-- Exact two-point regression witness.
--
-- This is not the zeta prime kernel.  It only shows that the admission test
-- itself is non-vacuous and mechanically separates a genuine pair relation
-- from endpoint-separable/rank-one patterns.
------------------------------------------------------------------------

data ToyPrimeIndex : Set where
  p₂ p₃ : ToyPrimeIndex

toyMismatchKernel : ToyPrimeIndex → ToyPrimeIndex → Nat
toyMismatchKernel p₂ p₂ = 0
toyMismatchKernel p₃ p₃ = 0
toyMismatchKernel p₂ p₃ = 1
toyMismatchKernel p₃ p₂ = 1

toyDiagonalZero : (p : ToyPrimeIndex) → toyMismatchKernel p p ≡ 0
toyDiagonalZero p₂ = refl
toyDiagonalZero p₃ = refl

toySwapSymmetric :
  (p q : ToyPrimeIndex) →
  toyMismatchKernel p q ≡ toyMismatchKernel q p
toySwapSymmetric p₂ p₂ = refl
toySwapSymmetric p₂ p₃ = refl
toySwapSymmetric p₃ p₂ = refl
toySwapSymmetric p₃ p₃ = refl

canonicalToyPrimePairKernel : FinitePrimePairKernel
canonicalToyPrimePairKernel =
  record
    { PrimeIndex = ToyPrimeIndex
    ; kernelCode = toyMismatchKernel
    ; diagonalZero = toyDiagonalZero
    ; swapSymmetric = toySwapSymmetric
    ; kernelReading =
        "Two-point mismatch kernel used only as a regression witness for diagonal-zero, relational nonseparability and rank-greater-than-one admission."
    }

toyRectangleObstruction :
  RectangleNonseparabilityWitness canonicalToyPrimePairKernel
toyRectangleObstruction =
  record
    { a = p₂
    ; b = p₃
    ; c = p₂
    ; d = p₃
    ; rectangleEqualityImpossible = λ ()
    }

toyRankOneObstruction :
  RankOneMinorObstruction canonicalToyPrimePairKernel
toyRankOneObstruction =
  record
    { a = p₂
    ; b = p₃
    ; c = p₂
    ; d = p₃
    ; rankOneMinorEqualityImpossible = λ ()
    }

canonicalToyPrimePairRelationalAdmission : PrimePairRelationalAdmission
canonicalToyPrimePairRelationalAdmission =
  record
    { kernel = canonicalToyPrimePairKernel
    ; rectangleObstruction = toyRectangleObstruction
    ; rankOneObstruction = toyRankOneObstruction
    ; admissionReading =
        "The admission gate is executable: diagonal zero and pair symmetry coexist with exact violations of the endpoint-separable rectangle identity and rank-one minor identity."
    }

------------------------------------------------------------------------
-- Swap reindexing boundary inspired by the finite-product/permutation lane.
------------------------------------------------------------------------

Pair : Set → Set
Pair A = A × A

swapPair : {A : Set} → Pair A → Pair A
swapPair (x , y) = y , x

swapPairInvolutive :
  {A : Set} →
  (p : Pair A) →
  swapPair (swapPair p) ≡ p
swapPairInvolutive (x , y) = refl

kernelSwapInvariant :
  (surface : FinitePrimePairKernel) →
  (p : Pair (PrimeIndex surface)) →
  kernelCode surface (fst p) (snd p)
  ≡
  kernelCode surface (fst (swapPair p)) (snd (swapPair p))
kernelSwapInvariant surface (x , y) = swapSymmetric surface x y

record PrimePairReindexBoundary : Set where
  constructor primePairReindexBoundary
  field
    swapCancellationMustPrecedeAbsoluteValues : Bool
    swapCancellationMustPrecedeAbsoluteValuesIsTrue :
      swapCancellationMustPrecedeAbsoluteValues ≡ true

    pureAntisymmetryOverFullSquareWouldEraseSignal : Bool
    pureAntisymmetryOverFullSquareWouldEraseSignalIsTrue :
      pureAntisymmetryOverFullSquareWouldEraseSignal ≡ true

    exactFiniteReindexingAloneProvesRH : Bool
    exactFiniteReindexingAloneProvesRHIsFalse :
      exactFiniteReindexingAloneProvesRH ≡ false

canonicalPrimePairReindexBoundary : PrimePairReindexBoundary
canonicalPrimePairReindexBoundary =
  primePairReindexBoundary
    true refl
    true refl
    false refl

module DASHI.Algebra.Quantum.QuantumFourierTransformFinite where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes
open import DASHI.Algebra.Quantum.FiniteQuantumRegister

------------------------------------------------------------------------
-- Finite quantum Fourier transform interface.
--
-- The name is intentionally explicit to avoid collision with
-- QFTParitySurface, where QFT means quantum field theory.
------------------------------------------------------------------------

record FiniteFourierTransform
    {B : FiniteBasis}
    (R : FiniteQuantumRegister B) : Set₁ where
  field
    fourier : State R → State R
    inverseFourier : State R → State R

    inverseAfterFourier :
      ∀ ψ → inverseFourier (fourier ψ) ≡ ψ

    fourierAfterInverse :
      ∀ ψ → fourier (inverseFourier ψ) ≡ ψ

open FiniteFourierTransform public

fourierInvertible :
  {B : FiniteBasis} →
  {R : FiniteQuantumRegister B} →
  (F : FiniteFourierTransform R) →
  Invertible (fourier F)
fourierInvertible F = record
  { inv = inverseFourier F
  ; left = inverseAfterFourier F
  ; right = fourierAfterInverse F
  }

fourierCircuit :
  {B : FiniteBasis} →
  {R : FiniteQuantumRegister B} →
  FiniteFourierTransform R →
  ReversibleCircuit R
fourierCircuit F = record
  { run = fourier F
  ; reversible = fourierInvertible F
  }

record FourierSample : Set where
  constructor mkFourierSample
  field
    numerator : Nat
    denominator : Nat

open FourierSample public

module DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_; _+_; _^_; ∣_-_∣)
open import Data.Nat.Logarithm using
  (⌈log₂_⌉; ⌈log₂⌉-mono-≤; ⌈log₂2^n⌉≡n)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale

------------------------------------------------------------------------
-- Literal shell convention.
--
-- shellIndex k is the ceiling base-two logarithm of the exact integer
-- max-coordinate norm.  Zero is deliberately mapped to shell zero; every
-- theorem used by the nonlinear route separately requires NonZeroMode.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 n = 2 ^ n

shellIndexMagnitude : Nat → Nat
shellIndexMagnitude n = ⌈log₂ n ⌉

shellIndex : Z3.FourierMode → Nat
shellIndex k = shellIndexMagnitude (Infinity.infinityNorm k)

shellIndexMonotone :
  ∀ {m n} → m ≤ n → shellIndexMagnitude m ≤ shellIndexMagnitude n
shellIndexMonotone = ⌈log₂⌉-mono-≤

shellIndexPowerOfTwo : ∀ n → shellIndexMagnitude (pow2 n) ≡ n
shellIndexPowerOfTwo = ⌈log₂2^n⌉≡n

------------------------------------------------------------------------
-- Explicit constants selected for the official max-norm convention.
--
-- Csep = 3 gives an input norm ratio strictly below 1/4 under the shell
-- lower/upper laws.  Cout and Cin are kept explicit and may be sharpened
-- after the exact boundary arithmetic is checked; no cutoff appears in them.
------------------------------------------------------------------------

Csep Cout Cin : Nat
Csep = 3
Cout = 2
Cin = 2

literalDyadicShellPolicy : Scale.PhysicalShellPolicy
literalDyadicShellPolicy = Scale.shell-policy shellIndex Csep

record DyadicShellBounds : Set₁ where
  field
    shellUpper :
      (k : Z3.FourierMode) →
      Z3.NonZeroMode k →
      Infinity.infinityNorm k ≤ pow2 (shellIndex k)

    shellLower :
      (k : Z3.FourierMode) →
      (nonzero : Z3.NonZeroMode k) →
      0 < shellIndex k →
      pow2 (shellIndex k ∸ 1) < Infinity.infinityNorm k

open DyadicShellBounds public

record LiteralDyadicConsequences
    (bounds : DyadicShellBounds) : Set₁ where
  field
    lowHighOutputTracksHigh :
      (τ : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.p τ) →
      Z3.NonZeroMode (Physical.q τ) →
      Z3.NonZeroMode (Physical.k τ) →
      shellIndex (Physical.p τ) + Csep ≤ shellIndex (Physical.q τ) →
      ∣ shellIndex (Physical.k τ) - shellIndex (Physical.q τ) ∣ ≤ Cout

    highLowOutputTracksHigh :
      (τ : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.p τ) →
      Z3.NonZeroMode (Physical.q τ) →
      Z3.NonZeroMode (Physical.k τ) →
      shellIndex (Physical.q τ) + Csep ≤ shellIndex (Physical.p τ) →
      ∣ shellIndex (Physical.k τ) - shellIndex (Physical.p τ) ∣ ≤ Cout

    highHighToLowInputsComparable :
      (τ : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.p τ) →
      Z3.NonZeroMode (Physical.q τ) →
      Z3.NonZeroMode (Physical.k τ) →
      shellIndex (Physical.k τ) + Csep ≤ shellIndex (Physical.p τ) →
      shellIndex (Physical.k τ) + Csep ≤ shellIndex (Physical.q τ) →
      ∣ shellIndex (Physical.p τ) - shellIndex (Physical.q τ) ∣ ≤ Cin

open LiteralDyadicConsequences public

literalShellFunctionConstructed : Bool
literalShellFunctionConstructed = true

literalShellFunctionConstructedIsTrue :
  literalShellFunctionConstructed ≡ true
literalShellFunctionConstructedIsTrue = refl

explicitDyadicConstantsSelected : Bool
explicitDyadicConstantsSelected = true

explicitDyadicConstantsSelectedIsTrue :
  explicitDyadicConstantsSelected ≡ true
explicitDyadicConstantsSelectedIsTrue = refl

-- The remaining proof is finite integer arithmetic from the already proved
-- infinity-norm triangle laws plus the two ceil-log shell bounds above.
fullDyadicConsequenceProofClosed : Bool
fullDyadicConsequenceProofClosed = false

fullDyadicConsequenceProofClosedIsFalse :
  fullDyadicConsequenceProofClosed ≡ false
fullDyadicConsequenceProofClosedIsFalse = refl

module DASHI.Algebra.Quantum.ShorFinitePowModTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
open import Data.Nat using (_<_)
open import Data.Nat.DivMod using (m%n<n)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Arithmetic.DeltaGrowth as Delta
import DASHI.Crypto.RSAArithmeticCore as RSA

------------------------------------------------------------------------
-- FINITE TARGET FOR RSA.powMod
--
-- `RSA.powMod base exponent modulus` is definitionally the repository's
-- Base369Nat remainder computation applied to `Delta.pow base exponent`.
-- Base369Nat._%_ is itself the builtin `mod-helper`; the standard-library
-- `m%n<n` theorem therefore supplies the exact residue bound for every
-- nonzero modulus.
--
-- This is arithmetic/carrier plumbing only.  It does not add a quantum claim,
-- a gate decomposition, an amplitude law, or a measurement law.
------------------------------------------------------------------------

powModLessThanModulus :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  RSA.powMod base exponent modulus {{modulusNonZero}} < modulus
powModLessThanModulus base exponent zero modulusNonZero
  with B369.NonZero.nonZero modulusNonZero
... | ()
powModLessThanModulus base exponent (suc n) modulusNonZero =
  m%n<n (Delta.pow base exponent) (suc n)

powModFiniteTarget :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Fin modulus
powModFiniteTarget base exponent modulus modulusNonZero =
  fromℕ<
    (powModLessThanModulus
      base exponent modulus modulusNonZero)

powModFiniteTargetValue :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  toℕ (powModFiniteTarget base exponent modulus modulusNonZero)
  ≡ RSA.powMod base exponent modulus {{modulusNonZero}}
powModFiniteTargetValue base exponent modulus modulusNonZero = refl

record ShorFinitePowModTargetBoundary : Set where
  constructor shorFinitePowModTargetBoundary
  field
    targetResidueFinite : Bool
    targetBoundDerivedFromRemainder : Bool
    rsaPowModNatValuePreserved : Bool
    targetEnumerationNeedsExtraNumberTheory : Bool
    qftPhaseActionConstructedHere : Bool
    amplitudeNormalizationConstructedHere : Bool
    bornMeasurementConstructedHere : Bool

canonicalShorFinitePowModTargetBoundary : ShorFinitePowModTargetBoundary
canonicalShorFinitePowModTargetBoundary =
  shorFinitePowModTargetBoundary
    true true true false false false false

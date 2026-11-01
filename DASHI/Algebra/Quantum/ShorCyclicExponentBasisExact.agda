module DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat using (_%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite

------------------------------------------------------------------------
-- CANONICAL CYCLIC EXPONENT BASIS Fin Q
--
-- Shor's QFT is not naturally indexed by an arbitrary repository FiniteBasis:
-- it is a cyclic transform on a chosen exponent modulus Q.  This owner supplies
-- that literal carrier.  `decode` is reduction modulo Q, and `cyclicAdd` is
-- addition followed by the same reduction.
--
-- This file adds no complex phases, DFT coefficients, normalization or Born
-- semantics.  It only pays the finite cyclic-coordinate part of the QFT seam.
------------------------------------------------------------------------

cyclicExponentBasis :
  (Q : Nat) →
  (qNonZero : B369.NonZero Q) →
  Finite.FiniteBasis
cyclicExponentBasis zero qNonZero
  with B369.NonZero.nonZero qNonZero
... | ()
cyclicExponentBasis (suc q) qNonZero = record
  { Basis = Fin (suc q)
  ; dimension = suc q
  ; encode = toℕ
  ; decode = λ n → fromℕ< (m%n<n n (suc q))
  ; decodeEncode = decodeEncode
  }
  where
    decodeEncode :
      (b : Fin (suc q)) →
      fromℕ< (m%n<n (toℕ b) (suc q)) ≡ b
    decodeEncode b =
      FinP.toℕ-injective
        (trans
          (FinP.toℕ-fromℕ< (m%n<n (toℕ b) (suc q)))
          (m<n⇒m%n≡m (FinP.toℕ<n b)))

cyclicAdd :
  (Q : Nat) →
  (qNonZero : B369.NonZero Q) →
  Fin Q → Fin Q → Fin Q
cyclicAdd zero qNonZero left right
  with B369.NonZero.nonZero qNonZero
... | ()
cyclicAdd (suc q) qNonZero left right =
  fromℕ< (m%n<n (toℕ left + toℕ right) (suc q))

cyclicZero :
  (Q : Nat) →
  (qNonZero : B369.NonZero Q) →
  Fin Q
cyclicZero zero qNonZero
  with B369.NonZero.nonZero qNonZero
... | ()
cyclicZero (suc q) qNonZero = fromℕ< (m%n<n zero (suc q))

record ShorCyclicExponentBasisBoundary : Set where
  constructor shorCyclicExponentBasisBoundary
  field
    literalFinQCarrier : Bool
    decodeUsesModuloQ : Bool
    cyclicAdditionConstructed : Bool
    rootOfUnityCharactersConstructed : Bool
    normalizedDFTConstructed : Bool
    measurementConstructed : Bool

canonicalShorCyclicExponentBasisBoundary : ShorCyclicExponentBasisBoundary
canonicalShorCyclicExponentBasisBoundary =
  shorCyclicExponentBasisBoundary
    true true true false false false

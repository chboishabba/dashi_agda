module DASHI.Algebra.Quantum.FiniteQuantumRegister where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

------------------------------------------------------------------------
-- Finite computational registers.
--
-- This is deliberately finite and algorithm-facing.  It does not require the
-- analytic Hilbert/QFT authority surface: a register names a computational
-- basis, a state carrier, preparation, and observation on prepared basis
-- states.  Reversible circuits are ordinary invertible endomaps.
------------------------------------------------------------------------

record FiniteBasis : Set₁ where
  field
    Basis : Set
    dimension : Nat
    encode : Basis → Nat
    decode : Nat → Basis
    decodeEncode : ∀ b → decode (encode b) ≡ b

open FiniteBasis public

record FiniteQuantumRegister (B : FiniteBasis) : Set₁ where
  field
    State : Set
    prepare : Basis B → State
    observe : State → Basis B
    observePrepared : ∀ b → observe (prepare b) ≡ b

open FiniteQuantumRegister public

record ReversibleCircuit
    {B : FiniteBasis}
    (R : FiniteQuantumRegister B) : Set₁ where
  field
    run : State R → State R
    reversible : Invertible run

open ReversibleCircuit public

identityCircuit :
  {B : FiniteBasis} →
  (R : FiniteQuantumRegister B) →
  ReversibleCircuit R
identityCircuit R = record
  { run = λ x → x
  ; reversible = record
      { inv = λ x → x
      ; left = λ x → refl
      ; right = λ x → refl
      }
  }

runInverse :
  {B : FiniteBasis} →
  {R : FiniteQuantumRegister B} →
  ReversibleCircuit R →
  State R →
  State R
runInverse C = Invertible.inv (reversible C)

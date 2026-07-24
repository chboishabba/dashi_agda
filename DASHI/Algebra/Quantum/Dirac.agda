module DASHI.Algebra.Quantum.Dirac where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Representation-neutral Dirac surface.
--
-- Ket and Bra are intentional wrappers around an existing state carrier.
-- The pairing remains supplied by the ambient scalar/Hilbert structure;
-- this module does not assume a concrete complex-number implementation.

record Ket (State : Set) : Set where
  constructor ket
  field
    state : State

open Ket public

record Bra (State : Set) : Set where
  constructor bra
  field
    costate : State

open Bra public

braOf : {State : Set} → Ket State → Bra State
braOf (ket ψ) = bra ψ

record DiracPairing (State Scalar : Set) : Set where
  field
    pair : Bra State → Ket State → Scalar

open DiracPairing public

braKet :
  {State Scalar : Set} →
  DiracPairing State Scalar →
  Bra State →
  Ket State →
  Scalar
braKet P φ ψ = pair P φ ψ

record Operator (State : Set) : Set where
  constructor operator
  field
    apply : State → State

open Operator public

act : {State : Set} → Operator State → Ket State → Ket State
act O (ket ψ) = ket (apply O ψ)

expectation :
  {State Scalar : Set} →
  DiracPairing State Scalar →
  Operator State →
  Ket State →
  Scalar
expectation P O ψ = braKet P (braOf ψ) (act O ψ)

record AdjointOperation (State : Set) : Set where
  field
    dagger : Operator State → Operator State

open AdjointOperation public

record IsAdjoint
  {State Scalar : Set}
  (P : DiracPairing State Scalar)
  (Adj : AdjointOperation State)
  (O : Operator State)
  (O† : Operator State) : Set where
  field
    daggerIdentifiesOperator : dagger Adj O ≡ O†
    adjointPairingLaw :
      (φ ψ : State) →
      braKet P (bra φ) (act O (ket ψ)) ≡
      braKet P (bra (apply O† φ)) (ket ψ)

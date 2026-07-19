module DASHI.Algebra.Quantum.DASHIQuantumBridge where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes
open import DASHI.Algebra.Clifford.UniversalProperty
open import DASHI.Algebra.Quantum.Unitary

------------------------------------------------------------------------
-- Downstream quantum-computation surface.
--
-- This module does not re-postulate the physics closure.  It consumes an
-- already certified contraction -> quadratic -> signature -> Clifford ->
-- wave-lift chain and packages the data needed by quantum algorithms.
------------------------------------------------------------------------

record StrictDescentSystem : Set₁ where
  field
    State : Set
    step : State → State
    codeLength : State → Nat
    codeLengthDescent : ∀ s → codeLength (step s) ≤ codeLength s

open StrictDescentSystem public

record CertifiedQuantumBridge (D : StrictDescentSystem) : Set₁ where
  field
    Wave : Set
    complex : ComplexAxioms
    innerProduct : InnerProductSpace complex Wave

    clifford : CliffordData
    cliffordAxioms : CliffordAxioms clifford

    -- The even/spinorial carrier obtained from the proved Clifford layer.
    Even : Set
    evenToWave : Even → Wave

    -- Reversible wave lift and a semantic observation back to DASHI state.
    lift : State D → Wave
    observe : Wave → State D

    -- Every semantic state compiles to reversible wave transport.
    transport : State D → Wave → Wave
    transportUnitary : ∀ s → Unitary innerProduct (transport s)

open CertifiedQuantumBridge public

record BridgeRoundTrip
    (D : StrictDescentSystem)
    (B : CertifiedQuantumBridge D) : Set₁ where
  field
    observe-lift : ∀ s → observe B (lift B s) ≡ s

open BridgeRoundTrip public

-- The wave shell is reversible; the semantic step remains the certified
-- contractive/MDL-descending part of the computation.
waveThenObserve :
  (D : StrictDescentSystem) →
  CertifiedQuantumBridge D →
  State D →
  State D
waveThenObserve D B s = observe B (transport B s (lift B s))

module DASHI.Algebra.Quantum.DASHIStructuredStateCompression where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Classical DASHI representation of a structured quantum-state class.
--
-- No claim is made for arbitrary Hilbert states.  A CompressionModel names a
-- structured source class, a DASHI description carrier, reconstruction, an
-- explicit approximation predicate, and honest source/description costs.
------------------------------------------------------------------------

record CompressionModel : Set₁ where
  field
    QuantumState : Set
    Description : Set

    encode : QuantumState → Description
    reconstruct : Description → QuantumState

    Approx : QuantumState → QuantumState → Set
    sourceCost : QuantumState → Nat
    descriptionCost : Description → Nat

open CompressionModel public

record CertifiedCompression (M : CompressionModel) : Set₁ where
  field
    reconstructionSound :
      ∀ ψ → Approx M ψ (reconstruct M (encode M ψ))

    noDescriptionInflation :
      ∀ ψ → descriptionCost M (encode M ψ) ≤ sourceCost M ψ

open CertifiedCompression public

record StrictCompressionWitness
    (M : CompressionModel)
    (C : CertifiedCompression M) : Set₁ where
  field
    witness : QuantumState M
    strictlySmaller :
      descriptionCost M (encode M witness) < sourceCost M witness

open StrictCompressionWitness public

-- Operational equivalence may be weaker than state equality: for example,
-- equality of a chosen family of observables or output distributions.
record ObservableAdequacy (M : CompressionModel) : Set₁ where
  field
    Observable : Set
    Outcome : Set
    evaluate : Observable → QuantumState M → Outcome
    reconstructionAdequate :
      ∀ O ψ → evaluate O ψ ≡ evaluate O (reconstruct M (encode M ψ))

open ObservableAdequacy public

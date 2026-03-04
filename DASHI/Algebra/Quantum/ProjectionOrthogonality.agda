module DASHI.Algebra.Quantum.ProjectionOrthogonality where

open import DASHI.Core.Prelude
open import Data.Nat using (_∸_)

record ProjectionOrthogonalityAxioms : Set₁ where
  field
    Hilbert : Set
    _H∸_ : Hilbert → Hilbert → Hilbert
    Inner : Hilbert → Hilbert → Nat

open ProjectionOrthogonalityAxioms public

record OrthoProj (A : ProjectionOrthogonalityAxioms) (P : Hilbert A → Hilbert A) : Set where
  field
    idem : ∀ x → P (P x) ≡ P x
    orth : ∀ x y → Inner A (P x) ((_H∸_ A) y (P y)) ≡ 0

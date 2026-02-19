module DASHI.Algebra.Quantum.ProjectionOrthogonality where

open import DASHI.Core.Prelude
open import Data.Nat using (_∸_)

postulate
  Hilbert : Set
  _H∸_ : Hilbert → Hilbert → Hilbert
  Inner   : Hilbert -> Hilbert -> Nat

record OrthoProj (P : Hilbert -> Hilbert) : Set where
  field
    idem : ∀ x -> P (P x) ≡ P x
    orth : ∀ x y -> Inner (P x) (y H∸ P y) ≡ 0

module DASHI.Algebra.ProjectionVsInvertible where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

projection+invertible→identity :
  ∀ {S : Set} {K : S → S} →
  Projection K → Invertible K → (∀ x → K x ≡ x)
projection+invertible→identity {S} {K} P I x =
  let open Projection P
      open Invertible I
  in
  trans (trans (sym (left (K x))) (cong inv (idem x))) (left x)

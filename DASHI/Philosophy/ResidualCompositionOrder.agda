module DASHI.Philosophy.ResidualCompositionOrder where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Residuals compose under an explicit combination operation and preorder.
-- The bound R_AC <= R_AB + R_BC is not available without a supplied law.

record ResidualOrderedMonoid : Set₁ where
  field
    Residual : Set

    zero : Residual

    _⊕_ : Residual → Residual → Residual

    _≼_ : Residual → Residual → Set

    reflexive :
      (r : Residual) →
      r ≼ r

    transitive :
      {a b c : Residual} →
      a ≼ b →
      b ≼ c →
      a ≼ c

    leftUnit :
      (r : Residual) →
      zero ⊕ r ≡ r

    rightUnit :
      (r : Residual) →
      r ⊕ zero ≡ r

    associative :
      (a b c : Residual) →
      (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)

    monotoneLeft :
      {a b : Residual} →
      a ≼ b →
      (c : Residual) →
      c ⊕ a ≼ c ⊕ b

    monotoneRight :
      {a b : Residual} →
      a ≼ b →
      (c : Residual) →
      a ⊕ c ≼ b ⊕ c

open ResidualOrderedMonoid public

record ResidualCompositionReceipt
       (R : ResidualOrderedMonoid) : Set₁ where
  field
    residualAB :
      Residual R

    residualBC :
      Residual R

    residualAC :
      Residual R

    compositionBound :
      _≼_ R residualAC (_⊕_ R residualAB residualBC)

    preservesLossReceipt :
      Set

    amplificationTracked :
      Set

open ResidualCompositionReceipt public

composeResidualBounds :
  (R : ResidualOrderedMonoid) →
  {a b c d e : Residual R} →
  _≼_ R c (_⊕_ R a b) →
  _≼_ R e (_⊕_ R c d) →
  _≼_ R e (_⊕_ R (_⊕_ R a b) d)
composeResidualBounds R first second =
  transitive R second (monotoneRight R first d)

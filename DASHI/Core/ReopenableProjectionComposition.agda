module DASHI.Core.ReopenableProjectionComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Exact composition law for projection + receipt + reopening.
--
-- This is the small algebraic core behind composing provenance-bearing
-- quotients.  It deliberately contains no semantic authority: a receipt is
-- only enough information to reconstruct the fine state.
------------------------------------------------------------------------

record ExactReopenableProjection (X Y : Set) : Set₁ where
  constructor exactReopenableProjection
  field
    Receipt : Set
    project : X → Y
    receipt : X → Receipt
    reopen : Y → Receipt → X
    reopenExact : (x : X) → reopen (project x) (receipt x) ≡ x

open ExactReopenableProjection public

record ComposedReceipt
    {X Y Z : Set}
    (first : ExactReopenableProjection X Y)
    (second : ExactReopenableProjection Y Z)
    (x : X) : Set where
  constructor composedReceipt
  field
    firstReceipt : Receipt first
    secondReceipt : Receipt second

------------------------------------------------------------------------
-- A uniform receipt type is the product of both residual channels.
------------------------------------------------------------------------

composeExactReopenableProjection :
  ∀ {X Y Z} →
  ExactReopenableProjection X Y →
  ExactReopenableProjection Y Z →
  ExactReopenableProjection X Z
composeExactReopenableProjection first second =
  exactReopenableProjection
    (Receipt first × Receipt second)
    (λ x → project second (project first x))
    (λ x → receipt first x , receipt second (project first x))
    (λ z receipts →
      reopen first
        (reopen second z (Data.Product.proj₂ receipts))
        (Data.Product.proj₁ receipts))
    λ x →
      trans
        (cong
          (λ y → reopen first y (receipt first x))
          (reopenExact second (project first x)))
        (reopenExact first x)

------------------------------------------------------------------------
-- Receipt accounting is therefore compositional:
--
--   delta_21(x) = (delta_1(x), delta_2(pi_1 x)).
--
-- No theorem here claims this pair is *minimal*.  Minimal sufficient residual
-- is a separate optimisation/order problem.
------------------------------------------------------------------------

record ResidualSufficiencyOrder (Receipt : Set) : Set₁ where
  field
    _≤receipt_ : Receipt → Receipt → Set
    reflexive : (r : Receipt) → r ≤receipt r

open ResidualSufficiencyOrder public

record MinimalSufficientResidual
    {X Y : Set}
    (projection : ExactReopenableProjection X Y)
    (order : ResidualSufficiencyOrder (Receipt projection)) : Set₁ where
  field
    candidate : Receipt projection
    Sufficient : Receipt projection → Set
    candidateSufficient : Sufficient candidate
    minimal :
      (other : Receipt projection) →
      Sufficient other →
      candidate ≤receipt other

open MinimalSufficientResidual public

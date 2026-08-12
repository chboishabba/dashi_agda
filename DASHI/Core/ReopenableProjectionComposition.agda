module DASHI.Core.ReopenableProjectionComposition where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Exact composition law for projection + receipt + reopening.
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
        (reopen second z (proj₂ receipts))
        (proj₁ receipts))
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
-- No theorem here claims this pair is minimal.  Minimal sufficient residual
-- is a separate optimisation/order problem, represented without pretending a
-- global minimiser exists.
------------------------------------------------------------------------

record ResidualSufficiencyOrder (R : Set) : Set₁ where
  field
    _≤receipt_ : R → R → Set
    reflexive : (r : R) → _≤receipt_ r r

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
      ResidualSufficiencyOrder._≤receipt_ order candidate other

open MinimalSufficientResidual public

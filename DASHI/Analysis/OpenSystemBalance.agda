module DASHI.Analysis.OpenSystemBalance where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Ordered open-system balance.
--
-- Every event carries a state-dependent increment.  The exact one-step law
--
--   Q(step e x) = Q(x) + increment(e,x)
--
-- composes along a finite event path.  The cumulative increment is evaluated
-- in path order, so source/sink terms may depend on the evolving state.
------------------------------------------------------------------------

record AdditiveBalance
    {q : Level}
    (Quantity : Set q)
    : Set (lsuc q) where
  field
    zero : Quantity
    _⊕_ : Quantity → Quantity → Quantity

    rightIdentity :
      (value : Quantity) →
      value ⊕ zero ≡ value

    associative :
      (left middle right : Quantity) →
      (left ⊕ middle) ⊕ right
        ≡ left ⊕ (middle ⊕ right)

open AdditiveBalance public

record OpenBalanceSystem
    {i x q : Level}
    (Input : Set i)
    (State : Set x)
    (Quantity : Set q)
    : Set (lsuc (i ⊔ x ⊔ q)) where
  field
    additive : AdditiveBalance Quantity

    quantity : State → Quantity
    step : Input → State → State
    increment : Input → State → Quantity

    quantityUpdate :
      (input : Input) →
      (state : State) →
      quantity (step input state)
        ≡ _⊕_ additive
            (quantity state)
            (increment input state)

open OpenBalanceSystem public

runBalancePath :
  ∀ {i x q}
    {Input : Set i}
    {State : Set x}
    {Quantity : Set q} →
  OpenBalanceSystem Input State Quantity →
  List Input →
  State →
  State
runBalancePath B [] state = state
runBalancePath B (input ∷ inputs) state =
  runBalancePath B inputs (step B input state)

accumulatedIncrement :
  ∀ {i x q}
    {Input : Set i}
    {State : Set x}
    {Quantity : Set q} →
  OpenBalanceSystem Input State Quantity →
  List Input →
  State →
  Quantity
accumulatedIncrement B [] state = zero (additive B)
accumulatedIncrement B (input ∷ inputs) state =
  _⊕_ (additive B)
    (increment B input state)
    (accumulatedIncrement B inputs (step B input state))

pathBalance :
  ∀ {i x q}
    {Input : Set i}
    {State : Set x}
    {Quantity : Set q} →
  (B : OpenBalanceSystem Input State Quantity) →
  (inputs : List Input) →
  (state : State) →
  quantity B (runBalancePath B inputs state)
    ≡ _⊕_ (additive B)
        (quantity B state)
        (accumulatedIncrement B inputs state)
pathBalance B [] state =
  sym (rightIdentity (additive B) (quantity B state))
pathBalance B (input ∷ inputs) state =
  trans
    (pathBalance B inputs (step B input state))
    (trans
      (cong
        (λ value →
          _⊕_ (additive B)
            value
            (accumulatedIncrement B inputs (step B input state)))
        (quantityUpdate B input state))
      (associative
        (additive B)
        (quantity B state)
        (increment B input state)
        (accumulatedIncrement B inputs (step B input state))))

record OpenBalanceCertificate
    {i x q : Level}
    {Input : Set i}
    {State : Set x}
    {Quantity : Set q}
    (B : OpenBalanceSystem Input State Quantity)
    : Set (lsuc (i ⊔ x ⊔ q)) where
  field
    exactPathBalance :
      (inputs : List Input) →
      (state : State) →
      quantity B (runBalancePath B inputs state)
        ≡ _⊕_ (additive B)
            (quantity B state)
            (accumulatedIncrement B inputs state)

open OpenBalanceCertificate public

certifyOpenBalance :
  ∀ {i x q}
    {Input : Set i}
    {State : Set x}
    {Quantity : Set q}
    (B : OpenBalanceSystem Input State Quantity) →
  OpenBalanceCertificate B
certifyOpenBalance B = record
  { exactPathBalance = pathBalance B
  }

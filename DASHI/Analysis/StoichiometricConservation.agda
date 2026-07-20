module DASHI.Analysis.StoichiometricConservation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- Domain-neutral stoichiometric conservation.
--
-- A reaction contributes a stoichiometric displacement νᵣ in a vector carrier.
-- A fixed conservation covector ℓ is represented by `leftFunctional`.  The
-- left-kernel condition
--
--   ℓ(νᵣ) = 0
--
-- for every reaction implies preservation of the associated state quantity for
-- one reaction and for every finite reaction path.
--
-- The carrier is abstract: concrete instances may use integer stoichiometric
-- vectors, exact rationals, charge/moiety vectors, or another finite module.
------------------------------------------------------------------------

record AdditiveQuantity {q : Level} (Quantity : Set q) : Set (lsuc q) where
  field
    zero : Quantity
    _⊕_ : Quantity → Quantity → Quantity
    rightIdentity : (value : Quantity) → value ⊕ zero ≡ value

open AdditiveQuantity public

record StoichiometricSystem
    {r v q x : Level}
    (Reaction : Set r)
    (Vector : Set v)
    (Quantity : Set q)
    (State : Set x)
    : Set (lsuc (r ⊔ v ⊔ q ⊔ x)) where
  field
    additive : AdditiveQuantity Quantity

    stoichiometricColumn : Reaction → Vector
    leftFunctional : Vector → Quantity

    quantity : State → Quantity
    step : Reaction → State → State

    quantityUpdate :
      (reaction : Reaction) →
      (state : State) →
      quantity (step reaction state)
        ≡
      _⊕_ additive
        (quantity state)
        (leftFunctional (stoichiometricColumn reaction))

open StoichiometricSystem public

record LeftKernelConservation
    {r v q x : Level}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x}
    (S : StoichiometricSystem Reaction Vector Quantity State)
    : Set (r ⊔ v ⊔ q ⊔ x) where
  field
    annihilatesStoichiometry :
      (reaction : Reaction) →
      leftFunctional S (stoichiometricColumn S reaction)
        ≡ zero (additive S)

open LeftKernelConservation public

reactionStepConserves :
  ∀ {r v q x}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x}
    (S : StoichiometricSystem Reaction Vector Quantity State) →
  LeftKernelConservation S →
  (reaction : Reaction) →
  (state : State) →
  quantity S (step S reaction state) ≡ quantity S state
reactionStepConserves S K reaction state =
  trans
    (quantityUpdate S reaction state)
    (trans
      (cong
        (_⊕_ (additive S) (quantity S state))
        (annihilatesStoichiometry K reaction))
      (rightIdentity (additive S) (quantity S state)))

runReactionPath :
  ∀ {r v q x}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x} →
  StoichiometricSystem Reaction Vector Quantity State →
  List Reaction →
  State →
  State
runReactionPath S [] state = state
runReactionPath S (reaction ∷ reactions) state =
  runReactionPath S reactions (step S reaction state)

reactionPathConserves :
  ∀ {r v q x}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x}
    (S : StoichiometricSystem Reaction Vector Quantity State) →
  LeftKernelConservation S →
  (reactions : List Reaction) →
  (state : State) →
  quantity S (runReactionPath S reactions state) ≡ quantity S state
reactionPathConserves S K [] state = refl
reactionPathConserves S K (reaction ∷ reactions) state =
  trans
    (reactionPathConserves S K reactions (step S reaction state))
    (reactionStepConserves S K reaction state)

record StoichiometricConservationCertificate
    {r v q x : Level}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x}
    (S : StoichiometricSystem Reaction Vector Quantity State)
    : Set (lsuc (r ⊔ v ⊔ q ⊔ x)) where
  field
    leftKernel : LeftKernelConservation S

    stepConservation :
      (reaction : Reaction) →
      (state : State) →
      quantity S (step S reaction state) ≡ quantity S state

    pathConservation :
      (reactions : List Reaction) →
      (state : State) →
      quantity S (runReactionPath S reactions state) ≡ quantity S state

open StoichiometricConservationCertificate public

certifyStoichiometricConservation :
  ∀ {r v q x}
    {Reaction : Set r}
    {Vector : Set v}
    {Quantity : Set q}
    {State : Set x}
    (S : StoichiometricSystem Reaction Vector Quantity State) →
  LeftKernelConservation S →
  StoichiometricConservationCertificate S
certifyStoichiometricConservation S K = record
  { leftKernel = K
  ; stepConservation = reactionStepConserves S K
  ; pathConservation = reactionPathConserves S K
  }

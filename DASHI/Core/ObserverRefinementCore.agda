module DASHI.Core.ObserverRefinementCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Generic observer-refinement core.
--
-- An observer is a projection X → V.  We say OA refines OB when equality
-- under OA forces equality under OB.  Equivalently, every OA-fibre lies in an
-- OB-fibre.  `InformationBelow` reverses that primitive relation so its order
-- reads in the conventional direction: less informative ≤ more informative.
------------------------------------------------------------------------

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Refines :
  ∀ {X A B : Set} →
  (X → A) → (X → B) → Set
Refines OA OB =
  ∀ x y → OA x ≡ OA y → OB x ≡ OB y

InformationBelow :
  ∀ {X A B : Set} →
  (X → A) → (X → B) → Set
InformationBelow OA OB = Refines OB OA

record NotRefines
    {X A B : Set}
    (OA : X → A)
    (OB : X → B) : Set where
  constructor notRefines
  field
    leftState : X
    rightState : X
    sameLeftObservation : OA leftState ≡ OA rightState
    differentRightObservation : OB leftState ≢ OB rightState

open NotRefines public

record IncomparableObservers
    {X A B : Set}
    (OA : X → A)
    (OB : X → B) : Set where
  constructor incomparableObservers
  field
    leftDoesNotRefineRight : NotRefines OA OB
    rightDoesNotRefineLeft : NotRefines OB OA

open IncomparableObservers public

------------------------------------------------------------------------
-- A cross-collision is the exact finite witness needed for incomparability:
-- one pair collides under A but separates under B, while another pair does
-- the converse.
------------------------------------------------------------------------

record CrossCollision
    {X A B : Set}
    (OA : X → A)
    (OB : X → B) : Set where
  constructor crossCollision
  field
    a₁ : X
    a₂ : X
    sameA : OA a₁ ≡ OA a₂
    differentB : OB a₁ ≢ OB a₂
    b₁ : X
    b₂ : X
    sameB : OB b₁ ≡ OB b₂
    differentA : OA b₁ ≢ OA b₂

open CrossCollision public

crossCollisionImpliesIncomparable :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  CrossCollision OA OB →
  IncomparableObservers OA OB
crossCollisionImpliesIncomparable witness =
  incomparableObservers
    (notRefines
      (a₁ witness)
      (a₂ witness)
      (sameA witness)
      (differentB witness))
    (notRefines
      (b₁ witness)
      (b₂ witness)
      (sameB witness)
      (differentA witness))

------------------------------------------------------------------------
-- Joint observer.
------------------------------------------------------------------------

pairObserver :
  ∀ {X A B : Set} →
  (X → A) → (X → B) → X → A × B
pairObserver OA OB x = OA x , OB x

pairLeftEquality :
  ∀ {A B : Set}
    {a a′ : A}
    {b b′ : B} →
  (a , b) ≡ (a′ , b′) → a ≡ a′
pairLeftEquality refl = refl

pairRightEquality :
  ∀ {A B : Set}
    {a a′ : A}
    {b b′ : B} →
  (a , b) ≡ (a′ , b′) → b ≡ b′
pairRightEquality refl = refl

pairRefinesLeft :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  Refines (pairObserver OA OB) OA
pairRefinesLeft x y samePair = pairLeftEquality samePair

pairRefinesRight :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  Refines (pairObserver OA OB) OB
pairRefinesRight x y samePair = pairRightEquality samePair

leftBelowPair :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  InformationBelow OA (pairObserver OA OB)
leftBelowPair = pairRefinesLeft

rightBelowPair :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  InformationBelow OB (pairObserver OA OB)
rightBelowPair = pairRefinesRight

leftDoesNotRefinePair :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  CrossCollision OA OB →
  NotRefines OA (pairObserver OA OB)
leftDoesNotRefinePair witness =
  notRefines
    (a₁ witness)
    (a₂ witness)
    (sameA witness)
    (λ samePair → differentB witness (pairRightEquality samePair))

rightDoesNotRefinePair :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  CrossCollision OA OB →
  NotRefines OB (pairObserver OA OB)
rightDoesNotRefinePair witness =
  notRefines
    (b₁ witness)
    (b₂ witness)
    (sameB witness)
    (λ samePair → differentA witness (pairLeftEquality samePair))

record StrictlyRefines
    {X A B : Set}
    (finer : X → A)
    (coarser : X → B) : Set where
  constructor strictlyRefines
  field
    refines : Refines finer coarser
    reverseRefinementFails : NotRefines coarser finer

open StrictlyRefines public

pairStrictlyRefinesLeft :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  CrossCollision OA OB →
  StrictlyRefines (pairObserver OA OB) OA
pairStrictlyRefinesLeft witness =
  strictlyRefines pairRefinesLeft (leftDoesNotRefinePair witness)

pairStrictlyRefinesRight :
  ∀ {X A B : Set}
    {OA : X → A}
    {OB : X → B} →
  CrossCollision OA OB →
  StrictlyRefines (pairObserver OA OB) OB
pairStrictlyRefinesRight witness =
  strictlyRefines pairRefinesRight (rightDoesNotRefinePair witness)

------------------------------------------------------------------------
-- Least joint refinement / binary join.
--
-- Any observer O that refines both OA and OB also refines the pair.  In the
-- explicit `InformationBelow` order this is exactly the least-upper-bound
-- law: OA ≤ pair, OB ≤ pair, and every common upper bound O has pair ≤ O.
------------------------------------------------------------------------

jointRefinesPair :
  ∀ {X A B C : Set}
    {O : X → C}
    {OA : X → A}
    {OB : X → B} →
  Refines O OA →
  Refines O OB →
  Refines O (pairObserver OA OB)
jointRefinesPair refinesA refinesB x y sameO =
  refinesA x y sameO , refinesB x y sameO

pairIsLeastUpperBound :
  ∀ {X A B C : Set}
    {O : X → C}
    {OA : X → A}
    {OB : X → B} →
  InformationBelow OA O →
  InformationBelow OB O →
  InformationBelow (pairObserver OA OB) O
pairIsLeastUpperBound = jointRefinesPair

module DASHI.Algebra.Jacobian.DimensionPadding where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.Jacobian.CollisionImpliesNonInjective as Collision

------------------------------------------------------------------------
-- Appending unchanged coordinates preserves a collision and block-diagonal
-- constant-Jacobian evidence.  The dimension arithmetic is supplied by the
-- padding witness and does not reopen the dimension-two lane.

data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B

firstProjection :
  ∀ {A B : Set} →
  Pair A B →
  A
firstProjection (a , b) = a

cong :
  ∀ {A B : Set}
    {x y : A} →
  (function : A → B) →
  x ≡ y →
  function x ≡ function y
cong function refl = refl

record PaddingData
       (Base Extra BaseImage ExtraImage : Set) : Set₁ where
  field
    baseMap : Base → BaseImage
    extraMap : Extra → ExtraImage

open PaddingData public

PaddedSource : Set → Set → Set
PaddedSource Base Extra = Pair Base Extra

PaddedTarget : Set → Set → Set
PaddedTarget BaseImage ExtraImage = Pair BaseImage ExtraImage

padMap :
  ∀ {Base Extra BaseImage ExtraImage : Set} →
  PaddingData Base Extra BaseImage ExtraImage →
  PaddedSource Base Extra →
  PaddedTarget BaseImage ExtraImage
padMap padding (base , extra) =
  baseMap padding base , extraMap padding extra

padCollision :
  ∀ {Base Extra BaseImage ExtraImage : Set}
    {padding : PaddingData Base Extra BaseImage ExtraImage}
    {extra : Extra} →
  Collision.Collision (baseMap padding) →
  Collision.Collision (padMap padding)
padCollision {padding = padding} {extra = extra} collision =
  record
    { Collision.left = Collision.left collision , extra
    ; Collision.right = Collision.right collision , extra
    ; Collision.distinct = λ equality →
        Collision.distinct collision
          (cong firstProjection equality)
    ; Collision.commonImage =
        cong
          (λ image → image , extraMap padding extra)
          (Collision.commonImage collision)
    }

record DimensionCounterexample : Set₁ where
  field
    dimension : Nat
    nonzeroConstantJacobian : Set
    collisionWitness : Set
    noninjectivityWitness : Set

open DimensionCounterexample public

record DimensionPaddingReceipt : Set₁ where
  field
    baseDimension : Nat
    targetDimension : Nat
    targetAtLeastBase : Set
    blockJacobianPreserved : Set
    collisionPreserved : Set
    targetCounterexample : DimensionCounterexample

open DimensionPaddingReceipt public

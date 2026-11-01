module DASHI.Algebra.Jacobian.CollisionImpliesNonInjective where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- The trusted logical kernel is deliberately tiny: two distinct inputs with
-- one common output refute injectivity.

data Never : Set where

Not : Set → Set
Not A = A → Never

Injective :
  ∀ {X Y : Set} →
  (X → Y) →
  Set
Injective f =
  ∀ x y →
  f x ≡ f y →
  x ≡ y

record Collision
       {X Y : Set}
       (f : X → Y) : Set₁ where
  field
    left : X
    right : X
    distinct : Not (left ≡ right)
    commonImage : f left ≡ f right

open Collision public

collisionImpliesNonInjective :
  ∀ {X Y : Set}
    {f : X → Y} →
  Collision f →
  Not (Injective f)
collisionImpliesNonInjective collision injective =
  distinct collision
    (injective
      (left collision)
      (right collision)
      (commonImage collision))

record ThreePointCollision
       {X Y : Set}
       (f : X → Y) : Set₁ where
  field
    first : X
    second : X
    third : X
    firstSecondDistinct : Not (first ≡ second)
    firstThirdDistinct : Not (first ≡ third)
    secondThirdDistinct : Not (second ≡ third)
    firstSecondImage : f first ≡ f second
    firstThirdImage : f first ≡ f third

open ThreePointCollision public

threePointCollisionImpliesNonInjective :
  ∀ {X Y : Set}
    {f : X → Y} →
  ThreePointCollision f →
  Not (Injective f)
threePointCollisionImpliesNonInjective triple =
  collisionImpliesNonInjective
    record
      { left = first triple
      ; right = second triple
      ; distinct = firstSecondDistinct triple
      ; commonImage = firstSecondImage triple
      }

module DASHI.Physics.Closure.NSTriadKNLuoThreeDimensionalCharacterOrthogonalityFactorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove the exact tensor-product step from one-dimensional cyclic character
-- orthogonality to the three-dimensional finite torus.  For each coordinate
-- assume the already-constructed one-dimensional pair sum
--
--   S(k,l) = M delta(k,l).
--
-- The product character on G=(Z/MZ)^3 then satisfies
--
--   S3(k,l) = M^3 delta3(k,l).
--
-- This module performs that factorization algebraically.  The one-dimensional
-- constructor is supplied by the finite root-of-unity cancellation theorem;
-- the physical complex-root instance remains a distinct scalar embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; _*_) 
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record OneDimensionalOrthogonality (Mode : Set) : Set₁ where
  constructor one-dimensional-orthogonality
  field
    cardinal : ℚ
    pairSum modeDelta : Mode → Mode → ℚ
    pairOrthogonality :
      (left right : Mode) →
      pairSum left right ≡ cardinal * modeDelta left right

open OneDimensionalOrthogonality public

Mode3 : Set → Set
Mode3 Mode = Mode × (Mode × Mode)

first : ∀ {Mode : Set} → Mode3 Mode → Mode
first mode = proj₁ mode

second : ∀ {Mode : Set} → Mode3 Mode → Mode
second mode = proj₁ (proj₂ mode)

third : ∀ {Mode : Set} → Mode3 Mode → Mode
third mode = proj₂ (proj₂ mode)

pairSum3 :
  ∀ {Mode : Set} →
  OneDimensionalOrthogonality Mode →
  Mode3 Mode → Mode3 Mode → ℚ
pairSum3 dataSet left right =
  pairSum dataSet (first left) (first right)
  * pairSum dataSet (second left) (second right)
  * pairSum dataSet (third left) (third right)

modeDelta3 :
  ∀ {Mode : Set} →
  OneDimensionalOrthogonality Mode →
  Mode3 Mode → Mode3 Mode → ℚ
modeDelta3 dataSet left right =
  modeDelta dataSet (first left) (first right)
  * modeDelta dataSet (second left) (second right)
  * modeDelta dataSet (third left) (third right)

threeDimensionalCharacterOrthogonality :
  ∀ {Mode : Set}
    (dataSet : OneDimensionalOrthogonality Mode)
    (left right : Mode3 Mode) →
  pairSum3 dataSet left right
  ≡ cardinal dataSet * cardinal dataSet * cardinal dataSet
    * modeDelta3 dataSet left right
threeDimensionalCharacterOrthogonality dataSet left right
  rewrite pairOrthogonality dataSet (first left) (first right)
        | pairOrthogonality dataSet (second left) (second right)
        | pairOrthogonality dataSet (third left) (third right) =
  solve
    ( cardinal dataSet
    ∷ modeDelta dataSet (first left) (first right)
    ∷ modeDelta dataSet (second left) (second right)
    ∷ modeDelta dataSet (third left) (third right)
    ∷ [])

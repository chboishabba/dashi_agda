module PrimeSubsetModel where

open import MDL
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Abstract prime index

PrimeIndex : Set
PrimeIndex = Nat

------------------------------------------------------------------------
-- General subset model

record PrimeModel (D : Dataset) : Set₁ where
  field
    subsetSize : Nat
    subsetId   : Subset subsetSize
    baseModel  : Model D

primeTotal :
  ∀ {D} →
  PrimeModel D →
  CodeLength
primeTotal {D} M =
  subsetCost (PrimeModel.subsetSize M) (PrimeModel.subsetId M)
    + modelTotalLength (PrimeModel.baseModel M)

------------------------------------------------------------------------
-- 71-restricted version

record PrimeModel71 (D : Dataset) : Set₁ where
  field
    base : PrimeModel D
    sizeBound : PrimeModel.subsetSize base ≤ 71

------------------------------------------------------------------------
-- Safety theorem

subsetBoundedCost :
  ∀ {D}
  (M : PrimeModel71 D) →
  PrimeModel.subsetSize (PrimeModel71.base M) ≤ 71

subsetBoundedCost M =
  PrimeModel71.sizeBound M

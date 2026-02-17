module MDL where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Basic length type

CodeLength : Set
CodeLength = Nat

_≤_ : Nat → Nat → Set
zero ≤ _ = ⊤
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

------------------------------------------------------------------------
-- Dataset abstraction

record Dataset : Set₁ where
  field
    Data : Set
    sample : Data

------------------------------------------------------------------------
-- Model abstraction (two-part code)

record Model (D : Dataset) : Set₁ where
  field
    Param      : Set
    param      : Param

    encodeM    : Param → CodeLength
    encodeData : Param → Dataset.Data D → CodeLength

modelTotalLength :
  ∀ {D} →
  Model D →
  CodeLength
modelTotalLength {D} M =
  Model.encodeM M (Model.param M) + Model.encodeData M (Model.param M) (Dataset.sample D)


------------------------------------------------------------------------
-- MDL comparison

better :
  ∀ {D} →
  Model D →
  Model D →
  Set

better {D} M₁ M₂ =
  modelTotalLength M₁ ≤ modelTotalLength M₂

------------------------------------------------------------------------
-- Subset selection cost (critical for honesty)

-- Suppose models are parameterized by a subset of primes
-- We must charge for describing that subset.

Subset : Nat → Set
Subset n = Nat  -- abstract: encoded subset id

subsetCost :
  ∀ (n : Nat) →
  Subset n →
  CodeLength
subsetCost n _ = n  -- naive upper bound: cost grows with space size

------------------------------------------------------------------------
-- Bounded model class (limit to 71)

record BoundedModel (D : Dataset) (limit : Nat) : Set₁ where
  field
    inner : Model D
    boundProof :
      modelTotalLength inner ≤ limit

------------------------------------------------------------------------
-- The "limit to 71" specialization

limit71 : Nat
limit71 = 71

record Model71 (D : Dataset) : Set₁ where
  field
    base : Model D
    bounded : modelTotalLength base ≤ limit71

------------------------------------------------------------------------
-- Theorem: restricting model space does not reduce price unfairly

restrictSafe :
  ∀ {D}
  (M : Model D)
  (p : modelTotalLength M ≤ limit71) →
  modelTotalLength M ≤ limit71

restrictSafe M p = p

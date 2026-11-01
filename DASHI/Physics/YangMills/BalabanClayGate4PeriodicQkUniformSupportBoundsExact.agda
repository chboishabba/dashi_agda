module DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkUniformSupportBoundsExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (_∈_; here; there; elements; complete; mapMembership)

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support

------------------------------------------------------------------------
-- Constructive uniform cardinality bounds.
--
-- Once a decidable physical support predicate is supplied, the sibling module
-- computes every row support and every dual column incidence list exactly.  The
-- finite maxima below therefore provide canonical N_row and N_col bounds; no
-- choice principle or external counting theorem is needed.
------------------------------------------------------------------------

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {upper} → zero ≤ᴺ upper
  suc≤suc : ∀ {lower upper} → lower ≤ᴺ upper → suc lower ≤ᴺ suc upper

natLeReflexive : ∀ value → value ≤ᴺ value
natLeReflexive zero = zero≤
natLeReflexive (suc value) = suc≤suc (natLeReflexive value)

natLeTransitive : ∀ {left middle right} →
  left ≤ᴺ middle → middle ≤ᴺ right → left ≤ᴺ right
natLeTransitive zero≤ upper = zero≤
natLeTransitive (suc≤suc lower) (suc≤suc upper) =
  suc≤suc (natLeTransitive lower upper)

maxNat : Nat → Nat → Nat
maxNat zero right = right
maxNat (suc left) zero = suc left
maxNat (suc left) (suc right) = suc (maxNat left right)

leftBelowMax : ∀ left right → left ≤ᴺ maxNat left right
leftBelowMax zero right = zero≤
leftBelowMax (suc left) zero = natLeReflexive (suc left)
leftBelowMax (suc left) (suc right) =
  suc≤suc (leftBelowMax left right)

rightBelowMax : ∀ left right → right ≤ᴺ maxNat left right
rightBelowMax zero right = natLeReflexive right
rightBelowMax (suc left) zero = zero≤
rightBelowMax (suc left) (suc right) =
  suc≤suc (rightBelowMax left right)

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) = function value ∷ mapList function values

mapListMembership :
  ∀ {A B : Set} (function : A → B)
    {value : A} {values : List A} →
  value ∈ values →
  function value ∈ mapList function values
mapListMembership function here = here
mapListMembership function (there membership) =
  there (mapListMembership function membership)

maxList : List Nat → Nat
maxList [] = zero
maxList (value ∷ values) = maxNat value (maxList values)

memberBelowMaxList :
  ∀ {value : Nat} {values : List Nat} →
  value ∈ values → value ≤ᴺ maxList values
memberBelowMaxList {values = []} ()
memberBelowMaxList {values = value ∷ values} here =
  leftBelowMax value (maxList values)
memberBelowMaxList {value = value} {values = candidate ∷ values}
  (there membership) =
  natLeTransitive
    (memberBelowMaxList membership)
    (rightBelowMax candidate (maxList values))

uniformRowBound :
  ∀ {CoarseBond FineBond : Set} →
  Support.FiniteKernelSupportRelation CoarseBond FineBond → Nat
uniformRowBound dataSet =
  maxList
    (mapList
      (Support.exactRowCount dataSet)
      (elements (Support.coarseFinite dataSet)))

uniformColumnBound :
  ∀ {CoarseBond FineBond : Set} →
  Support.FiniteKernelSupportRelation CoarseBond FineBond → Nat
uniformColumnBound dataSet =
  maxList
    (mapList
      (Support.exactColumnCount dataSet)
      (elements (Support.fineFinite dataSet)))

rowCountBelowUniformBound :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : Support.FiniteKernelSupportRelation CoarseBond FineBond)
    coarse →
  Support.exactRowCount dataSet coarse ≤ᴺ uniformRowBound dataSet
rowCountBelowUniformBound dataSet coarse =
  memberBelowMaxList
    (mapListMembership
      (Support.exactRowCount dataSet)
      (complete (Support.coarseFinite dataSet) coarse))

columnCountBelowUniformBound :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : Support.FiniteKernelSupportRelation CoarseBond FineBond)
    fine →
  Support.exactColumnCount dataSet fine ≤ᴺ uniformColumnBound dataSet
columnCountBelowUniformBound dataSet fine =
  memberBelowMaxList
    (mapListMembership
      (Support.exactColumnCount dataSet)
      (complete (Support.fineFinite dataSet) fine))

periodicQkUniformRowBoundConstructionLevel : ProofLevel
periodicQkUniformRowBoundConstructionLevel = machineChecked

periodicQkUniformColumnBoundConstructionLevel : ProofLevel
periodicQkUniformColumnBoundConstructionLevel = machineChecked

periodicQkUniformSupportBoundComputationLevel : ProofLevel
periodicQkUniformSupportBoundComputationLevel = computed

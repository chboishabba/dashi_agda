{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR445ExteriorKernelTVChainFiniteExact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Finite coordinate-chain/TV telescope reconstructed from
-- Docs/physics/YMClayR445WeightedExteriorInfluenceMaxCut20261114.md:10-51
-- and scripts/check_ym_r445_weighted_exterior_influence.py.  This proves only
-- the finite rational path inequality for a list of exterior rows.  It does
-- NOT prove an R445 Wilson kernel bound, physical exterior influence bound,
-- D1, D2, or any Clay endpoint.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _+_; ∣_∣; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteDobrushinReopeningExact as Dob
import DASHI.Physics.YangMills.YMClayR445WeightedExteriorInfluenceFiniteExact as W

pathEndpoint : ∀ {Y : Set} → Y → List Y → Y
pathEndpoint start [] = start
pathEndpoint _ (next ∷ rest) = pathEndpoint next rest

rowDistance :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ) (left right : Y) → ℚ
rowDistance xs kernel left right =
  Dob.rowL1Difference xs
    (λ x → kernel x left)
    (λ x → kernel x right)

chainCost :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ) → Y → List Y → ℚ
chainCost xs kernel start [] = 0ℚ
chainCost xs kernel start (next ∷ rest) =
  rowDistance xs kernel start next + chainCost xs kernel next rest

budgetPathCost :
  ∀ {Y : Set} (budget : Y → Y → ℚ) → Y → List Y → ℚ
budgetPathCost budget start [] = 0ℚ
budgetPathCost budget start (next ∷ rest) =
  budget start next + budgetPathCost budget next rest

sameRowDifferenceZero :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ) (start : Y) →
  Sums.sumRational xs (λ x → kernel x start)
    - Sums.sumRational xs (λ x → kernel x start)
  ≡ 0ℚ
sameRowDifferenceZero [] kernel start = ℚRing.solve []
sameRowDifferenceZero (x ∷ xs) kernel start =
  ℚRing.solve-∀
    (kernel x start)
    (Sums.sumRational xs (λ value → kernel value start))

rowDifferenceAbsUpper :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ) (left right : Y) →
  ∣ Sums.sumRational xs (λ x → kernel x left)
      - Sums.sumRational xs (λ x → kernel x right) ∣
  ≤ rowDistance xs kernel left right
rowDifferenceAbsUpper xs kernel left right =
  let
    exact =
      W.sumDifferenceExact xs
        (λ x → kernel x left)
        (λ x → kernel x right)
  in
  subst
    (λ lower →
      ∣ lower ∣ ≤
      Dob.rowL1Difference xs
        (λ x → kernel x left)
        (λ x → kernel x right))
    (sym exact)
    (Dob.sumAbsUpper xs
      (λ x → kernel x left - kernel x right))
  where
    sym : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
    sym refl = refl

chainRowDifferenceBound :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ) →
  ∀ start path →
  ∣ Sums.sumRational xs (λ x → kernel x start)
      - Sums.sumRational xs (λ x → kernel x (pathEndpoint start path)) ∣
  ≤ chainCost xs kernel start path
chainRowDifferenceBound xs kernel start [] =
  subst
    (λ lower → ∣ lower ∣ ≤ 0ℚ)
    (sym (sameRowDifferenceZero xs kernel start))
    (ℚP.0≤∣p∣ 0ℚ)
  where
    sym : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
    sym refl = refl
chainRowDifferenceBound xs kernel start (next ∷ rest) =
  let
    rowStart =
      Sums.sumRational xs (λ x → kernel x start)
    rowNext =
      Sums.sumRational xs (λ x → kernel x next)
    rowEnd =
      Sums.sumRational xs (λ x → kernel x (pathEndpoint next rest))

    first : ∣ rowStart - rowNext ∣ ≤ rowDistance xs kernel start next
    first = rowDifferenceAbsUpper xs kernel start next

    second : ∣ rowNext - rowEnd ∣ ≤ chainCost xs kernel next rest
    second = chainRowDifferenceBound xs kernel next rest

    telescope : rowStart - rowEnd ≡ (rowStart - rowNext) + (rowNext - rowEnd)
    telescope = ℚRing.solve-∀ rowStart rowNext rowEnd

    triangle :
      ∣ rowStart - rowEnd ∣ ≤ ∣ rowStart - rowNext ∣ + ∣ rowNext - rowEnd ∣
    triangle =
      subst
        (λ lower →
          ∣ lower ∣ ≤ ∣ rowStart - rowNext ∣ + ∣ rowNext - rowEnd ∣)
        (sym telescope)
        (ℚP.∣p+q∣≤∣p∣+∣q∣ (rowStart - rowNext) (rowNext - rowEnd))

    budgetSum :
      ∣ rowStart - rowNext ∣ + ∣ rowNext - rowEnd ∣
      ≤ rowDistance xs kernel start next + chainCost xs kernel next rest
    budgetSum = ℚP.+-mono-≤ first second
  in
  ℚP.≤-trans triangle budgetSum
  where
    sym : ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
    sym refl = refl

chainCostBelowBudgets :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ)
    (budget : Y → Y → ℚ) →
  ∀ start path →
  (∀ previous next → rowDistance xs kernel previous next ≤ budget previous next) →
  chainCost xs kernel start path ≤ budgetPathCost budget start path
chainCostBelowBudgets xs kernel budget start [] pointwise = ℚP.≤-refl
chainCostBelowBudgets xs kernel budget start (next ∷ rest) pointwise =
  ℚP.+-mono-≤
    (pointwise start next)
    (chainCostBelowBudgets xs kernel budget next rest pointwise)

kernelChainTVBound :
  ∀ {X Y : Set} (xs : List X) (kernel : X → Y → ℚ)
    (budget : Y → Y → ℚ) →
  ∀ start path →
  (∀ previous next → rowDistance xs kernel previous next ≤ budget previous next) →
  ∣ Sums.sumRational xs (λ x → kernel x start)
      - Sums.sumRational xs (λ x → kernel x (pathEndpoint start path)) ∣
  ≤ budgetPathCost budget start path
kernelChainTVBound xs kernel budget start path pointwise =
  ℚP.≤-trans
    (chainRowDifferenceBound xs kernel start path)
    (chainCostBelowBudgets xs kernel budget start path pointwise)

exteriorTVChainCompilerLevel : ProofLevel
exteriorTVChainCompilerLevel = machineChecked

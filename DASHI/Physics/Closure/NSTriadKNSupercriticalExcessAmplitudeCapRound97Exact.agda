module DASHI.Physics.Closure.NSTriadKNSupercriticalExcessAmplitudeCapRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Authors: Zhen Lei; Xiao Ren.
-- Title: "Quantitative partial regularity of the Navier-Stokes equations
-- and applications".
-- arXiv:2210.01783 (2022).
-- DOI: not asserted from the supplied arXiv manuscript.
--
-- ROUND97 / CAPPED-EXCESS DICHOTOMY
--
-- Round96's only unabsorbed currency is
--
--   X_ext = C * sum_i D_i X_i,
--
-- with X_i = (A_i-A_*)_+ in the physical realization.  If a branch supplies
-- a cutoff-uniform cap X_i <= X_max, then positivity gives
--
--   X_ext <= C * X_max * sum_i D_i.
--
-- Hence the ordinary finite dissipation budget pays the entire supercritical
-- excess on that branch; no separate phase/escape theorem is required there.
-- The only remaining branch is failure of the amplitude cap.  This is the
-- exact interface suggested by the repository's `SizeGood`/excessive-size
-- coverage split.  The theorem below is deliberately algebraic and does not
-- claim that a non-circular cutoff-uniform X_max has already been produced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNSupercriticalExternalExcessOccupationRound96Exact as Excess

record CappedExcessCell
    (C threshold excessCap : ℚ) : Set where
  constructor capped-excess-cell
  field
    cell : Excess.ExternalCriticalExcessCell C threshold
    excessBelowCap : Excess.excess cell ≤ excessCap

open CappedExcessCell public

cappedCellCostBelowCapTimesDissipation :
  ∀ {C threshold excessCap : ℚ} →
  0ℚ ≤ C →
  0ℚ ≤ excessCap →
  (capped : CappedExcessCell C threshold excessCap) →
  C * (Excess.dissipation (cell capped) * Excess.excess (cell capped))
  ≤ (C * excessCap) * Excess.dissipation (cell capped)
cappedCellCostBelowCapTimesDissipation {C} {excessCap} cNN capNN capped =
  let
    D = Excess.dissipation (cell capped)
    X = Excess.excess (cell capped)

    DX≤DCap : D * X ≤ D * excessCap
    DX≤DCap =
      let instance dNN = nonNegative (Excess.dissipationNonnegative (cell capped))
      in ℚP.*-monoˡ-≤-nonNeg D (excessBelowCap capped)

    CDX≤CDCap : C * (D * X) ≤ C * (D * excessCap)
    CDX≤CDCap =
      let instance cNNI = nonNegative cNN
      in ℚP.*-monoˡ-≤-nonNeg C DX≤DCap

    rearrange : C * (D * excessCap) ≡ (C * excessCap) * D
    rearrange = solve (C ∷ D ∷ excessCap ∷ [])
  in
  subst
    (λ upper → C * (D * X) ≤ upper)
    rearrange CDX≤CDCap

sumCappedExcessCost :
  ∀ {C threshold excessCap} →
  List (CappedExcessCell C threshold excessCap) → ℚ
sumCappedExcessCost [] = 0ℚ
sumCappedExcessCost {C} (capped ∷ rest) =
  C * (Excess.dissipation (cell capped) * Excess.excess (cell capped))
    + sumCappedExcessCost rest

sumCappedDissipation :
  ∀ {C threshold excessCap} →
  List (CappedExcessCell C threshold excessCap) → ℚ
sumCappedDissipation [] = 0ℚ
sumCappedDissipation (capped ∷ rest) =
  Excess.dissipation (cell capped) + sumCappedDissipation rest

finiteCappedExcessPaidByDissipation :
  ∀ {C threshold excessCap : ℚ} →
  0ℚ ≤ C →
  0ℚ ≤ excessCap →
  (cells : List (CappedExcessCell C threshold excessCap)) →
  sumCappedExcessCost cells
  ≤ (C * excessCap) * sumCappedDissipation cells
finiteCappedExcessPaidByDissipation cNN capNN [] = ℚP.≤-refl
finiteCappedExcessPaidByDissipation {C} {threshold} {excessCap}
    cNN capNN (capped ∷ rest) =
  let
    head = cappedCellCostBelowCapTimesDissipation cNN capNN capped
    tail = finiteCappedExcessPaidByDissipation cNN capNN rest
    added = ℚP.+-mono-≤ head tail
    D = Excess.dissipation (cell capped)
    Ds = sumCappedDissipation rest
    factor = C * excessCap
    endpoint : factor * D + factor * Ds ≡ factor * (D + Ds)
    endpoint = solve (factor ∷ D ∷ Ds ∷ [])
  in
  subst
    (λ upper → sumCappedExcessCost (capped ∷ rest) ≤ upper)
    endpoint added

record CappedExcessDissipationBudget
    (C threshold excessCap : ℚ) : Set where
  constructor capped-excess-dissipation-budget
  field
    nonlinearConstantNonnegative : 0ℚ ≤ C
    excessCapNonnegative : 0ℚ ≤ excessCap
    cells : List (CappedExcessCell C threshold excessCap)
    dissipationBudget : ℚ
    totalDissipationBelowBudget :
      sumCappedDissipation cells ≤ dissipationBudget

open CappedExcessDissipationBudget public

cappedExcessHasFiniteEndpointBudget :
  ∀ {C threshold excessCap} →
  (budget : CappedExcessDissipationBudget C threshold excessCap) →
  sumCappedExcessCost (cells budget)
  ≤ (C * excessCap) * dissipationBudget budget
cappedExcessHasFiniteEndpointBudget {C} {excessCap} budget =
  let
    base = finiteCappedExcessPaidByDissipation
      (nonlinearConstantNonnegative budget)
      (excessCapNonnegative budget)
      (cells budget)
    factorNN : 0ℚ ≤ C * excessCap
    factorNN =
      let
        instance
          cNN = nonNegative (nonlinearConstantNonnegative budget)
          capNN = nonNegative (excessCapNonnegative budget)
          productNN = ℚP.nonNeg*nonNeg⇒nonNeg C excessCap
      in ℚP.nonNegative⁻¹ (C * excessCap)
    scaleBudget =
      let instance fNN = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg (C * excessCap)
        (totalDissipationBelowBudget budget)
  in
  ℚP.≤-trans base scaleBudget

round97UniformlyCappedExcessReducesToDissipationBudget : Bool
round97UniformlyCappedExcessReducesToDissipationBudget = true

round97AmplitudeCapItselfMustBeNonCircular : Bool
round97AmplitudeCapItselfMustBeNonCircular = true

round97UniformlyCappedExcessReducesToDissipationBudgetIsTrue :
  round97UniformlyCappedExcessReducesToDissipationBudget ≡ true
round97UniformlyCappedExcessReducesToDissipationBudgetIsTrue = refl

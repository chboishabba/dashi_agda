module DASHI.Physics.Closure.NSTriadKNCappedExcessFiniteRemainderRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- Author: John G. Heywood.
-- Title: "Epochs of Regularity for Weak Solutions of the Navier-Stokes
-- Equations in Unbounded Domains".
-- Tohoku Mathematical Journal 40 (1988), 293--313.
-- DOI: 10.2748/tmj/1178228031.
--
-- ROUND97 / FINITE-REMAINDER ROUTE
--
-- The direct integrated compact-Gamma/BKM consumer permits a finite
-- forcing-and-data remainder.  Therefore the Round96 supercritical excess
-- need not be paid by the escape margin on every branch.
--
-- If X_i <= X_max and total dissipation is bounded, then
--
--   R_i + delta D_i <= nu D_i + C D_i X_i
--                        <= nu D_i + C X_max D_i,
--
-- and finite summation yields
--
--   sum R_i + delta sum D_i
--      <= nu sum D_i + (C X_max) D_budget.
--
-- The last term is a finite endpoint remainder of exactly the kind consumed
-- by `PointwiseCompactGammaExpenditure.forcingAndDataRemainder`.  Thus the
-- capped branch does not require `supercriticalExcessPaidByEscape`.
--
-- This theorem deliberately leaves the production of a NON-CIRCULAR,
-- cutoff-uniform X_max as a separate branch condition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNSupercriticalExternalExcessOccupationRound96Exact as Excess
import DASHI.Physics.Closure.NSTriadKNSupercriticalExcessAmplitudeCapRound97Exact as Cap

sumCappedExternalFlux :
  ∀ {C threshold excessCap} →
  List (Cap.CappedExcessCell C threshold excessCap) → ℚ
sumCappedExternalFlux [] = 0ℚ
sumCappedExternalFlux (capped ∷ rest) =
  Excess.externalFlux (Cap.cell capped) + sumCappedExternalFlux rest

sumCappedDissipation :
  ∀ {C threshold excessCap} →
  List (Cap.CappedExcessCell C threshold excessCap) → ℚ
sumCappedDissipation [] = 0ℚ
sumCappedDissipation (capped ∷ rest) =
  Excess.dissipation (Cap.cell capped) + sumCappedDissipation rest

cappedCellStrictAbsorptionWithFiniteRateRemainder :
  ∀ {C threshold excessCap viscosity delta : ℚ} →
  0ℚ ≤ C →
  0ℚ ≤ excessCap →
  C * threshold + delta ≤ viscosity →
  (capped : Cap.CappedExcessCell C threshold excessCap) →
  Excess.externalFlux (Cap.cell capped)
      + delta * Excess.dissipation (Cap.cell capped)
  ≤ viscosity * Excess.dissipation (Cap.cell capped)
      + (C * excessCap) * Excess.dissipation (Cap.cell capped)
cappedCellStrictAbsorptionWithFiniteRateRemainder
    {C} {threshold} {excessCap} {viscosity} {delta}
    cNN capNN headroom capped =
  let
    cell = Cap.cell capped
    base = Excess.externalCellAbsorbedModuloExcess cNN headroom cell
    capCost = Cap.cappedCellCostBelowCapTimesDissipation cNN capNN capped
    replace = ℚP.+-mono-≤ ℚP.≤-refl capCost
  in
  ℚP.≤-trans base replace

finiteCappedFluxStrictlyAbsorbedWithRateRemainder :
  ∀ {C threshold excessCap viscosity delta : ℚ} →
  0ℚ ≤ C →
  0ℚ ≤ excessCap →
  C * threshold + delta ≤ viscosity →
  (cells : List (Cap.CappedExcessCell C threshold excessCap)) →
  sumCappedExternalFlux cells + delta * sumCappedDissipation cells
  ≤ viscosity * sumCappedDissipation cells
      + (C * excessCap) * sumCappedDissipation cells
finiteCappedFluxStrictlyAbsorbedWithRateRemainder cNN capNN headroom [] =
  ℚP.≤-refl
finiteCappedFluxStrictlyAbsorbedWithRateRemainder
    {C} {threshold} {excessCap} {viscosity} {delta}
    cNN capNN headroom (capped ∷ rest) =
  let
    head = cappedCellStrictAbsorptionWithFiniteRateRemainder
      cNN capNN headroom capped
    tail = finiteCappedFluxStrictlyAbsorbedWithRateRemainder
      cNN capNN headroom rest
    added = ℚP.+-mono-≤ head tail
    R = Excess.externalFlux (Cap.cell capped)
    D = Excess.dissipation (Cap.cell capped)
    Rs = sumCappedExternalFlux rest
    Ds = sumCappedDissipation rest
    F = C * excessCap
    leftMeaning :
      (R + delta * D) + (Rs + delta * Ds)
      ≡ (R + Rs) + delta * (D + Ds)
    leftMeaning = solve (R ∷ delta ∷ D ∷ Rs ∷ Ds ∷ [])
    rightMeaning :
      (viscosity * D + F * D) + (viscosity * Ds + F * Ds)
      ≡ viscosity * (D + Ds) + F * (D + Ds)
    rightMeaning = solve (viscosity ∷ D ∷ F ∷ Ds ∷ [])
  in
  subst
    (λ lhs → lhs ≤
      viscosity * sumCappedDissipation (capped ∷ rest)
        + (C * excessCap) * sumCappedDissipation (capped ∷ rest))
    leftMeaning
    (subst
      (λ rhs →
        (R + delta * D) + (Rs + delta * Ds) ≤ rhs)
      rightMeaning added)

record CappedFluxFiniteRemainderBudget
    (C threshold excessCap viscosity delta : ℚ) : Set where
  constructor capped-flux-finite-remainder-budget
  field
    nonlinearConstantNonnegative : 0ℚ ≤ C
    excessCapNonnegative : 0ℚ ≤ excessCap
    viscosityHeadroom : C * threshold + delta ≤ viscosity
    cells : List (Cap.CappedExcessCell C threshold excessCap)
    dissipationBudget : ℚ
    totalDissipationBelowBudget :
      sumCappedDissipation cells ≤ dissipationBudget

open CappedFluxFiniteRemainderBudget public

finiteEndpointRemainder :
  ∀ {C threshold excessCap viscosity delta} →
  CappedFluxFiniteRemainderBudget C threshold excessCap viscosity delta → ℚ
finiteEndpointRemainder {C} {excessCap} budget =
  (C * excessCap) * dissipationBudget budget

cappedFluxStrictlyAbsorbedModuloFiniteEndpointRemainder :
  ∀ {C threshold excessCap viscosity delta} →
  (budget : CappedFluxFiniteRemainderBudget
    C threshold excessCap viscosity delta) →
  sumCappedExternalFlux (cells budget)
      + delta * sumCappedDissipation (cells budget)
  ≤ viscosity * sumCappedDissipation (cells budget)
      + finiteEndpointRemainder budget
cappedFluxStrictlyAbsorbedModuloFiniteEndpointRemainder
    {C} {threshold} {excessCap} {viscosity} {delta} budget =
  let
    base = finiteCappedFluxStrictlyAbsorbedWithRateRemainder
      (nonlinearConstantNonnegative budget)
      (excessCapNonnegative budget)
      (viscosityHeadroom budget)
      (cells budget)

    factor = C * excessCap
    factorNN : 0ℚ ≤ factor
    factorNN =
      let
        instance
          cNN = nonNegative (nonlinearConstantNonnegative budget)
          xNN = nonNegative (excessCapNonnegative budget)
          fxNN = ℚP.nonNeg*nonNeg⇒nonNeg C excessCap
      in ℚP.nonNegative⁻¹ factor

    scaledBudget :
      factor * sumCappedDissipation (cells budget)
      ≤ factor * dissipationBudget budget
    scaledBudget =
      let instance fNN = nonNegative factorNN
      in ℚP.*-monoˡ-≤-nonNeg factor
        (totalDissipationBelowBudget budget)

    replace = ℚP.+-mono-≤ ℚP.≤-refl scaledBudget
  in
  ℚP.≤-trans base replace

round97CappedExcessNeedsNoEscapeMargin : Bool
round97CappedExcessNeedsNoEscapeMargin = true

round97OnlyUnboundedSizeBranchNeedsAdditionalControl : Bool
round97OnlyUnboundedSizeBranchNeedsAdditionalControl = true

round97CappedExcessNeedsNoEscapeMarginIsTrue :
  round97CappedExcessNeedsNoEscapeMargin ≡ true
round97CappedExcessNeedsNoEscapeMarginIsTrue = refl

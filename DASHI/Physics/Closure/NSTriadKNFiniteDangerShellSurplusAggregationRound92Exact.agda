module DASHI.Physics.Closure.NSTriadKNFiniteDangerShellSurplusAggregationRound92Exact where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Finite dangerous-shell strict-surplus aggregation".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is exact finite ordered-field algebra.
--
-- ROUND92 / LOCAL-TO-FINITE-SHELL COMPILER
--
-- Once one physical shell has a same-object good/bad certificate
--
--      bad + delta D <= good,
--
-- its NET signed nonlinear contribution N = bad - good satisfies
--
--      N + delta D <= 0.
--
-- Summing a finite family of shells with the SAME positive margin delta keeps
-- that margin exactly:
--
--      sum N_K + delta sum D_K <= 0.
--
-- Thus finite simultaneous dangerous-shell aggregation does not consume any
-- additional viscosity.  The hard PDE content remains the construction of the
-- local certificates and the time/packet coverage, not the shell summation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record DangerShellMarginCell (delta : ℚ) : Set where
  constructor danger-shell-margin-cell
  field
    bad good dissipation : ℚ
    localStrictCoercivity :
      bad + delta * dissipation ≤ good

open DangerShellMarginCell public

netProduction : ∀ {delta} → DangerShellMarginCell delta → ℚ
netProduction cell = bad cell - good cell

localStrictCoercivityToNetDamping :
  ∀ {delta} (cell : DangerShellMarginCell delta) →
  netProduction cell + delta * dissipation cell ≤ 0ℚ
localStrictCoercivityToNetDamping {delta} cell =
  let
    shifted = ℚP.+-monoʳ-≤ (- good cell) (localStrictCoercivity cell)
    leftMeaning :
      (bad cell + delta * dissipation cell) + (- good cell)
      ≡ netProduction cell + delta * dissipation cell
    leftMeaning = solve (bad cell ∷ good cell ∷ delta ∷ dissipation cell ∷ [])
    rightMeaning : good cell + (- good cell) ≡ 0ℚ
    rightMeaning = solve (good cell ∷ [])
  in
  subst
    (λ left → left ≤ 0ℚ)
    leftMeaning
    (subst
      (λ right →
        (bad cell + delta * dissipation cell) + (- good cell) ≤ right)
      rightMeaning shifted)

sumProduction : ∀ {delta} → List (DangerShellMarginCell delta) → ℚ
sumProduction [] = 0ℚ
sumProduction (cell ∷ rest) = netProduction cell + sumProduction rest

sumDissipation : ∀ {delta} → List (DangerShellMarginCell delta) → ℚ
sumDissipation [] = 0ℚ
sumDissipation (cell ∷ rest) = dissipation cell + sumDissipation rest

finiteDangerShellStrictSurplus :
  ∀ {delta} (cells : List (DangerShellMarginCell delta)) →
  sumProduction cells + delta * sumDissipation cells ≤ 0ℚ
finiteDangerShellStrictSurplus {delta} [] = ℚP.≤-refl
finiteDangerShellStrictSurplus {delta} (cell ∷ rest) =
  let
    head = localStrictCoercivityToNetDamping cell
    tail = finiteDangerShellStrictSurplus rest
    added = ℚP.+-mono-≤ head tail

    leftMeaning :
      (netProduction cell + delta * dissipation cell)
        + (sumProduction rest + delta * sumDissipation rest)
      ≡ sumProduction (cell ∷ rest)
          + delta * sumDissipation (cell ∷ rest)
    leftMeaning =
      solve
        ( netProduction cell ∷ dissipation cell
        ∷ sumProduction rest ∷ sumDissipation rest ∷ delta ∷ [])

    rightMeaning : 0ℚ + 0ℚ ≡ 0ℚ
    rightMeaning = solve []
  in
  subst
    (λ left → left ≤ 0ℚ)
    leftMeaning
    (subst
      (λ right →
        (netProduction cell + delta * dissipation cell)
          + (sumProduction rest + delta * sumDissipation rest) ≤ right)
      rightMeaning added)

round92LocalSignedCoercivityCompilesToNetDamping : Bool
round92LocalSignedCoercivityCompilesToNetDamping = true

round92FiniteDangerShellAggregationPreservesMargin : Bool
round92FiniteDangerShellAggregationPreservesMargin = true

round92FiniteDangerShellAggregationPreservesMarginIsTrue :
  round92FiniteDangerShellAggregationPreservesMargin ≡ true
round92FiniteDangerShellAggregationPreservesMarginIsTrue = refl

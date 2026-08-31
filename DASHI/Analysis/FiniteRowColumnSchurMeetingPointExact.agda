module DASHI.Analysis.FiniteRowColumnSchurMeetingPointExact where

------------------------------------------------------------------------
-- MINIMAL FINITE ROW/COLUMN SCHUR MEETING POINT
--
-- Domain-specific owners should retain their literal finite kernel and prove
-- the row/column estimates there.  The generic downstream algebra needs only
--
--   Y <= R * W,
--   W <= C * X,
--
-- with R >= 0.  Here W is the row-Cauchy weighted input mass after summing
-- over output rows; the domain's column enumeration proves W <= C X.
-- Therefore
--
--   Y <= R C X.
--
-- This intentionally does NOT define a matrix, invent row/column cardinality,
-- or hide a kernel sum.  It is the weakest scalar interface shared by the
-- finite Cauchy producer and the downstream Schur consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record FiniteRowColumnSchurReceipt : Set where
  constructor finite-row-column-schur-receipt
  field
    outputMass rowBudget rowWeightedInput columnBudget inputMass : ℚ

    rowBudgetNonnegative : 0ℚ ≤ rowBudget
    columnBudgetNonnegative : 0ℚ ≤ columnBudget
    inputMassNonnegative : 0ℚ ≤ inputMass
    rowWeightedInputNonnegative : 0ℚ ≤ rowWeightedInput

    rowCauchyBound :
      outputMass ≤ rowBudget * rowWeightedInput

    columnAggregationBound :
      rowWeightedInput ≤ columnBudget * inputMass

open FiniteRowColumnSchurReceipt public

finiteRowColumnSchurSquaredBound :
  (D : FiniteRowColumnSchurReceipt) →
  outputMass D ≤ (rowBudget D * columnBudget D) * inputMass D
finiteRowColumnSchurSquaredBound D =
  let
    scaledColumn :
      rowBudget D * rowWeightedInput D
      ≤ rowBudget D * (columnBudget D * inputMass D)
    scaledColumn =
      let instance rowNN = nonNegative (rowBudgetNonnegative D)
      in ℚP.*-monoˡ-≤-nonNeg (rowBudget D) (columnAggregationBound D)

    normalized :
      rowBudget D * (columnBudget D * inputMass D)
      ≡ (rowBudget D * columnBudget D) * inputMass D
    normalized = solve
      (rowBudget D ∷ columnBudget D ∷ inputMass D ∷ [])
  in
  ℚP.≤-trans
    (rowCauchyBound D)
    (subst
      (λ upper → rowBudget D * rowWeightedInput D ≤ upper)
      normalized
      scaledColumn)

roundFiniteSchurCompilerIntroducesKernelCardinality : Bool
roundFiniteSchurCompilerIntroducesKernelCardinality = false

roundFiniteSchurCompilerRequiresDomainRowReceipt : Bool
roundFiniteSchurCompilerRequiresDomainRowReceipt = true

roundFiniteSchurCompilerRequiresDomainColumnReceipt : Bool
roundFiniteSchurCompilerRequiresDomainColumnReceipt = true

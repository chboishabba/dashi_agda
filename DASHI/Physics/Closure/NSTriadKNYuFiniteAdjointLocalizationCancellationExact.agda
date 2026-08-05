module DASHI.Physics.Closure.NSTriadKNYuFiniteAdjointLocalizationCancellationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Record the exact algebraic cancellation used for the adjoint localization
-- term.  Once the continuum producer proves that the adjoint filtered
-- operator applied to the constant function vanishes,
--
--   C_ell^* 1 = 0,
--
-- every residual density containing it as a factor vanishes, and so does its
-- finite sum.  This removes that one localization subterm only; annular cutoff
-- derivatives and the other localization budgets remain visible elsewhere.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

record AdjointLocalizationCell : Set where
  constructor adjoint-localization-cell
  field
    localizationCoefficient adjointOnConstant : ℚ
    adjointKillsConstant : adjointOnConstant ≡ 0ℚ

open AdjointLocalizationCell public

adjointLocalizationResidual : AdjointLocalizationCell → ℚ
adjointLocalizationResidual cell =
  localizationCoefficient cell * adjointOnConstant cell

adjointLocalizationResidualVanishes :
  (cell : AdjointLocalizationCell) →
  adjointLocalizationResidual cell ≡ 0ℚ
adjointLocalizationResidualVanishes cell
  rewrite adjointKillsConstant cell = solve (localizationCoefficient cell ∷ [])

sumAdjointLocalizationResidual : List AdjointLocalizationCell → ℚ
sumAdjointLocalizationResidual [] = 0ℚ
sumAdjointLocalizationResidual (cell ∷ cells) =
  adjointLocalizationResidual cell
  + sumAdjointLocalizationResidual cells

allAdjointLocalizationResidualsVanish :
  (cells : List AdjointLocalizationCell) →
  sumAdjointLocalizationResidual cells ≡ 0ℚ
allAdjointLocalizationResidualsVanish [] = refl
allAdjointLocalizationResidualsVanish (cell ∷ cells)
  rewrite adjointLocalizationResidualVanishes cell
        | allAdjointLocalizationResidualsVanish cells =
  solve []

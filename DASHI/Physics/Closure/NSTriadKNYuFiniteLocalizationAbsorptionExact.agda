module DASHI.Physics.Closure.NSTriadKNYuFiniteLocalizationAbsorptionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- arXiv:2606.27560v1.
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Local-energy reference:
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the Navier-Stokes
-- equations".
-- DOI: 10.1080/03605308208820218.
--
-- PURPOSE
-- Close the exact algebra of the remaining cutoff budget.  The gradient
-- cutoff term is paid by epsilon diffusion plus a reservoir, while the
-- Laplacian/time-cutoff term is paid entirely by a reservoir.  Their sum is
-- therefore
--
--   L <= epsilon P + (C_grad + C_zero) O.
--
-- The localized Caccioppoli/Poincare estimates producing the two component
-- bounds remain explicit fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record LocalizationAbsorptionData : Set where
  constructor localization-absorption-data
  field
    gradientCutoffResidual zeroOrderCutoffResidual : ℚ
    diffusion reservoir : ℚ
    epsilon gradientReservoirCoefficient : ℚ
    zeroOrderReservoirCoefficient : ℚ

    gradientCutoffBound :
      gradientCutoffResidual
      ≤ epsilon * diffusion
        + gradientReservoirCoefficient * reservoir

    zeroOrderCutoffBound :
      zeroOrderCutoffResidual
      ≤ zeroOrderReservoirCoefficient * reservoir

open LocalizationAbsorptionData public

totalLocalizationResidual : LocalizationAbsorptionData → ℚ
totalLocalizationResidual dataSet =
  gradientCutoffResidual dataSet + zeroOrderCutoffResidual dataSet

combinedLocalizationCoefficient : LocalizationAbsorptionData → ℚ
combinedLocalizationCoefficient dataSet =
  gradientReservoirCoefficient dataSet
  + zeroOrderReservoirCoefficient dataSet

localizationDiffusionAbsorption :
  (dataSet : LocalizationAbsorptionData) →
  totalLocalizationResidual dataSet
  ≤ epsilon dataSet * diffusion dataSet
    + combinedLocalizationCoefficient dataSet * reservoir dataSet
localizationDiffusionAbsorption dataSet =
  let
    summed :
      gradientCutoffResidual dataSet + zeroOrderCutoffResidual dataSet
      ≤ (epsilon dataSet * diffusion dataSet
          + gradientReservoirCoefficient dataSet * reservoir dataSet)
        + zeroOrderReservoirCoefficient dataSet * reservoir dataSet
    summed =
      ℚₚ.+-mono-≤
        (gradientCutoffBound dataSet)
        (zeroOrderCutoffBound dataSet)

    targetMeaning :
      (epsilon dataSet * diffusion dataSet
        + gradientReservoirCoefficient dataSet * reservoir dataSet)
        + zeroOrderReservoirCoefficient dataSet * reservoir dataSet
      ≡ epsilon dataSet * diffusion dataSet
        + (gradientReservoirCoefficient dataSet
          + zeroOrderReservoirCoefficient dataSet)
          * reservoir dataSet
    targetMeaning =
      solve
        ( epsilon dataSet
        ∷ diffusion dataSet
        ∷ gradientReservoirCoefficient dataSet
        ∷ zeroOrderReservoirCoefficient dataSet
        ∷ reservoir dataSet
        ∷ [])
  in
  subst
    (λ upper → totalLocalizationResidual dataSet ≤ upper)
    targetMeaning
    summed

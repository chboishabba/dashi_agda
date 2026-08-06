module DASHI.Physics.Closure.NSTriadKNYuLocalizationCaccioppoliTailExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial Regularity of Suitable Weak Solutions of the
-- Navier--Stokes Equations".
-- DOI: 10.1080/03605308208820218.
--
-- PURPOSE
-- Supply the exact algebraic absorption step behind a localized Caccioppoli
-- estimate. For epsilon>0 and epsilonInv satisfying epsilon*epsilonInv=1,
--
--   2 a b <= epsilon a^2 + epsilonInv b^2.
--
-- This is proved from the nonnegative square
--
--   epsilonInv (epsilon a - b)^2.
--
-- The theorem is then inserted into a localization balance, leaving only the
-- genuine PDE task of identifying the diffusion, cutoff-observation and
-- remainder quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

record YoungParameter : Set where
  constructor young-parameter
  field
    epsilon epsilonInverse : ℚ
    epsilonPositive : 0ℚ < epsilon
    epsilonInverseNonnegative : 0ℚ ≤ epsilonInverse
    inverseMeaning : epsilon * epsilonInverse ≡ 1ℚ

open YoungParameter public

orderedYoungTwoProduct :
  (parameter : YoungParameter) →
  (a b : ℚ) →
  a * b + a * b
  ≤ epsilon parameter * L2.square a
    + epsilonInverse parameter * L2.square b
orderedYoungTwoProduct parameter a b =
  let
    squareNN : 0ℚ ≤ L2.square (epsilon parameter * a - b)
    squareNN = L2.squareNonnegative (epsilon parameter * a - b)

    defectNN :
      0ℚ
      ≤ epsilonInverse parameter
        * L2.square (epsilon parameter * a - b)
    defectNN =
      let
        instance
          inverseNN = nonNegative (epsilonInverseNonnegative parameter)
          squareNNI = nonNegative squareNN
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (epsilonInverse parameter)
              (L2.square (epsilon parameter * a - b))
      in
      ℚₚ.nonNegative⁻¹
        (epsilonInverse parameter
          * L2.square (epsilon parameter * a - b))

    addDefect :
      a * b + a * b
      ≤ a * b + a * b
        + epsilonInverse parameter
          * L2.square (epsilon parameter * a - b)
    addDefect =
      subst
        (λ lower →
          lower
          ≤ a * b + a * b
            + epsilonInverse parameter
              * L2.square (epsilon parameter * a - b))
        (ℚₚ.+-identityʳ (a * b + a * b))
        (ℚₚ.+-monoʳ-≤ (a * b + a * b) defectNN)

    identity :
      a * b + a * b
        + epsilonInverse parameter
          * L2.square (epsilon parameter * a - b)
      ≡ epsilon parameter * L2.square a
        + epsilonInverse parameter * L2.square b
    identity =
      subst
        (λ product →
          a * b + a * b
            + epsilonInverse parameter
              * L2.square (epsilon parameter * a - b)
          ≡ product * L2.square a
            + epsilonInverse parameter * L2.square b)
        (sym (inverseMeaning parameter))
        (solve
          ( epsilon parameter
          ∷ epsilonInverse parameter
          ∷ a ∷ b ∷ []))
  in
  subst
    (λ upper → a * b + a * b ≤ upper)
    identity
    addDefect

record LocalizationCaccioppoliCell : Set where
  constructor localization-caccioppoli-cell
  field
    parameter : YoungParameter
    localization diffusion observation remainder : ℚ
    gradientFactor cutoffFactor : ℚ

    localizationBound :
      localization
      ≤ diffusion
        + (gradientFactor * cutoffFactor
          + gradientFactor * cutoffFactor)
        + observation

    diffusionMeaning : L2.square gradientFactor ≡ diffusion
    remainderMeaning : L2.square cutoffFactor ≡ remainder

open LocalizationCaccioppoliCell public

localizationCaccioppoliBound :
  (cell : LocalizationCaccioppoliCell) →
  localization cell
  ≤ diffusion cell
    + epsilon (parameter cell) * diffusion cell
    + epsilonInverse (parameter cell) * remainder cell
    + observation cell
localizationCaccioppoliBound cell =
  let
    young =
      orderedYoungTwoProduct
        (parameter cell)
        (gradientFactor cell)
        (cutoffFactor cell)

    middleAdjusted :
      gradientFactor cell * cutoffFactor cell
        + gradientFactor cell * cutoffFactor cell
      ≤ epsilon (parameter cell) * diffusion cell
        + epsilonInverse (parameter cell) * remainder cell
    middleAdjusted =
      subst
        (λ gradientSquare →
          gradientFactor cell * cutoffFactor cell
            + gradientFactor cell * cutoffFactor cell
          ≤ epsilon (parameter cell) * gradientSquare
            + epsilonInverse (parameter cell) * remainder cell)
        (diffusionMeaning cell)
        (subst
          (λ cutoffSquare →
            gradientFactor cell * cutoffFactor cell
              + gradientFactor cell * cutoffFactor cell
            ≤ epsilon (parameter cell)
                * L2.square (gradientFactor cell)
              + epsilonInverse (parameter cell) * cutoffSquare)
          (remainderMeaning cell)
          young)

    assembled =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤ ℚₚ.≤-refl middleAdjusted)
        ℚₚ.≤-refl

    endpoint :
      diffusion cell
        + (epsilon (parameter cell) * diffusion cell
          + epsilonInverse (parameter cell) * remainder cell)
        + observation cell
      ≡ diffusion cell
        + epsilon (parameter cell) * diffusion cell
        + epsilonInverse (parameter cell) * remainder cell
        + observation cell
    endpoint = solve
      ( diffusion cell
      ∷ epsilon (parameter cell)
      ∷ epsilonInverse (parameter cell)
      ∷ remainder cell
      ∷ observation cell
      ∷ [])
  in
  ℚₚ.≤-trans
    (localizationBound cell)
    (subst
      (λ upper →
        diffusion cell
          + (gradientFactor cell * cutoffFactor cell
            + gradientFactor cell * cutoffFactor cell)
          + observation cell
        ≤ upper)
      endpoint
      assembled)

record LocalizationTailTransferData : Set where
  constructor localization-tail-transfer-data
  field
    localization controllingTail : ℕ → ℚ
    pointwiseBound :
      (shell : ℕ) → localization shell ≤ controllingTail shell

open LocalizationTailTransferData public

localizationVanishingFromCaccioppoliTail :
  (dataSet : LocalizationTailTransferData) →
  Limit.TendsToZero (controllingTail dataSet) →
  Limit.TendsToZero (localization dataSet)
localizationVanishingFromCaccioppoliTail dataSet tailVanishing =
  Limit.interactionDepletionFromCriticalDepletion
    (Limit.critical-to-interaction-data
      (localization dataSet)
      (controllingTail dataSet)
      (pointwiseBound dataSet))
    tailVanishing

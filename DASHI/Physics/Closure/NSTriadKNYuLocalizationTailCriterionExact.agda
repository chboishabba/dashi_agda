module DASHI.Physics.Closure.NSTriadKNYuLocalizationTailCriterionExact where

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
-- Navier-Stokes Equations".
-- DOI: 10.1080/03605308208820218.
--
-- PURPOSE
-- Close the epsilon transfer for the localization remainder after diffusion
-- absorption.  If shellwise
--
--   L_q <= absorbedDiffusion_q + observation_q,
--
-- and a common tail makes both nonnegative envelopes at most epsilon/2, then
-- the complete localization tail is at most epsilon.  This is the exact final
-- step required after a localized Caccioppoli/Poincare estimate supplies the
-- two tail bounds.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (ℕ; _≤_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

half : ℚ
half = Int.+ 1 / 2

record LocalizationTailData : Set where
  constructor localization-tail-data
  field
    localizationTail absorbedDiffusionTail observationTail : ℕ → ℚ

    localizationPointwiseBound :
      (shell : ℕ) →
      localizationTail shell
      ≤ absorbedDiffusionTail shell + observationTail shell

open LocalizationTailData public

record JointLocalizationVanishing
  (dataSet : LocalizationTailData) : Set where
  constructor joint-localization-vanishing
  field
    commonTail :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      ℕ

    absorbedDiffusionTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      absorbedDiffusionTail dataSet shell ≤ half * epsilon

    observationTailBound :
      (epsilon : ℚ) →
      (epsilonPositive : 0ℚ < epsilon) →
      (shell : ℕ) →
      commonTail epsilon epsilonPositive ≤ shell →
      observationTail dataSet shell ≤ half * epsilon

open JointLocalizationVanishing public

localizationTailVanishing :
  (dataSet : LocalizationTailData) →
  JointLocalizationVanishing dataSet →
  Limit.TendsToZero (localizationTail dataSet)
localizationTailVanishing dataSet joint =
  Limit.tends-to-zero transfer
  where
  transfer :
    (epsilon : ℚ) →
    0ℚ < epsilon →
    Limit.EventuallyBelow (localizationTail dataSet) epsilon
  transfer epsilon epsilonPositive =
    let
      cutoff = commonTail joint epsilon epsilonPositive

      tail :
        (shell : ℕ) →
        cutoff ≤ shell →
        localizationTail dataSet shell ≤ epsilon
      tail shell cutoffBelowShell =
        let
          summed :
            absorbedDiffusionTail dataSet shell
              + observationTail dataSet shell
            ≤ half * epsilon + half * epsilon
          summed =
            ℚₚ.+-mono-≤
              (absorbedDiffusionTailBound
                joint epsilon epsilonPositive shell cutoffBelowShell)
              (observationTailBound
                joint epsilon epsilonPositive shell cutoffBelowShell)

          epsilonMeaning :
            half * epsilon + half * epsilon ≡ epsilon
          epsilonMeaning = solve (epsilon ∷ [])
        in
        ℚₚ.≤-trans
          (localizationPointwiseBound dataSet shell)
          (subst
            (λ upper →
              absorbedDiffusionTail dataSet shell
                + observationTail dataSet shell
              ≤ upper)
            epsilonMeaning
            summed)
    in
    Limit.eventually-below cutoff tail

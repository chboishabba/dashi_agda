module DASHI.Physics.Closure.NSTriadKNLuoFiniteNormalizedWeightedJensenExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Johan Jensen.
-- Result: normalized weighted Jensen inequality for the square function.
-- DOI: not applicable to this classical inequality.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Extract the two forms needed for finite time windows from the exact weighted
-- variance-defect theorem.  Unit total mass gives
--
--   (sum w_i a_i)^2 <= sum w_i a_i^2.
--
-- More generally, an explicitly named interval mass M gives the division-free
-- form
--
--   (sum w_i a_i)^2 <= M sum w_i a_i^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Jensen

record NormalizedWeightedWindow : Set where
  constructor normalized-weighted-window
  field
    normalizedSamples : List Jensen.WeightedValue
    massIsOne : Jensen.mass normalizedSamples ≡ 1ℚ

open NormalizedWeightedWindow public

normalizedWeightedJensen :
  (window : NormalizedWeightedWindow) →
  L2.square (Jensen.firstMoment (normalizedSamples window))
  ≤ Jensen.secondMoment (normalizedSamples window)
normalizedWeightedJensen window =
  let
    unitMassBound :
      L2.square (Jensen.firstMoment (normalizedSamples window))
      ≤ 1ℚ * Jensen.secondMoment (normalizedSamples window)
    unitMassBound =
      subst
        (λ massValue →
          L2.square (Jensen.firstMoment (normalizedSamples window))
          ≤ massValue * Jensen.secondMoment (normalizedSamples window))
        (massIsOne window)
        (Jensen.finiteWeightedJensenSquare (normalizedSamples window))

    unitMeaning :
      1ℚ * Jensen.secondMoment (normalizedSamples window)
      ≡ Jensen.secondMoment (normalizedSamples window)
    unitMeaning = solve (Jensen.secondMoment (normalizedSamples window) ∷ [])
  in
  subst
    (λ upper →
      L2.square (Jensen.firstMoment (normalizedSamples window)) ≤ upper)
    unitMeaning
    unitMassBound

record WeightedIntervalWindow : Set where
  constructor weighted-interval-window
  field
    intervalSamples : List Jensen.WeightedValue
    intervalMass : ℚ
    intervalMassMeaning : Jensen.mass intervalSamples ≡ intervalMass

open WeightedIntervalWindow public

intervalWeightedJensen :
  (window : WeightedIntervalWindow) →
  L2.square (Jensen.firstMoment (intervalSamples window))
  ≤ intervalMass window * Jensen.secondMoment (intervalSamples window)
intervalWeightedJensen window =
  subst
    (λ massValue →
      L2.square (Jensen.firstMoment (intervalSamples window))
      ≤ massValue * Jensen.secondMoment (intervalSamples window))
    (intervalMassMeaning window)
    (Jensen.finiteWeightedJensenSquare (intervalSamples window))

finiteNormalizedWeightedJensenClosed : Bool
finiteNormalizedWeightedJensenClosed = true

finiteIntervalWeightedJensenClosed : Bool
finiteIntervalWeightedJensenClosed = true

finiteNormalizedWeightedJensenClosedIsTrue :
  finiteNormalizedWeightedJensenClosed ≡ true
finiteNormalizedWeightedJensenClosedIsTrue = refl

finiteIntervalWeightedJensenClosedIsTrue :
  finiteIntervalWeightedJensenClosed ≡ true
finiteIntervalWeightedJensenClosedIsTrue = refl

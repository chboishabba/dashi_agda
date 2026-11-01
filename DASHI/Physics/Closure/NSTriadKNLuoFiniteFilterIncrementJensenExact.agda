module DASHI.Physics.Closure.NSTriadKNLuoFiniteFilterIncrementJensenExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Author: Anthony Leonard.
-- Title: "Energy Cascade in Large-Eddy Simulations of Turbulent Fluid
-- Flows".
-- DOI: 10.1016/S0065-2687(08)60464-1.
--
-- DASHI CONTRIBUTION
--
-- This module proves a finite, radical-free Jensen estimate for filtered
-- vorticity increments.  Quadrature weights are represented as rational
-- squares w_i = s_i^2, so ordinary finite Cauchy--Schwarz applies without
-- adjoining square roots:
--
--   |sum_i w_i delta_i|^2
--     <= (sum_i w_i) (sum_i w_i |delta_i|^2).
--
-- Under normalized total weight one,
--
--   |delta Omega_filter|^2
--     <= sum_i w_i |delta omega_i|^2.
--
-- This is the exact finite filter-smoothing bridge needed between the
-- magnitude-weighted direction defect and a first-order vorticity-increment
-- reservoir.  The remaining analytic step is passing from the quadrature to
-- the continuum convolution and then bounding the weighted increment integral
-- by filtered diffusion with constants uniform in scale.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using
  (ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram

record FilterIncrementSample : Set where
  constructor filterIncrementSample
  field
    squareRootWeight : ℚ
    increment : Gram.Vec3

open FilterIncrementSample public

xPairs : List FilterIncrementSample → List L2.Pair
xPairs [] = []
xPairs (sample ∷ samples) =
  ( squareRootWeight sample
  , squareRootWeight sample * Gram.x (increment sample) )
  ∷ xPairs samples

yPairs : List FilterIncrementSample → List L2.Pair
yPairs [] = []
yPairs (sample ∷ samples) =
  ( squareRootWeight sample
  , squareRootWeight sample * Gram.y (increment sample) )
  ∷ yPairs samples

zPairs : List FilterIncrementSample → List L2.Pair
zPairs [] = []
zPairs (sample ∷ samples) =
  ( squareRootWeight sample
  , squareRootWeight sample * Gram.z (increment sample) )
  ∷ zPairs samples

totalFilterWeight : List FilterIncrementSample → ℚ
totalFilterWeight samples = L2.leftNormSquared (xPairs samples)

weightedXEnergy : List FilterIncrementSample → ℚ
weightedXEnergy samples = L2.rightNormSquared (xPairs samples)

weightedYEnergy : List FilterIncrementSample → ℚ
weightedYEnergy samples = L2.rightNormSquared (yPairs samples)

weightedZEnergy : List FilterIncrementSample → ℚ
weightedZEnergy samples = L2.rightNormSquared (zPairs samples)

weightedIncrementEnergy : List FilterIncrementSample → ℚ
weightedIncrementEnergy samples =
  weightedXEnergy samples + weightedYEnergy samples + weightedZEnergy samples

sumWeightedIncrement : List FilterIncrementSample → Gram.Vec3
sumWeightedIncrement samples =
  Gram.vec3
    (L2.pairDot (xPairs samples))
    (L2.pairDot (yPairs samples))
    (L2.pairDot (zPairs samples))

yWeightMeaning :
  ∀ samples →
  L2.leftNormSquared (yPairs samples) ≡ totalFilterWeight samples
yWeightMeaning [] = refl
yWeightMeaning (sample ∷ samples)
  rewrite yWeightMeaning samples = refl

zWeightMeaning :
  ∀ samples →
  L2.leftNormSquared (zPairs samples) ≡ totalFilterWeight samples
zWeightMeaning [] = refl
zWeightMeaning (sample ∷ samples)
  rewrite zWeightMeaning samples = refl

componentXJensen :
  ∀ samples →
  L2.square (Gram.x (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedXEnergy samples
componentXJensen samples = L2.finiteCauchySchwarzSquared (xPairs samples)

componentYJensen :
  ∀ samples →
  L2.square (Gram.y (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedYEnergy samples
componentYJensen samples =
  subst
    (λ weight →
      L2.square (L2.pairDot (yPairs samples))
      ≤ weight * weightedYEnergy samples)
    (yWeightMeaning samples)
    (L2.finiteCauchySchwarzSquared (yPairs samples))

componentZJensen :
  ∀ samples →
  L2.square (Gram.z (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedZEnergy samples
componentZJensen samples =
  subst
    (λ weight →
      L2.square (L2.pairDot (zPairs samples))
      ≤ weight * weightedZEnergy samples)
    (zWeightMeaning samples)
    (L2.finiteCauchySchwarzSquared (zPairs samples))

finiteFilterIncrementJensen :
  ∀ samples →
  Gram.normSquared (sumWeightedIncrement samples)
  ≤ totalFilterWeight samples * weightedIncrementEnergy samples
finiteFilterIncrementJensen samples =
  let
    summed =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (componentXJensen samples)
          (componentYJensen samples))
        (componentZJensen samples)

    rightMeaning :
      totalFilterWeight samples * weightedXEnergy samples
      + totalFilterWeight samples * weightedYEnergy samples
      + totalFilterWeight samples * weightedZEnergy samples
      ≡ totalFilterWeight samples * weightedIncrementEnergy samples
    rightMeaning =
      solve
        ( totalFilterWeight samples
        ∷ weightedXEnergy samples
        ∷ weightedYEnergy samples
        ∷ weightedZEnergy samples
        ∷ [])
  in
  subst
    (λ upper →
      Gram.normSquared (sumWeightedIncrement samples) ≤ upper)
    rightMeaning
    summed

record NormalizedFiniteFilter : Set where
  constructor normalizedFiniteFilter
  field
    samples : List FilterIncrementSample
    normalizedWeight : totalFilterWeight samples ≡ 1ℚ

open NormalizedFiniteFilter public

normalizedFiniteFilterIncrementJensen :
  ∀ filter →
  Gram.normSquared (sumWeightedIncrement (samples filter))
  ≤ weightedIncrementEnergy (samples filter)
normalizedFiniteFilterIncrementJensen filter =
  let
    base = finiteFilterIncrementJensen (samples filter)

    rightMeaning :
      totalFilterWeight (samples filter)
        * weightedIncrementEnergy (samples filter)
      ≡ weightedIncrementEnergy (samples filter)
    rightMeaning
      rewrite normalizedWeight filter =
      solve (weightedIncrementEnergy (samples filter) ∷ [])
  in
  subst
    (λ upper →
      Gram.normSquared (sumWeightedIncrement (samples filter)) ≤ upper)
    rightMeaning
    base

record FilterIncrementJensenAuthorityBoundary : Set where
  constructor filterIncrementJensenAuthorityBoundary
  field
    finiteSquaredWeightJensenProved : Set
    normalizedFilterContractionProved : Set
    continuumConvolutionLimitProved : Set
    differenceQuotientToDiffusionProved : Set
    uniformScaleConstantProduced : Set

canonicalFilterIncrementJensenAuthorityBoundary :
  FilterIncrementJensenAuthorityBoundary
canonicalFilterIncrementJensenAuthorityBoundary =
  filterIncrementJensenAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)

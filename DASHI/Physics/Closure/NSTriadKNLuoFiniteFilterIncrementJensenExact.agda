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

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact as Cross

record FilterIncrementSample : Set where
  constructor filterIncrementSample
  field
    squareRootWeight : ℚ
    increment : Gram.Vec3

open FilterIncrementSample public

sampleWeight : FilterIncrementSample → ℚ
sampleWeight sample = L2.square (squareRootWeight sample)

weightedIncrement : FilterIncrementSample → Gram.Vec3
weightedIncrement sample =
  Cross.scaleVec (sampleWeight sample) (increment sample)

sumWeightedIncrement : List FilterIncrementSample → Gram.Vec3
sumWeightedIncrement [] = Gram.vec3 0ℚ 0ℚ 0ℚ
sumWeightedIncrement (sample ∷ samples) =
  Cross.vecAdd (weightedIncrement sample) (sumWeightedIncrement samples)

totalFilterWeight : List FilterIncrementSample → ℚ
totalFilterWeight [] = 0ℚ
totalFilterWeight (sample ∷ samples) =
  sampleWeight sample + totalFilterWeight samples

weightedIncrementEnergy : List FilterIncrementSample → ℚ
weightedIncrementEnergy [] = 0ℚ
weightedIncrementEnergy (sample ∷ samples) =
  sampleWeight sample * Gram.normSquared (increment sample)
  + weightedIncrementEnergy samples

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

pairDotXMeaning :
  ∀ samples →
  L2.pairDot (xPairs samples) ≡ Gram.x (sumWeightedIncrement samples)
pairDotXMeaning [] = solve []
pairDotXMeaning (sample ∷ samples)
  rewrite pairDotXMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.x (increment sample)
    ∷ Gram.x (sumWeightedIncrement samples)
    ∷ [])

pairDotYMeaning :
  ∀ samples →
  L2.pairDot (yPairs samples) ≡ Gram.y (sumWeightedIncrement samples)
pairDotYMeaning [] = solve []
pairDotYMeaning (sample ∷ samples)
  rewrite pairDotYMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.y (increment sample)
    ∷ Gram.y (sumWeightedIncrement samples)
    ∷ [])

pairDotZMeaning :
  ∀ samples →
  L2.pairDot (zPairs samples) ≡ Gram.z (sumWeightedIncrement samples)
pairDotZMeaning [] = solve []
pairDotZMeaning (sample ∷ samples)
  rewrite pairDotZMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.z (increment sample)
    ∷ Gram.z (sumWeightedIncrement samples)
    ∷ [])

leftNormXMeaning :
  ∀ samples →
  L2.leftNormSquared (xPairs samples) ≡ totalFilterWeight samples
leftNormXMeaning [] = solve []
leftNormXMeaning (sample ∷ samples)
  rewrite leftNormXMeaning samples = solve []

leftNormYMeaning :
  ∀ samples →
  L2.leftNormSquared (yPairs samples) ≡ totalFilterWeight samples
leftNormYMeaning [] = solve []
leftNormYMeaning (sample ∷ samples)
  rewrite leftNormYMeaning samples = solve []

leftNormZMeaning :
  ∀ samples →
  L2.leftNormSquared (zPairs samples) ≡ totalFilterWeight samples
leftNormZMeaning [] = solve []
leftNormZMeaning (sample ∷ samples)
  rewrite leftNormZMeaning samples = solve []

weightedXEnergy : List FilterIncrementSample → ℚ
weightedXEnergy [] = 0ℚ
weightedXEnergy (sample ∷ samples) =
  sampleWeight sample * L2.square (Gram.x (increment sample))
  + weightedXEnergy samples

weightedYEnergy : List FilterIncrementSample → ℚ
weightedYEnergy [] = 0ℚ
weightedYEnergy (sample ∷ samples) =
  sampleWeight sample * L2.square (Gram.y (increment sample))
  + weightedYEnergy samples

weightedZEnergy : List FilterIncrementSample → ℚ
weightedZEnergy [] = 0ℚ
weightedZEnergy (sample ∷ samples) =
  sampleWeight sample * L2.square (Gram.z (increment sample))
  + weightedZEnergy samples

rightNormXMeaning :
  ∀ samples →
  L2.rightNormSquared (xPairs samples) ≡ weightedXEnergy samples
rightNormXMeaning [] = solve []
rightNormXMeaning (sample ∷ samples)
  rewrite rightNormXMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.x (increment sample)
    ∷ weightedXEnergy samples
    ∷ [])

rightNormYMeaning :
  ∀ samples →
  L2.rightNormSquared (yPairs samples) ≡ weightedYEnergy samples
rightNormYMeaning [] = solve []
rightNormYMeaning (sample ∷ samples)
  rewrite rightNormYMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.y (increment sample)
    ∷ weightedYEnergy samples
    ∷ [])

rightNormZMeaning :
  ∀ samples →
  L2.rightNormSquared (zPairs samples) ≡ weightedZEnergy samples
rightNormZMeaning [] = solve []
rightNormZMeaning (sample ∷ samples)
  rewrite rightNormZMeaning samples =
  solve
    ( squareRootWeight sample
    ∷ Gram.z (increment sample)
    ∷ weightedZEnergy samples
    ∷ [])

componentXJensen :
  ∀ samples →
  L2.square (Gram.x (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedXEnergy samples
componentXJensen samples =
  subst
    (λ left →
      L2.square left
      ≤ totalFilterWeight samples * weightedXEnergy samples)
    (pairDotXMeaning samples)
    (subst
      (λ leftNorm →
        L2.square (L2.pairDot (xPairs samples))
        ≤ leftNorm * weightedXEnergy samples)
      (leftNormXMeaning samples)
      (subst
        (λ rightNorm →
          L2.square (L2.pairDot (xPairs samples))
          ≤ L2.leftNormSquared (xPairs samples) * rightNorm)
        (rightNormXMeaning samples)
        (L2.finiteCauchySchwarzSquared (xPairs samples))))

componentYJensen :
  ∀ samples →
  L2.square (Gram.y (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedYEnergy samples
componentYJensen samples =
  subst
    (λ left →
      L2.square left
      ≤ totalFilterWeight samples * weightedYEnergy samples)
    (pairDotYMeaning samples)
    (subst
      (λ leftNorm →
        L2.square (L2.pairDot (yPairs samples))
        ≤ leftNorm * weightedYEnergy samples)
      (leftNormYMeaning samples)
      (subst
        (λ rightNorm →
          L2.square (L2.pairDot (yPairs samples))
          ≤ L2.leftNormSquared (yPairs samples) * rightNorm)
        (rightNormYMeaning samples)
        (L2.finiteCauchySchwarzSquared (yPairs samples))))

componentZJensen :
  ∀ samples →
  L2.square (Gram.z (sumWeightedIncrement samples))
  ≤ totalFilterWeight samples * weightedZEnergy samples
componentZJensen samples =
  subst
    (λ left →
      L2.square left
      ≤ totalFilterWeight samples * weightedZEnergy samples)
    (pairDotZMeaning samples)
    (subst
      (λ leftNorm →
        L2.square (L2.pairDot (zPairs samples))
        ≤ leftNorm * weightedZEnergy samples)
      (leftNormZMeaning samples)
      (subst
        (λ rightNorm →
          L2.square (L2.pairDot (zPairs samples))
          ≤ L2.leftNormSquared (zPairs samples) * rightNorm)
        (rightNormZMeaning samples)
        (L2.finiteCauchySchwarzSquared (zPairs samples))))

weightedEnergyCoordinates :
  ∀ samples →
  weightedIncrementEnergy samples
  ≡ weightedXEnergy samples + weightedYEnergy samples + weightedZEnergy samples
weightedEnergyCoordinates [] = solve []
weightedEnergyCoordinates (sample ∷ samples)
  rewrite weightedEnergyCoordinates samples =
  solve
    ( sampleWeight sample
    ∷ Gram.x (increment sample)
    ∷ Gram.y (increment sample)
    ∷ Gram.z (increment sample)
    ∷ weightedXEnergy samples
    ∷ weightedYEnergy samples
    ∷ weightedZEnergy samples
    ∷ [])

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
    rightMeaning
      rewrite weightedEnergyCoordinates samples =
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

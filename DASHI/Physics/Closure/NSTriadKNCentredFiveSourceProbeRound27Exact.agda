module DASHI.Physics.Closure.NSTriadKNCentredFiveSourceProbeRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Structural precursor:
-- DASHI/Moonshine/Monster3BCentredProbeCoreSelectorExact.agda.
--
-- DASHI CONTRIBUTION
--
-- For the signed five-source vector
--
--   F_i = base + delta_i,
--
-- prove the division-free centred-probe identity
--
--   5 (w dot F)
--     = (sum w) aug(F)
--       + sum_i (5 w_i - sum w) delta_i.
--
-- Hence a weighted observable separates into a uniform augmentation and a
-- centred source-imbalance probe.  The theorem is exact algebra; it does not
-- estimate any source or promote a viscosity coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

zero one five : ℚ
zero = Int.+ 0 / 1
one = Int.+ 1 / 1
five = Int.+ 5 / 1

record FiveSourceCoreDefect : Set where
  constructor five-source-core-defect
  field
    commonBase : ℚ
    deltaHH deltaLH deltaHL deltaCC deltaCom : ℚ

open FiveSourceCoreDefect public

sourceHH sourceLH sourceHL sourceCC sourceCom :
  FiveSourceCoreDefect → ℚ
sourceHH source = commonBase source + deltaHH source
sourceLH source = commonBase source + deltaLH source
sourceHL source = commonBase source + deltaHL source
sourceCC source = commonBase source + deltaCC source
sourceCom source = commonBase source + deltaCom source

sourceAugmentation : FiveSourceCoreDefect → ℚ
sourceAugmentation source =
  sourceHH source + sourceLH source + sourceHL source
  + sourceCC source + sourceCom source

record FiveSourceWeights : Set where
  constructor five-source-weights
  field
    weightHH weightLH weightHL weightCC weightCom : ℚ

open FiveSourceWeights public

weightSum : FiveSourceWeights → ℚ
weightSum weights =
  weightHH weights + weightLH weights + weightHL weights
  + weightCC weights + weightCom weights

weightedSourceProbe :
  FiveSourceWeights → FiveSourceCoreDefect → ℚ
weightedSourceProbe weights source =
  weightHH weights * sourceHH source
  + weightLH weights * sourceLH source
  + weightHL weights * sourceHL source
  + weightCC weights * sourceCC source
  + weightCom weights * sourceCom source

centredDefectProbe :
  FiveSourceWeights → FiveSourceCoreDefect → ℚ
centredDefectProbe weights source =
  (five * weightHH weights - weightSum weights) * deltaHH source
  + (five * weightLH weights - weightSum weights) * deltaLH source
  + (five * weightHL weights - weightSum weights) * deltaHL source
  + (five * weightCC weights - weightSum weights) * deltaCC source
  + (five * weightCom weights - weightSum weights) * deltaCom source

centredFiveSourceProbeIdentity :
  (weights : FiveSourceWeights) →
  (source : FiveSourceCoreDefect) →
  five * weightedSourceProbe weights source
  ≡
  weightSum weights * sourceAugmentation source
  + centredDefectProbe weights source
centredFiveSourceProbeIdentity weights source =
  solve
    ( commonBase source
    ∷ deltaHH source ∷ deltaLH source ∷ deltaHL source
    ∷ deltaCC source ∷ deltaCom source
    ∷ weightHH weights ∷ weightLH weights ∷ weightHL weights
    ∷ weightCC weights ∷ weightCom weights
    ∷ [])

uniformWeightsIgnoreCentredDefect :
  (weight : ℚ) →
  (source : FiveSourceCoreDefect) →
  centredDefectProbe
    (five-source-weights weight weight weight weight weight)
    source
  ≡ zero
uniformWeightsIgnoreCentredDefect weight source =
  solve
    ( weight
    ∷ deltaHH source ∷ deltaLH source ∷ deltaHL source
    ∷ deltaCC source ∷ deltaCom source
    ∷ [])

centredFiveSourceProbeClosed : Bool
centredFiveSourceProbeClosed = true

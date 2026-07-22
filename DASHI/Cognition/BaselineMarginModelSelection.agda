module DASHI.Cognition.BaselineMarginModelSelection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

import DASHI.Cognition.CognitiveObservableDistributions as Distribution

------------------------------------------------------------------------
-- Positive-margin inversion on a finite dataset.
--
-- observed = baseline + beta * resonance - control
-- therefore
-- baselineEstimate = control + observed - beta * resonance.
--
-- Nat subtraction is intentional: these data are the positive-margin lane.
-- Negative/collapsed observations remain represented by SignedMargin in the
-- master system and require a two-sided calibration rather than this solver.
------------------------------------------------------------------------

record MarginDatum : Set where
  constructor marginDatum
  field
    controlLoad : Nat
    resonanceDrive : Nat
    observedPositiveMargin : Nat

open MarginDatum public

baselineEstimate : Nat → MarginDatum → Nat
baselineEstimate beta datum =
  (controlLoad datum + observedPositiveMargin datum)
  - (beta * resonanceDrive datum)

mapEstimate : Nat → List MarginDatum → List Nat
mapEstimate beta [] = []
mapEstimate beta (datum ∷ data) =
  baselineEstimate beta datum ∷ mapEstimate beta data

inferredBaselineDistribution :
  Nat → List MarginDatum → Distribution.FiniteNatDistribution
inferredBaselineDistribution beta data =
  Distribution.fromSamples (mapEstimate beta data)

------------------------------------------------------------------------
-- MDL cost for a common-baseline model.
-- The first inferred baseline is the reference parameter; remaining values
-- are residual-coded by absolute deviation.  beta itself costs unary length.
------------------------------------------------------------------------

absDiff : Nat → Nat → Nat
absDiff zero n = n
absDiff (suc m) zero = suc m
absDiff (suc m) (suc n) = absDiff m n

residualFrom : Nat → List Nat → Nat
residualFrom reference [] = 0
residualFrom reference (x ∷ xs) =
  absDiff reference x + residualFrom reference xs

baselineResidualCost : List Nat → Nat
baselineResidualCost [] = 0
baselineResidualCost (reference ∷ rest) = residualFrom reference rest

betaCode : Nat → Nat
betaCode zero = 0
betaCode (suc beta) = suc (suc beta)

modelCode : Nat → List MarginDatum → Nat
modelCode beta data =
  betaCode beta + baselineResidualCost (mapEstimate beta data)

lessNat : Nat → Nat → Bool
lessNat zero zero = false
lessNat zero (suc _) = true
lessNat (suc _) zero = false
lessNat (suc m) (suc n) = lessNat m n

couplingImprovesMDL : Nat → List MarginDatum → Bool
couplingImprovesMDL beta data =
  lessNat (modelCode beta data) (modelCode 0 data)

------------------------------------------------------------------------
-- Small exact condition family.
-- A true common baseline 10 is distorted under the scalar-only inversion
-- whenever resonance contributes 3 units.  The beta=3 model reconstructs the
-- tight distribution [10,10,10], while beta=0 gives [10,13,13].
------------------------------------------------------------------------

coupledDataset : List MarginDatum
coupledDataset =
  marginDatum 2 0 8
  ∷ marginDatum 5 1 8
  ∷ marginDatum 8 1 5
  ∷ []

nullBaselineEstimates : mapEstimate 0 coupledDataset ≡ 10 ∷ 13 ∷ 13 ∷ []
nullBaselineEstimates = refl

coupledBaselineEstimates : mapEstimate 3 coupledDataset ≡ 10 ∷ 10 ∷ 10 ∷ []
coupledBaselineEstimates = refl

nullModelCodeIsSix : modelCode 0 coupledDataset ≡ 6
nullModelCodeIsSix = refl

coupledModelCodeIsFive : modelCode 3 coupledDataset ≡ 5
coupledModelCodeIsFive = refl

couplingWinsThisFiniteDataset :
  couplingImprovesMDL 3 coupledDataset ≡ true
couplingWinsThisFiniteDataset = refl

------------------------------------------------------------------------
-- Control-only fixture.  With no resonance variation, the scalar model
-- already reconstructs a point-mass baseline and the extra beta code loses.
------------------------------------------------------------------------

scalarDataset : List MarginDatum
scalarDataset =
  marginDatum 2 0 8
  ∷ marginDatum 5 0 5
  ∷ marginDatum 8 0 2
  ∷ []

scalarBaselineEstimates : mapEstimate 0 scalarDataset ≡ 10 ∷ 10 ∷ 10 ∷ []
scalarBaselineEstimates = refl

extraCouplingDoesNotImproveScalarDataset :
  couplingImprovesMDL 3 scalarDataset ≡ false
extraCouplingDoesNotImproveScalarDataset = refl

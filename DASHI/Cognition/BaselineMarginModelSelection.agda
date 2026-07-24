module DASHI.Cognition.BaselineMarginModelSelection where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_)

import DASHI.Cognition.CognitiveObservableDistributions as Distribution

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
  ∸ (beta * resonanceDrive datum)

mapEstimate : Nat → List MarginDatum → List Nat
mapEstimate beta [] = []
mapEstimate beta (datum ∷ rest) =
  baselineEstimate beta datum ∷ mapEstimate beta rest

inferredBaselineDistribution :
  Nat → List MarginDatum → Distribution.FiniteNatDistribution
inferredBaselineDistribution beta rest =
  Distribution.fromSamples (mapEstimate beta rest)

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
betaCode (suc beta) = suc (suc (suc beta))

modelCode : Nat → List MarginDatum → Nat
modelCode beta rest =
  betaCode beta + baselineResidualCost (mapEstimate beta rest)

lessNat : Nat → Nat → Bool
lessNat zero zero = false
lessNat zero (suc _) = true
lessNat (suc _) zero = false
lessNat (suc m) (suc n) = lessNat m n

couplingImprovesMDL : Nat → List MarginDatum → Bool
couplingImprovesMDL beta rest =
  lessNat (modelCode beta rest) (modelCode 0 rest)

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

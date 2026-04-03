module Ontology.Hecke.Layer2FiniteSearch where

open import Ontology.Hecke.CurrentSaturatedPredictedPairComparisons
  using
    ( FirstPairCorrelationSeparates
    ; FirstPairSectorSeparates
    ; FirstPairTriadPackageSeparates
    ; PredictedLayer2ProofOrder
    ; SecondPairCorrelationSeparates
    ; SecondPairSectorSeparates
    ; SecondPairTriadPackageSeparates
    ; ThirdPairCorrelationSeparates
    ; ThirdPairSectorSeparates
    ; ThirdPairTriadPackageSeparates
    ; predictedLayer2ProofOrder
    )

------------------------------------------------------------------------
-- Thin fixed-domain Layer 2 search packaging.
--
-- This module deliberately does not introduce a new invariant. It only
-- packages the already-landed Layer 2 proof order as a finite bounded search:
--
--   sector -> package -> correlation
--
-- on the three predicted current saturated pairs. The intended reading is
-- close to proposal/replay/promote:
-- bounded search surfaces first, then promotion only after an actual
-- separating or exhaustion theorem lands.

record PairComparisonPlan : Set₁ where
  field
    sectorTarget : Set
    packageTarget : Set
    correlationTarget : Set

open PairComparisonPlan public

firstPairPlan : PairComparisonPlan
firstPairPlan = record
  { sectorTarget = FirstPairSectorSeparates
  ; packageTarget = FirstPairTriadPackageSeparates
  ; correlationTarget = FirstPairCorrelationSeparates
  }

secondPairPlan : PairComparisonPlan
secondPairPlan = record
  { sectorTarget = SecondPairSectorSeparates
  ; packageTarget = SecondPairTriadPackageSeparates
  ; correlationTarget = SecondPairCorrelationSeparates
  }

thirdPairPlan : PairComparisonPlan
thirdPairPlan = record
  { sectorTarget = ThirdPairSectorSeparates
  ; packageTarget = ThirdPairTriadPackageSeparates
  ; correlationTarget = ThirdPairCorrelationSeparates
  }

record FiniteLayer2Search : Set₁ where
  field
    predictedProofOrder : PredictedLayer2ProofOrder
    firstPair : PairComparisonPlan
    secondPair : PairComparisonPlan
    thirdPair : PairComparisonPlan

open FiniteLayer2Search public

finiteLayer2Search : FiniteLayer2Search
finiteLayer2Search = record
  { predictedProofOrder = predictedLayer2ProofOrder
  ; firstPair = firstPairPlan
  ; secondPair = secondPairPlan
  ; thirdPair = thirdPairPlan
  }

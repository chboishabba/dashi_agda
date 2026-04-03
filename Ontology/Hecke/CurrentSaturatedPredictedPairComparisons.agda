module Ontology.Hecke.CurrentSaturatedPredictedPairComparisons where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedBalancedComposed
    ; saturatedBalancedCycle
    ; saturatedDenseComposed
    ; saturatedFullSupportCascade
    ; saturatedSupportCascade
    )
open import Ontology.Hecke.CurrentSaturatedSectorHistogramComputations
  using
    ( sector0HistAt
    ; sector1HistAt
    ; sector2HistAt
    ; sectorHistogramsAt
    )
open import Ontology.Hecke.TriadSectorCorrelationRefinement
  using (currentSaturatedSectorCorrelationAt)

------------------------------------------------------------------------
-- Fixed-domain predicted pair targets for Layer 2.
--
-- The current saturated branch is already fully normalized at the coarse
-- level, so the next proof step should stay on this finite scope and test
-- the most asymmetric current pairs first.

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

  _⊎_ : Set → Set → Set

------------------------------------------------------------------------
-- Predicted first pair order.

firstPredictedLeft : CurrentSaturatedGenerator
firstPredictedLeft = saturatedBalancedCycle

firstPredictedRight : CurrentSaturatedGenerator
firstPredictedRight = saturatedSupportCascade

secondPredictedLeft : CurrentSaturatedGenerator
secondPredictedLeft = saturatedBalancedComposed

secondPredictedRight : CurrentSaturatedGenerator
secondPredictedRight = saturatedSupportCascade

thirdPredictedLeft : CurrentSaturatedGenerator
thirdPredictedLeft = saturatedDenseComposed

thirdPredictedRight : CurrentSaturatedGenerator
thirdPredictedRight = saturatedFullSupportCascade

------------------------------------------------------------------------
-- Sector-by-sector comparison targets.

FirstPairSectorSeparates : Set
FirstPairSectorSeparates =
    sector0HistAt firstPredictedLeft ≢ sector0HistAt firstPredictedRight
  ⊎ sector1HistAt firstPredictedLeft ≢ sector1HistAt firstPredictedRight
  ⊎ sector2HistAt firstPredictedLeft ≢ sector2HistAt firstPredictedRight

SecondPairSectorSeparates : Set
SecondPairSectorSeparates =
    sector0HistAt secondPredictedLeft ≢ sector0HistAt secondPredictedRight
  ⊎ sector1HistAt secondPredictedLeft ≢ sector1HistAt secondPredictedRight
  ⊎ sector2HistAt secondPredictedLeft ≢ sector2HistAt secondPredictedRight

ThirdPairSectorSeparates : Set
ThirdPairSectorSeparates =
    sector0HistAt thirdPredictedLeft ≢ sector0HistAt thirdPredictedRight
  ⊎ sector1HistAt thirdPredictedLeft ≢ sector1HistAt thirdPredictedRight
  ⊎ sector2HistAt thirdPredictedLeft ≢ sector2HistAt thirdPredictedRight

------------------------------------------------------------------------
-- Whole-package comparison targets.

FirstPairTriadPackageSeparates : Set
FirstPairTriadPackageSeparates =
  sectorHistogramsAt firstPredictedLeft ≢ sectorHistogramsAt firstPredictedRight

SecondPairTriadPackageSeparates : Set
SecondPairTriadPackageSeparates =
  sectorHistogramsAt secondPredictedLeft ≢ sectorHistogramsAt secondPredictedRight

ThirdPairTriadPackageSeparates : Set
ThirdPairTriadPackageSeparates =
  sectorHistogramsAt thirdPredictedLeft ≢ sectorHistogramsAt thirdPredictedRight

------------------------------------------------------------------------
-- Correlation fallback comparison targets.

FirstPairCorrelationSeparates : Set
FirstPairCorrelationSeparates =
  currentSaturatedSectorCorrelationAt firstPredictedLeft
    ≢
  currentSaturatedSectorCorrelationAt firstPredictedRight

SecondPairCorrelationSeparates : Set
SecondPairCorrelationSeparates =
  currentSaturatedSectorCorrelationAt secondPredictedLeft
    ≢
  currentSaturatedSectorCorrelationAt secondPredictedRight

ThirdPairCorrelationSeparates : Set
ThirdPairCorrelationSeparates =
  currentSaturatedSectorCorrelationAt thirdPredictedLeft
    ≢
  currentSaturatedSectorCorrelationAt thirdPredictedRight

------------------------------------------------------------------------
-- Proof-order packaging.

record PredictedLayer2ProofOrder : Set₁ where
  field
    firstSectorTarget : Set
    secondSectorTarget : Set
    thirdSectorTarget : Set
    firstPackageTarget : Set
    secondPackageTarget : Set
    thirdPackageTarget : Set
    firstCorrelationTarget : Set
    secondCorrelationTarget : Set
    thirdCorrelationTarget : Set

open PredictedLayer2ProofOrder public

predictedLayer2ProofOrder : PredictedLayer2ProofOrder
predictedLayer2ProofOrder = record
  { firstSectorTarget = FirstPairSectorSeparates
  ; secondSectorTarget = SecondPairSectorSeparates
  ; thirdSectorTarget = ThirdPairSectorSeparates
  ; firstPackageTarget = FirstPairTriadPackageSeparates
  ; secondPackageTarget = SecondPairTriadPackageSeparates
  ; thirdPackageTarget = ThirdPairTriadPackageSeparates
  ; firstCorrelationTarget = FirstPairCorrelationSeparates
  ; secondCorrelationTarget = SecondPairCorrelationSeparates
  ; thirdCorrelationTarget = ThirdPairCorrelationSeparates
  }

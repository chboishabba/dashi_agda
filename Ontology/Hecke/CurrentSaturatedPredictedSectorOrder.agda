module Ontology.Hecke.CurrentSaturatedPredictedSectorOrder where

open import Agda.Builtin.Equality using (_≡_)

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
    )
open import Ontology.Hecke.DefectOrbitSummaryRefinement
  using (DefectHistogram)
open import Ontology.Hecke.TriadSectorDirectedCorrelationRefinement
  using
    ( DirectedTriadCorrelationSummary
    ; currentSaturatedDirectedTriadCorrelationAt
    )

------------------------------------------------------------------------
-- The finite Layer 2 speedrun order as data.
--
-- This module does not assert that the predictions are true.  It records the
-- order in which the existing finite computations should be discharged, while
-- keeping the prediction separate from the resulting theorem.

data PredictedPair : Set where
  balancedCycle-supportCascade : PredictedPair
  balancedComposed-supportCascade : PredictedPair
  denseComposed-fullSupportCascade : PredictedPair

data Sector : Set where
  sector0 : Sector
  sector1 : Sector
  sector2 : Sector

leftAt : PredictedPair → CurrentSaturatedGenerator
leftAt balancedCycle-supportCascade = saturatedBalancedCycle
leftAt balancedComposed-supportCascade = saturatedBalancedComposed
leftAt denseComposed-fullSupportCascade = saturatedDenseComposed

rightAt : PredictedPair → CurrentSaturatedGenerator
rightAt balancedCycle-supportCascade = saturatedSupportCascade
rightAt balancedComposed-supportCascade = saturatedSupportCascade
rightAt denseComposed-fullSupportCascade = saturatedFullSupportCascade

firstSector : PredictedPair → Sector
firstSector balancedCycle-supportCascade = sector1
firstSector balancedComposed-supportCascade = sector1
firstSector denseComposed-fullSupportCascade = sector0

secondSector : PredictedPair → Sector
secondSector balancedCycle-supportCascade = sector0
secondSector balancedComposed-supportCascade = sector2
secondSector denseComposed-fullSupportCascade = sector1

thirdSector : PredictedPair → Sector
thirdSector balancedCycle-supportCascade = sector2
thirdSector balancedComposed-supportCascade = sector0
thirdSector denseComposed-fullSupportCascade = sector2

histogramAt : CurrentSaturatedGenerator → Sector → DefectHistogram
histogramAt c sector0 = sector0HistAt c
histogramAt c sector1 = sector1HistAt c
histogramAt c sector2 = sector2HistAt c

postulate
  ⊥ : Set

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

firstSectorSeparates : PredictedPair → Set
firstSectorSeparates p =
  histogramAt (leftAt p) (firstSector p)
    ≢
  histogramAt (rightAt p) (firstSector p)

secondSectorSeparates : PredictedPair → Set
secondSectorSeparates p =
  histogramAt (leftAt p) (secondSector p)
    ≢
  histogramAt (rightAt p) (secondSector p)

thirdSectorSeparates : PredictedPair → Set
thirdSectorSeparates p =
  histogramAt (leftAt p) (thirdSector p)
    ≢
  histogramAt (rightAt p) (thirdSector p)

directedCorrelationSeparates : PredictedPair → Set
directedCorrelationSeparates p =
  currentSaturatedDirectedTriadCorrelationAt (leftAt p)
    ≢
  currentSaturatedDirectedTriadCorrelationAt (rightAt p)

record PredictedPairDischargeOrder (p : PredictedPair) : Set₁ where
  field
    firstSectorTarget : Set
    secondSectorTarget : Set
    thirdSectorTarget : Set
    directedCorrelationTarget : Set

open PredictedPairDischargeOrder public

pairDischargeOrder :
  (p : PredictedPair) → PredictedPairDischargeOrder p
pairDischargeOrder p = record
  { firstSectorTarget = firstSectorSeparates p
  ; secondSectorTarget = secondSectorSeparates p
  ; thirdSectorTarget = thirdSectorSeparates p
  ; directedCorrelationTarget = directedCorrelationSeparates p
  }

------------------------------------------------------------------------
-- Concrete first targets, named for direct use in long-compute modules.

balancedCycle-supportCascade-firstTarget : Set
balancedCycle-supportCascade-firstTarget =
  firstSectorSeparates balancedCycle-supportCascade

balancedComposed-supportCascade-firstTarget : Set
balancedComposed-supportCascade-firstTarget =
  firstSectorSeparates balancedComposed-supportCascade

denseComposed-fullSupportCascade-firstTarget : Set
denseComposed-fullSupportCascade-firstTarget =
  firstSectorSeparates denseComposed-fullSupportCascade

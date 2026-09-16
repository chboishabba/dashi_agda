module DASHI.Cognition.RecursiveFibreTowerGateSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Topology.TetrationalGateField as Gate
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- RECURSIVE FIBRE / TETRATION GATE SEPARATION
--
-- Two independent finite constructions happen to agree on the first triadic
-- tetration counts: TetrationalGateField.TowerDimension and
-- RecursiveFibreTower.predicateLevelSizeRecurrence.  That numerical agreement
-- is retained as a consistency check only.  It does not identify the carriers,
-- and it does not identify hidden phase refinement with opening a new literal
-- function-space tower level.
------------------------------------------------------------------------

triadicHeightZeroCardinalityAgrees :
  Gate.TowerDimension 3 0 ≡ Tower.predicateLevelSizeRecurrence 0
triadicHeightZeroCardinalityAgrees =
  trans Gate.triadicTowerHeight0 (sym Tower.triadicTetrationZero)

triadicHeightOneCardinalityAgrees :
  Gate.TowerDimension 3 1 ≡ Tower.predicateLevelSizeRecurrence 1
triadicHeightOneCardinalityAgrees =
  trans Gate.triadicTowerHeight1 (sym Tower.triadicTetrationOne)

triadicHeightTwoCardinalityAgrees :
  Gate.TowerDimension 3 2 ≡ Tower.predicateLevelSizeRecurrence 2
triadicHeightTwoCardinalityAgrees =
  trans Gate.triadicTowerHeight2 (sym Tower.triadicTetrationTwo)

phaseRefinementPreservesBaseObservation :
  (level : Nat) →
  (phase : Phase.Phase3) →
  Tower.observeBase (Tower.phaseVariant level phase) ≡ BT.zero
phaseRefinementPreservesBaseObservation = Tower.allPhaseVariantsRemainZero

towerOpeningIsNotWithinChartRefinement :
  Gate.openTowerLevel ≡ Gate.refineWithinChart → ⊥
towerOpeningIsNotWithinChartRefinement ()

towerOpeningIsNotFibreDimensionIncrease :
  Gate.openTowerLevel ≡ Gate.increaseFibreDimension → ⊥
towerOpeningIsNotFibreDimensionIncrease ()

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data MatchingCardinalityIdentifiesCarriers : Set where

data HiddenPhaseRefinementIsLiteralFunctionSpaceTetration : Set where

data FibreDimensionIncreaseIsTowerOpening : Set where

matchingCardinalityDoesNotIdentifyCarriers :
  MatchingCardinalityIdentifiesCarriers → ⊥
matchingCardinalityDoesNotIdentifyCarriers ()

hiddenPhaseRefinementDoesNotBecomeLiteralFunctionSpaceTetration :
  HiddenPhaseRefinementIsLiteralFunctionSpaceTetration → ⊥
hiddenPhaseRefinementDoesNotBecomeLiteralFunctionSpaceTetration ()

fibreDimensionIncreaseDoesNotBecomeTowerOpening :
  FibreDimensionIncreaseIsTowerOpening → ⊥
fibreDimensionIncreaseDoesNotBecomeTowerOpening ()

record RecursiveFibreTowerGateBoundary : Set where
  constructor recursive-fibre-tower-gate-boundary
  field
    finiteTriadicCountsAgreeAtZeroOneTwo : Bool
    recursivePhaseFibreAddsHiddenPhase : Bool
    recursivePhaseRefinementPreservesBaseObservable : Bool
    predicateTowerIsLiteralTernaryFunctionSpace : Bool
    matchingCardinalityIdentifiesCarrier : Bool
    matchingCardinalityIdentifiesCarrierIsFalse :
      matchingCardinalityIdentifiesCarrier ≡ false
    hiddenPhaseRefinementEqualsLiteralTetration : Bool
    hiddenPhaseRefinementEqualsLiteralTetrationIsFalse :
      hiddenPhaseRefinementEqualsLiteralTetration ≡ false
    fibreDimensionIncreaseEqualsTowerOpening : Bool
    fibreDimensionIncreaseEqualsTowerOpeningIsFalse :
      fibreDimensionIncreaseEqualsTowerOpening ≡ false
    boundaryNote : String

open RecursiveFibreTowerGateBoundary public

canonicalRecursiveFibreTowerGateBoundary : RecursiveFibreTowerGateBoundary
canonicalRecursiveFibreTowerGateBoundary =
  recursive-fibre-tower-gate-boundary
    true
    true
    true
    true
    false refl
    false refl
    false refl
    "The gate-field and predicate-tower cardinality recurrences agree on the first triadic heights, but equality of counts does not identify their carriers. Hidden phase refinement preserves the lower observable and remains distinct from fibre-dimension increase and from opening a new literal function-space tower level."

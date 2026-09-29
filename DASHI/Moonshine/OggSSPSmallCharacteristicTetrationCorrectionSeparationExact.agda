module DASHI.Moonshine.OggSSPSmallCharacteristicTetrationCorrectionSeparationExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC WILD CORRECTIONS / TETRATION: TYPED SEPARATION
--
-- EXTERNAL ATTRIBUTION:
-- Duncan--Swisher supplies the monstrous-exponent arithmetic (p > 3
-- formula, with exceptional continuation values at p=2 and p=3).
-- Kobin--Zureick-Brown supplies the wild modular-stack context; neither
-- source proves a tetrational Monster correction.
--
-- REPOSITORY PROVENANCE:
-- The self-indexing recurrence is imported from DASHI's
-- SelfIndexingHyperfabricTetrationExact and SelfIndexedParetoHyperfabric-
-- TetrationExact. The 3^9 carrier comparison is from
-- Monster369NDimParetoTetrationBridgeExact.
-- The raw wild-different obstruction is owned by WildDifferentNoGoExact.
--
-- NEW DASHI RESULT:
-- A tetrational tower opening, one more tensor/product layer, and a
-- small-characteristic correction are three DIFFERENT typed operations.
-- Neither the 9-axis level-one tower nor its 19683 ternary profiles are
-- the literal exceptional residual counts 10 and 2.
--
-- A future arithmetic explanation needs a source-specific valuation map,
-- a proof that geometric corrections contribute under that map, and a
-- policy for which fibre histories may be forgotten. Merely matching the
-- count of orbits at one tower level is NOT that proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Self
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Pareto
import DASHI.Cognition.RecursiveFibreTowerGateSeparationExact as Gate
import DASHI.Topology.TetrationalGateField as GateField
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as MonsterTower
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as Wild
import DASHI.Moonshine.OggSSPSmallCharacteristicWildDifferentNoGoExact as Different
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Import exact recurrence, rather than defining a competing tower.
------------------------------------------------------------------------

towerLevelOneAxes : Self.selfIndexedSiteCount 1 ≡ 9
towerLevelOneAxes = Self.selfIndexedLevelOneHasNineSites

towerLevelTwoAxes :
  Self.selfIndexedSiteCount 2 ≡ 9 * 9 * 9 * 9 * 9 * 9 * 9 * 9 * 9
towerLevelTwoAxes = refl

towerLevelOneProfiles :
  Pareto.ternaryObjectiveProfileCount 1 ≡ 19683
towerLevelOneProfiles = Pareto.levelOneTernaryProfileCountIs19683

towerMatchesExisting369ProfileCount :
  Pareto.ternaryObjectiveProfileCount 1
  ≡ MonsterTower.base369ProfileCount
towerMatchesExisting369ProfileCount =
  Pareto.levelOneTernaryProfilesMatchBase369FabricCount

------------------------------------------------------------------------
-- 2. Concrete failed identifications, not hypothetical false flags.
------------------------------------------------------------------------

nineAxesAreNotP2Residual :
  Self.selfIndexedSiteCount 1
  ≡ Wild.wildGeometricSectorCount Wild.primeTwo ->
  ⊥
nineAxesAreNotP2Residual ()

nineAxesAreNotP3Residual :
  Self.selfIndexedSiteCount 1
  ≡ Wild.wildGeometricSectorCount Wild.primeThree ->
  ⊥
nineAxesAreNotP3Residual ()

ternaryProfilesAreNotP2Residual :
  Pareto.ternaryObjectiveProfileCount 1
  ≡ Wild.wildGeometricSectorCount Wild.primeTwo ->
  ⊥
ternaryProfilesAreNotP2Residual ()

ternaryProfilesAreNotP3Residual :
  Pareto.ternaryObjectiveProfileCount 1
  ≡ Wild.wildGeometricSectorCount Wild.primeThree ->
  ⊥
ternaryProfilesAreNotP3Residual ()

------------------------------------------------------------------------
-- 3. The gate semantics does not conflate refinement with tower opening.
------------------------------------------------------------------------

refinementIsNotTowerOpening :
  GateField.refineWithinChart ≡ GateField.openTowerLevel -> ⊥
refinementIsNotTowerOpening = Gate.towerOpeningIsNotWithinChartRefinement

------------------------------------------------------------------------
-- 4. Keep arithmetic correction, wild different, and tower depth apart.
------------------------------------------------------------------------

data CorrectionConstructionKind : Set where
  additiveMonsterCorrection : CorrectionConstructionKind
  geometricOrbitClassification : CorrectionConstructionKind
  stackWildDifferent : CorrectionConstructionKind
  localFibreRefinement : CorrectionConstructionKind
  literalFunctionSpaceTowerOpening : CorrectionConstructionKind

kindOfWildCorrection : CorrectionConstructionKind
kindOfWildCorrection = additiveMonsterCorrection

kindOfTetration : CorrectionConstructionKind
kindOfTetration = literalFunctionSpaceTowerOpening

wildCorrectionIsNotTowerOpening :
  kindOfWildCorrection ≡ kindOfTetration -> ⊥
wildCorrectionIsNotTowerOpening ()

differentP2DoesNotEqualCorrection :
  Different.p2WildDifferentCoefficient
  ≡ Wild.wildGeometricSectorCount Wild.primeTwo -> ⊥
differentP2DoesNotEqualCorrection =
  Different.p2WildDifferentIsNotMonsterResidual

differentP3DoesNotEqualCorrection :
  Different.p3WildDifferentCoefficient
  ≡ Wild.wildGeometricSectorCount Wild.primeThree -> ⊥
differentP3DoesNotEqualCorrection =
  Different.p3WildDifferentIsNotMonsterResidual

------------------------------------------------------------------------
-- 5. Promotion obligation for a future TETRATION -> VALUATION mechanism.
--
-- This contract cannot be inhabited merely from the two numerical equalities:
-- it requires an actual source-indexed tower observable, a correction
-- contribution at each exceptional prime, and an external authority witness.
-- We deliberately provide NO inhabitant of this stronger contract.
------------------------------------------------------------------------

data ExternalTetrationalMonsterValuationIdentification : Set where

record TetrationToMonsterValuationMechanism : Set₁ where
  field
    towerHeightAt : Wild.SmallCharacteristicPrime -> Nat
    towerObservable :
      (p : Wild.SmallCharacteristicPrime) ->
      Self.SelfIndexedCarrier (towerHeightAt p) -> Nat

    selectedTowerState :
      (p : Wild.SmallCharacteristicPrime) ->
      Self.SelfIndexedCarrier (towerHeightAt p)

    contributionAt : Wild.SmallCharacteristicPrime -> Nat

    contributionComputedFromTower :
      (p : Wild.SmallCharacteristicPrime) ->
      contributionAt p ≡
        towerObservable p (selectedTowerState p)

    contributionEqualsResidual :
      (p : Wild.SmallCharacteristicPrime) ->
      contributionAt p ≡ Wild.wildGeometricSectorCount p

    identifiedWithClassicalMonsterValuation :
      ExternalTetrationalMonsterValuationIdentification

------------------------------------------------------------------------
-- 6. Machine-checkable provenance and claim boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

unpaidMechanismClaimOrigin : Attribution.ClaimOrigin
unpaidMechanismClaimOrigin = Attribution.openRecognitionConjecture

record SmallCharacteristicTetrationCorrectionBoundary : Set where
  constructor small-characteristic-tetration-correction-boundary
  field
    selfIndexedTowerRecurrenceReused : Bool
    levelOneNineAxisProfileMatchPaid : Bool
    towerGateDistinctFromRefinement : Bool
    nineAxisCardinalityEqualsP2Residual : Bool
    nineAxisCardinalityEqualsP3Residual : Bool
    firstLevelProfilesEqualP2Residual : Bool
    firstLevelProfilesEqualP3Residual : Bool
    rawDifferentEqualsResidual : Bool
    sourceSpecificTetrationValuationMechanismPaid : Bool
    sourcesCreditedWithDASHITetrationCorrection : Bool

canonicalSmallCharacteristicTetrationCorrectionBoundary :
  SmallCharacteristicTetrationCorrectionBoundary
canonicalSmallCharacteristicTetrationCorrectionBoundary =
  small-characteristic-tetration-correction-boundary
    true true true false false false false false false false

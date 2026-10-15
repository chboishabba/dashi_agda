module DASHI.Biology.IITTernaryLatticeStateSpaceScalingExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Tower
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

------------------------------------------------------------------------
-- SITE COUNT, LOCAL-CARRIER COUNT, CONFIGURATION COUNT
--
-- These quantities are easy to conflate and are kept definitionally separate.
--
--   one 3x3x3 ternary geometric cube = 27 local points/states;
--   three such 27-state factors       = 27^3 = 3^9 = 19683 states;
--   one 3x3 ternary face as 9 sites  = 3^9 = 19683 configurations;
--   one 3x3x3 lattice as 27 ternary sites = 3^27 configurations.
--
-- The equality 27^3 = 3^9 is therefore only a cardinality coincidence between
-- two different factorisations.  It does not identify their causal/gluing
-- semantics.  The self-indexing tower is yet another recursion: 9 ↑↑ n.
------------------------------------------------------------------------

faceSiteCount : Nat
faceSiteCount = 9

cubeSiteCount : Nat
cubeSiteCount = 27

faceConfigurationCount : Nat
faceConfigurationCount = Hyper.ternaryLatticeCount faceSiteCount

cubeConfigurationCount : Nat
cubeConfigurationCount = Hyper.ternaryLatticeCount cubeSiteCount

threeTwentySevenStateFactorCount : Nat
threeTwentySevenStateFactorCount = Geometry.hyperformalStateCount

faceConfigurationCountIs19683 : faceConfigurationCount ≡ 19683
faceConfigurationCountIs19683 = refl

threeFactorCountIs19683 : threeTwentySevenStateFactorCount ≡ 19683
threeFactorCountIs19683 = Geometry.hyperformalStateCountIs19683

faceConfigurationsEqualThreeFactorStates :
  faceConfigurationCount ≡ threeTwentySevenStateFactorCount
faceConfigurationsEqualThreeFactorStates = refl

cubeConfigurationCountIs7625597484987 :
  cubeConfigurationCount ≡ 7625597484987
cubeConfigurationCountIs7625597484987 = refl

cubeConfigurationsAreNotThreeFactorStates :
  cubeConfigurationCount ≡ threeTwentySevenStateFactorCount → ⊥
cubeConfigurationsAreNotThreeFactorStates ()

------------------------------------------------------------------------
-- TETRATION BOUNDARY
------------------------------------------------------------------------

selfIndexedLevelTwoCount : Nat
selfIndexedLevelTwoCount = Tower.selfIndexedSiteCount 2

selfIndexedLevelTwoCountIsNineToNine :
  selfIndexedLevelTwoCount ≡ Hyper.powNat 9 9
selfIndexedLevelTwoCountIsNineToNine = Tower.selfIndexedLevelTwoHasNineToNineSites

faceConfigurationsAreNotSelfIndexedLevelTwo :
  faceConfigurationCount ≡ selfIndexedLevelTwoCount → ⊥
faceConfigurationsAreNotSelfIndexedLevelTwo ()

------------------------------------------------------------------------
-- WOLFRAM / MULTIWAY BOUNDARY
--
-- Equal visible endpoints can retain distinct path residuals.  Hence state
-- count or visible endpoint count cannot by itself specify the causal/path
-- object presented to an IIT consumer.
------------------------------------------------------------------------

wolframMultiwayResidualReceipt :
  Natural.pathResidual (Natural.executeMultiway Natural.leftThenRight) ≡ 1
  ×
  Natural.pathResidual (Natural.executeMultiway Natural.rightThenLeft) ≡ 2
wolframMultiwayResidualReceipt = Natural.multiwayPathsRetainDifferentResiduals

record TernaryLatticeStateSpaceScalingBoundary : Set where
  constructor ternaryLatticeStateSpaceScalingBoundary
  field
    geometricCubeHasTwentySevenLocalPoints : Bool
    threeTwentySevenStateFactorsHave19683States : Bool
    nineTernarySitesHave19683Configurations : Bool
    twentySevenTernarySitesHave7625597484987Configurations : Bool
    equal19683CardinalityIdentifiesFactorisation : Bool
    ordinaryConfigurationGrowthIsTetration : Bool
    selfIndexingTowerIsOrdinaryProductGrowth : Bool
    equalVisibleEndpointErasesWolframPathResidual : Bool
    carrierCardinalityAloneDefinesIITDynamics : Bool

open TernaryLatticeStateSpaceScalingBoundary public

canonicalTernaryLatticeStateSpaceScalingBoundary :
  TernaryLatticeStateSpaceScalingBoundary
canonicalTernaryLatticeStateSpaceScalingBoundary =
  ternaryLatticeStateSpaceScalingBoundary
    true true true true
    false false false false false

sameCardinalityDoesNotIdentifyFactorisation :
  equal19683CardinalityIdentifiesFactorisation
    canonicalTernaryLatticeStateSpaceScalingBoundary ≡ false
sameCardinalityDoesNotIdentifyFactorisation = refl

ordinaryStateSpaceGrowthIsNotSelfIndexingTetration :
  ordinaryConfigurationGrowthIsTetration
    canonicalTernaryLatticeStateSpaceScalingBoundary ≡ false
ordinaryStateSpaceGrowthIsNotSelfIndexingTetration = refl

visibleEndpointDoesNotErasePathResidual :
  equalVisibleEndpointErasesWolframPathResidual
    canonicalTernaryLatticeStateSpaceScalingBoundary ≡ false
visibleEndpointDoesNotErasePathResidual = refl

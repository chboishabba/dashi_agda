module DASHI.Biology.SSPHyperfibreSymmetryTowerExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as SelfIndexing

------------------------------------------------------------------------
-- The fifteen SSP lanes index a family of increasingly typed hyperfibres.
-- Each lane has its own state carrier, symmetry carrier, action, 3/6/9
-- resolution, path type, transport, and residual.  Numerical prime value is
-- only the arithmetic coordinate used by FRACTRAN; it is not the definition
-- of the associated geometry or symmetry.

record SSPHyperfibreAtlas : Set₁ where
  constructor sspHyperfibreAtlas
  field
    Fibre : SSP.SSPPrime → Set
    Symmetry : SSP.SSPPrime → Set
    Residual : SSP.SSPPrime → Set
    Path : SSP.SSPPrime → SSP.SSPPrime → Set

    act :
      (lane : SSP.SSPPrime) →
      Symmetry lane → Fibre lane → Fibre lane

    resolution : SSP.SSPPrime → SelfIndexing.FabricResolution

    transport :
      {source target : SSP.SSPPrime} →
      Path source target → Fibre source → Fibre target

    residualAfter :
      {source target : SSP.SSPPrime} →
      Path source target → Fibre source → Residual target

    declaredComplexity : SSP.SSPPrime → Nat
    complexityCertificate :
      (lane : SSP.SSPPrime) →
      declaredComplexity lane ≡ SSP.sspComplexityRank lane

open SSPHyperfibreAtlas public

------------------------------------------------------------------------
-- A complete finite witness with a shared balanced carrier.  The generic
-- atlas permits heterogeneous fibres; this witness is intentionally small.

data LaneState : Set where
  negativeLaneState : LaneState
  mediatedLaneState : LaneState
  positiveLaneState : LaneState

laneOrientationAction : SSP.FibreOrientation → LaneState → LaneState
laneOrientationAction SSP.inverseOrientation negativeLaneState = positiveLaneState
laneOrientationAction SSP.inverseOrientation mediatedLaneState = mediatedLaneState
laneOrientationAction SSP.inverseOrientation positiveLaneState = negativeLaneState
laneOrientationAction SSP.mediatedOrientation state = state
laneOrientationAction SSP.forwardOrientation state = state

data LanePath : SSP.SSPPrime → SSP.SSPPrime → Set where
  identityLanePath :
    (lane : SSP.SSPPrime) → LanePath lane lane
  forwardLanePath :
    (source target : SSP.SSPPrime) → LanePath source target
  inverseLanePath :
    (source target : SSP.SSPPrime) → LanePath source target

transportLaneState :
  {source target : SSP.SSPPrime} →
  LanePath source target → LaneState → LaneState
transportLaneState (identityLanePath lane) state = state
transportLaneState (forwardLanePath source target) state = state
transportLaneState (inverseLanePath source target) state =
  laneOrientationAction SSP.inverseOrientation state

pathResidual :
  {source target : SSP.SSPPrime} →
  LanePath source target → LaneState → SSP.FibreOrientation
pathResidual (identityLanePath lane) state = SSP.mediatedOrientation
pathResidual (forwardLanePath source target) state = SSP.forwardOrientation
pathResidual (inverseLanePath source target) state = SSP.inverseOrientation

resolutionByRank : SSP.SSPPrime → SelfIndexing.FabricResolution
resolutionByRank SSP.ssp2 = SelfIndexing.resolution3
resolutionByRank SSP.ssp3 = SelfIndexing.resolution3
resolutionByRank SSP.ssp5 = SelfIndexing.resolution3
resolutionByRank SSP.ssp7 = SelfIndexing.resolution3
resolutionByRank SSP.ssp11 = SelfIndexing.resolution3
resolutionByRank SSP.ssp13 = SelfIndexing.resolution6
resolutionByRank SSP.ssp17 = SelfIndexing.resolution6
resolutionByRank SSP.ssp19 = SelfIndexing.resolution6
resolutionByRank SSP.ssp23 = SelfIndexing.resolution6
resolutionByRank SSP.ssp29 = SelfIndexing.resolution6
resolutionByRank SSP.ssp31 = SelfIndexing.resolution9
resolutionByRank SSP.ssp41 = SelfIndexing.resolution9
resolutionByRank SSP.ssp47 = SelfIndexing.resolution9
resolutionByRank SSP.ssp59 = SelfIndexing.resolution9
resolutionByRank SSP.ssp71 = SelfIndexing.resolution9

canonicalSSPHyperfibreAtlas : SSPHyperfibreAtlas
canonicalSSPHyperfibreAtlas =
  sspHyperfibreAtlas
    (λ lane → LaneState)
    (λ lane → SSP.FibreOrientation)
    (λ lane → SSP.FibreOrientation)
    LanePath
    (λ lane → laneOrientationAction)
    resolutionByRank
    transportLaneState
    pathResidual
    SSP.sspComplexityRank
    (λ lane → refl)

------------------------------------------------------------------------
-- Exact examples of 3/6/9 decomposition and signed/inverse transport.

smallestLaneUsesResolutionThree :
  resolution canonicalSSPHyperfibreAtlas SSP.ssp2
  ≡ SelfIndexing.resolution3
smallestLaneUsesResolutionThree = refl

middleLaneUsesResolutionSix :
  resolution canonicalSSPHyperfibreAtlas SSP.ssp19
  ≡ SelfIndexing.resolution6
middleLaneUsesResolutionSix = refl

largestLaneUsesResolutionNine :
  resolution canonicalSSPHyperfibreAtlas SSP.ssp71
  ≡ SelfIndexing.resolution9
largestLaneUsesResolutionNine = refl

inverseTransportReversesPolarity :
  transport canonicalSSPHyperfibreAtlas
    (inverseLanePath SSP.ssp59 SSP.ssp7)
    positiveLaneState
  ≡ negativeLaneState
inverseTransportReversesPolarity = refl

forwardTransportPreservesVisibleLaneState :
  transport canonicalSSPHyperfibreAtlas
    (forwardLanePath SSP.ssp47 SSP.ssp59)
    positiveLaneState
  ≡ positiveLaneState
forwardTransportPreservesVisibleLaneState = refl

inversePathRetainsInverseResidual :
  residualAfter canonicalSSPHyperfibreAtlas
    (inverseLanePath SSP.ssp59 SSP.ssp7)
    positiveLaneState
  ≡ SSP.inverseOrientation
inversePathRetainsInverseResidual = refl

record SSPHyperfibreTowerBoundary : Set where
  constructor sspHyperfibreTowerBoundary
  field
    increasingPrimeValueProvesIncreasingPhysicalComplexity : Bool
    increasingPrimeValueProvesIncreasingPhysicalComplexityIsFalse :
      increasingPrimeValueProvesIncreasingPhysicalComplexity ≡ false

    allFifteenFibresMustHaveTheSameCarrier : Bool
    allFifteenFibresMustHaveTheSameCarrierIsFalse :
      allFifteenFibresMustHaveTheSameCarrier ≡ false

    inverseTransportErasesItsPathResidual : Bool
    inverseTransportErasesItsPathResidualIsFalse :
      inverseTransportErasesItsPathResidual ≡ false

    sspLanesCanIndexHeterogeneousSymmetryFibres : Bool
    sspLanesCanIndexHeterogeneousSymmetryFibresIsTrue :
      sspLanesCanIndexHeterogeneousSymmetryFibres ≡ true

open SSPHyperfibreTowerBoundary public

canonicalSSPHyperfibreTowerBoundary : SSPHyperfibreTowerBoundary
canonicalSSPHyperfibreTowerBoundary =
  sspHyperfibreTowerBoundary false refl false refl false refl true refl

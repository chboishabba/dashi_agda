module DASHI.Physics.Closure.SSPPrimeLane369DepthPhaseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Foundations.SSPPrimeLaneSymmetryProfile as Symmetry
import DASHI.Foundations.StageAtlasZeroToEleven as StageAtlas
import DASHI.Physics.Closure.SSPPrimeLane369PhaseBridge as PB
import DASHI.TrackedPrimes as Tracked

------------------------------------------------------------------------
-- Depth-aware 3/6/9 bridge.
--
-- This bridge keeps the three seams explicit:
--   * the tracked prime lane,
--   * the depth-indexed refinement address,
--   * the phase bridge for the same prime lane,
--   * the stage reading extracted from the depth coordinate.

record SSPPrimeLane369DepthPhaseBridge : Set where
  constructor mkSSPPrimeLane369DepthPhaseBridge
  field
    primeLane : Tracked.SSP
    depth : Nat
    depthAddress : Ref.Lane369Address depth
    refinement : Ref.SSPPrimeLane369Refinement depth
    phaseBridge : PB.SSPPrimeLane369PhaseBridge
    stageCoordinate : StageAtlas.StageAtlasZeroToEleven
    stageReading : StageAtlas.StageAtlasTopologicalReading
    depthAddressMatches : Ref.address refinement ≡ depthAddress
    primeLaneMatchesRefinement : Ref.primeLane refinement ≡ primeLane
    phaseBridgeMatchesPrimeLane : PB.primeIdentity phaseBridge ≡ primeLane
    stageCoordinateMatchesDepth :
      stageCoordinate ≡ Symmetry.stageCoordinateFromNatModulo12 depth
    stageReadingMatchesCoordinate :
      stageReading ≡ StageAtlas.topological-reading-of stageCoordinate

open SSPPrimeLane369DepthPhaseBridge public

primeLane369DepthPhaseBridge :
  ∀ {d : Nat} →
  Ref.SSPPrimeLane369Refinement d →
  SSPPrimeLane369DepthPhaseBridge
primeLane369DepthPhaseBridge {d} refinement = record
  { primeLane = Ref.primeLane refinement
  ; depth = d
  ; depthAddress = Ref.address refinement
  ; refinement = refinement
  ; phaseBridge = PB.primeLane369PhaseBridge (Ref.primeLane refinement)
  ; stageCoordinate = Symmetry.stageCoordinateFromNatModulo12 d
  ; stageReading = StageAtlas.topological-reading-of
      (Symmetry.stageCoordinateFromNatModulo12 d)
  ; depthAddressMatches = refl
  ; primeLaneMatchesRefinement = refl
  ; phaseBridgeMatchesPrimeLane = refl
  ; stageCoordinateMatchesDepth = refl
  ; stageReadingMatchesCoordinate = refl
  }

canonicalRootDepthPhaseBridge :
  SSPPrimeLane369DepthPhaseBridge
canonicalRootDepthPhaseBridge =
  primeLane369DepthPhaseBridge Ref.canonicalRootLane369Refinement

canonicalThreeSixNineDepthPhaseBridge :
  SSPPrimeLane369DepthPhaseBridge
canonicalThreeSixNineDepthPhaseBridge =
  primeLane369DepthPhaseBridge Ref.canonicalThreeSixNineLane369Refinement

canonicalRootDepthIsZero :
  depth canonicalRootDepthPhaseBridge ≡ zero
canonicalRootDepthIsZero = refl

canonicalThreeSixNineDepthIsThree :
  depth canonicalThreeSixNineDepthPhaseBridge ≡ suc (suc (suc zero))
canonicalThreeSixNineDepthIsThree = refl

canonicalRootPrimeLaneIsP3 :
  primeLane canonicalRootDepthPhaseBridge ≡ Tracked.p3
canonicalRootPrimeLaneIsP3 = refl

canonicalThreeSixNinePrimeLaneIsP3 :
  primeLane canonicalThreeSixNineDepthPhaseBridge ≡ Tracked.p3
canonicalThreeSixNinePrimeLaneIsP3 = refl

canonicalRootDepthAddressIsRoot :
  depthAddress canonicalRootDepthPhaseBridge ≡ Ref.root
canonicalRootDepthAddressIsRoot = refl

canonicalThreeSixNineDepthAddressIsCanonical :
  depthAddress canonicalThreeSixNineDepthPhaseBridge
  ≡ Ref.canonicalThreeSixNineAddress
canonicalThreeSixNineDepthAddressIsCanonical = refl

canonicalRootStageCoordinateIsAtlas0 :
  stageCoordinate canonicalRootDepthPhaseBridge ≡ StageAtlas.atlas-0
canonicalRootStageCoordinateIsAtlas0 = refl

canonicalThreeSixNineStageCoordinateIsAtlas3 :
  stageCoordinate canonicalThreeSixNineDepthPhaseBridge ≡ StageAtlas.atlas-3
canonicalThreeSixNineStageCoordinateIsAtlas3 = refl

canonicalRootStageReadingIsAtlas0 :
  stageReading canonicalRootDepthPhaseBridge
  ≡ StageAtlas.topological-reading-of StageAtlas.atlas-0
canonicalRootStageReadingIsAtlas0 = refl

canonicalThreeSixNineStageReadingIsAtlas3 :
  stageReading canonicalThreeSixNineDepthPhaseBridge
  ≡ StageAtlas.topological-reading-of StageAtlas.atlas-3
canonicalThreeSixNineStageReadingIsAtlas3 = refl

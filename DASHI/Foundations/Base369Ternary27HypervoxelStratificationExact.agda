module DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact where

------------------------------------------------------------------------
-- 3x3x3 TERNARY HYPERVOXEL STRATIFICATION
--
-- A point is classified by how many coordinates lie on the outer levels
-- {-1,+1} rather than the central level 0:
--
--   0 outer coordinates : 1 centre
--   1 outer coordinate  : 6 face-centres
--   2 outer coordinates : 12 edge-centres
--   3 outer coordinates : 8 corners
--
-- Hence 1 + 6 + 12 + 8 = 27.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

------------------------------------------------------------------------
-- 1. Outer-support pattern.
------------------------------------------------------------------------

data SupportBit : Set where
  centralBit outerBit : SupportBit

supportBit : SSP.SSPTrit → SupportBit
supportBit SSP.sspNegOne = outerBit
supportBit SSP.sspZero = centralBit
supportBit SSP.sspPosOne = outerBit

record SupportPattern3 : Set where
  constructor supportPattern3
  field sx sy sz : SupportBit
open SupportPattern3 public

supportPattern : Geometry.Ternary27Point → SupportPattern3
supportPattern p =
  supportPattern3
    (supportBit (Geometry.x p))
    (supportBit (Geometry.y p))
    (supportBit (Geometry.z p))

------------------------------------------------------------------------
-- 2. Centre / face-centre / edge-centre / corner strata.
------------------------------------------------------------------------

data VoxelStratum : Set where
  centreStratum
  faceCentreStratum
  edgeCentreStratum
  cornerStratum
  : VoxelStratum

patternStratum : SupportPattern3 → VoxelStratum
patternStratum (supportPattern3 centralBit centralBit centralBit) = centreStratum
patternStratum (supportPattern3 outerBit centralBit centralBit) = faceCentreStratum
patternStratum (supportPattern3 centralBit outerBit centralBit) = faceCentreStratum
patternStratum (supportPattern3 centralBit centralBit outerBit) = faceCentreStratum
patternStratum (supportPattern3 outerBit outerBit centralBit) = edgeCentreStratum
patternStratum (supportPattern3 outerBit centralBit outerBit) = edgeCentreStratum
patternStratum (supportPattern3 centralBit outerBit outerBit) = edgeCentreStratum
patternStratum (supportPattern3 outerBit outerBit outerBit) = cornerStratum

voxelStratum : Geometry.Ternary27Point → VoxelStratum
voxelStratum p = patternStratum (supportPattern p)

originIsCentre : voxelStratum Geometry.origin ≡ centreStratum
originIsCentre = refl

positiveXFaceCentre : Geometry.Ternary27Point
positiveXFaceCentre =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

positiveXFaceCentreIsFaceCentre :
  voxelStratum positiveXFaceCentre ≡ faceCentreStratum
positiveXFaceCentreIsFaceCentre = refl

positiveXYEdgeCentre : Geometry.Ternary27Point
positiveXYEdgeCentre =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero

positiveXYEdgeCentreIsEdgeCentre :
  voxelStratum positiveXYEdgeCentre ≡ edgeCentreStratum
positiveXYEdgeCentreIsEdgeCentre = refl

negativeCornerIsCorner :
  voxelStratum Geometry.negativeCorner ≡ cornerStratum
negativeCornerIsCorner = refl

positiveCornerIsCorner :
  voxelStratum Geometry.positiveCorner ≡ cornerStratum
positiveCornerIsCorner = refl

------------------------------------------------------------------------
-- 3. Exact finite counts of the four geometric strata.
------------------------------------------------------------------------

centreCount : Nat
centreCount = 1

faceCentreCount : Nat
faceCentreCount = 6

edgeCentreCount : Nat
edgeCentreCount = 12

cornerCount : Nat
cornerCount = 8

stratifiedStateCount : Nat
stratifiedStateCount = centreCount + faceCentreCount + edgeCentreCount + cornerCount

stratifiedStateCountIs27 : stratifiedStateCount ≡ 27
stratifiedStateCountIs27 = refl

stratifiedCountAgreesWithHypervoxel :
  stratifiedStateCount ≡ Geometry.hypervoxelStateCount
stratifiedCountAgreesWithHypervoxel = refl

------------------------------------------------------------------------
-- 4. Grid degree by stratum for the ordinary 3x3x3 nearest-neighbour graph.
-- These are geometric degree values: centre 6, face-centre 5, edge-centre 4,
-- corner 3.  The adjacency relation itself is owned by the geometry module.
------------------------------------------------------------------------

gridDegree : VoxelStratum → Nat
gridDegree centreStratum = 6
gridDegree faceCentreStratum = 5
gridDegree edgeCentreStratum = 4
gridDegree cornerStratum = 3

originDegreeIs6 : gridDegree (voxelStratum Geometry.origin) ≡ 6
originDegreeIs6 = refl

cornerDegreeIs3 : gridDegree (voxelStratum Geometry.positiveCorner) ≡ 3
cornerDegreeIs3 = refl

------------------------------------------------------------------------
-- 5. Hyperformal product stratum: each 19683-state fabric point has one
-- stratum in each of its three 27-cube factors.
------------------------------------------------------------------------

record FabricStratum3 : Set where
  constructor fabricStratum3
  field
    interactionStratum : VoxelStratum
    appraisalAStratum : VoxelStratum
    appraisalBStratum : VoxelStratum
open FabricStratum3 public

fabricStratum : Geometry.TernaryHyperformalPoint → FabricStratum3
fabricStratum p =
  fabricStratum3
    (voxelStratum (Geometry.interactionVoxel p))
    (voxelStratum (Geometry.appraisalAVoxel p))
    (voxelStratum (Geometry.appraisalBVoxel p))

fabricOriginStratum :
  fabricStratum Geometry.fabricOrigin ≡
  fabricStratum3 centreStratum centreStratum centreStratum
fabricOriginStratum = refl

------------------------------------------------------------------------
-- 6. Boundary receipt.
------------------------------------------------------------------------

record Ternary27StratificationBoundary : Set where
  constructor ternary27StratificationBoundary
  field
    centreCountIsOne : Bool
    faceCentreCountIsSix : Bool
    edgeCentreCountIsTwelve : Bool
    cornerCountIsEight : Bool
    strataSumToTwentySeven : Bool
    centreGridDegreeIsSix : Bool
    cornerGridDegreeIsThree : Bool
    stratumIsSemanticMeaning : Bool

canonicalTernary27StratificationBoundary : Ternary27StratificationBoundary
canonicalTernary27StratificationBoundary =
  ternary27StratificationBoundary true true true true true true true false

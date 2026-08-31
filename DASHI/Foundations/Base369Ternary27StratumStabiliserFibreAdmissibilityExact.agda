module DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact where

------------------------------------------------------------------------
-- STRATUM / STABILISER / FIBRE-ADMISSIBILITY CROSS-POLLINATION
--
-- The geometric centre/face/edge/corner stratum is NOT fine enough to recover
-- the coordinate-permutation stabiliser.  This matters if one wants to reduce
-- or select admissible fibre sectors by symmetry: the exact base point, not
-- merely its coarse stratum, must remain available.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Symmetry
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Two edge-centre points have the same coarse geometric stratum but
--    different stabilisers.
------------------------------------------------------------------------

sameSignEdge : Geometry.Ternary27Point
sameSignEdge =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero

oppositeSignEdge : Geometry.Ternary27Point
oppositeSignEdge =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero

sameSignEdgeIsEdgeCentre :
  Stratification.voxelStratum sameSignEdge ≡ Stratification.edgeCentreStratum
sameSignEdgeIsEdgeCentre = refl

oppositeSignEdgeIsEdgeCentre :
  Stratification.voxelStratum oppositeSignEdge ≡ Stratification.edgeCentreStratum
oppositeSignEdgeIsEdgeCentre = refl

sameSignEdgeHasS2 :
  Spectral.voxelStabiliser sameSignEdge ≡ Symmetry.pairStabiliserS2
sameSignEdgeHasS2 = refl

oppositeSignEdgeHasTrivialStabiliser :
  Spectral.voxelStabiliser oppositeSignEdge ≡ Symmetry.trivialStabiliser
oppositeSignEdgeHasTrivialStabiliser = refl

------------------------------------------------------------------------
-- 2. The same phenomenon already occurs within the corner stratum.
------------------------------------------------------------------------

mixedSignCorner : Geometry.Ternary27Point
mixedSignCorner =
  Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne

mixedSignCornerIsCorner :
  Stratification.voxelStratum mixedSignCorner ≡ Stratification.cornerStratum
mixedSignCornerIsCorner = refl

positiveCornerHasS3 :
  Spectral.voxelStabiliser Geometry.positiveCorner ≡ Symmetry.fullStabiliserS3
positiveCornerHasS3 = refl

mixedSignCornerHasS2 :
  Spectral.voxelStabiliser mixedSignCorner ≡ Symmetry.pairStabiliserS2
mixedSignCornerHasS2 = refl

------------------------------------------------------------------------
-- 3. Symmetry-qualified fibre sector class.
--
-- This is intentionally only an admissibility/reduction code.  It does not
-- claim an actual representation decomposition or orbit cardinality theorem.
------------------------------------------------------------------------

data FibreSectorClass : Set where
  fullySymmetricSector
  pairSymmetricSector
  genericSector
  : FibreSectorClass

sectorClassOfStabiliser : Symmetry.StabiliserType → FibreSectorClass
sectorClassOfStabiliser Symmetry.fullStabiliserS3 = fullySymmetricSector
sectorClassOfStabiliser Symmetry.pairStabiliserS2 = pairSymmetricSector
sectorClassOfStabiliser Symmetry.trivialStabiliser = genericSector

sectorClassAtBase : Geometry.Ternary27Point → FibreSectorClass
sectorClassAtBase p = sectorClassOfStabiliser (Spectral.voxelStabiliser p)

sameSignEdgeSector : sectorClassAtBase sameSignEdge ≡ pairSymmetricSector
sameSignEdgeSector = refl

oppositeSignEdgeSector : sectorClassAtBase oppositeSignEdge ≡ genericSector
oppositeSignEdgeSector = refl

positiveCornerSector : sectorClassAtBase Geometry.positiveCorner ≡ fullySymmetricSector
positiveCornerSector = refl

mixedSignCornerSector : sectorClassAtBase mixedSignCorner ≡ pairSymmetricSector
mixedSignCornerSector = refl

------------------------------------------------------------------------
-- 4. Non-factorability: coarse stratum cannot recover the symmetry-qualified
--    fibre sector class.
------------------------------------------------------------------------

data EdgeFineState : Set where
  edgeSameSign edgeOppositeSign : EdgeFineState

edgePoint : EdgeFineState → Geometry.Ternary27Point
edgePoint edgeSameSign = sameSignEdge
edgePoint edgeOppositeSign = oppositeSignEdge

edgeStratumSurface : EdgeFineState → Stratification.VoxelStratum
edgeStratumSurface s = Stratification.voxelStratum (edgePoint s)

edgeSectorSurface : EdgeFineState → FibreSectorClass
edgeSectorSurface s = sectorClassAtBase (edgePoint s)

edgeStratumCannotRecoverSectorClass :
  INF.FactorsThrough edgeStratumSurface edgeSectorSurface → ⊥
edgeStratumCannotRecoverSectorClass =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness edgeSameSign edgeOppositeSign refl (λ ()))

data CornerFineState : Set where
  cornerUniform cornerMixed : CornerFineState

cornerPoint : CornerFineState → Geometry.Ternary27Point
cornerPoint cornerUniform = Geometry.positiveCorner
cornerPoint cornerMixed = mixedSignCorner

cornerStratumSurface : CornerFineState → Stratification.VoxelStratum
cornerStratumSurface s = Stratification.voxelStratum (cornerPoint s)

cornerSectorSurface : CornerFineState → FibreSectorClass
cornerSectorSurface s = sectorClassAtBase (cornerPoint s)

cornerStratumCannotRecoverSectorClass :
  INF.FactorsThrough cornerStratumSurface cornerSectorSurface → ⊥
cornerStratumCannotRecoverSectorClass =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness cornerUniform cornerMixed refl (λ ()))

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record StratumStabiliserFibreBoundary : Set where
  constructor stratum-stabiliser-fibre-boundary
  field
    exactBaseMaySelectSymmetryQualifiedSector : Bool
    edgeStratumDeterminesStabiliser : Bool
    cornerStratumDeterminesStabiliser : Bool
    coarseStratumDeterminesFibreSectorClass : Bool
    stabiliserCodeIsFullRepresentationDecomposition : Bool
    stabiliserCodeDeterminesOrbitCardinality : Bool

canonicalStratumStabiliserFibreBoundary : StratumStabiliserFibreBoundary
canonicalStratumStabiliserFibreBoundary =
  stratum-stabiliser-fibre-boundary true false false false false false

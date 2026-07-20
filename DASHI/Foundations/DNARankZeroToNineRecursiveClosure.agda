module DASHI.Foundations.DNARankZeroToNineRecursiveClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToEleven as StageAtlas
import DASHI.Geometry.DNAFourAdicSheetLift as Lift

------------------------------------------------------------------------
-- Rank 0..9 DNA structural atlas.
--
-- Rank is geometric/operational arity, not tetration height.  A completed
-- rank-0..9 packet may itself be treated as one cell of a successor packet;
-- that recursive packet closure is the source of the symbolic tower reading.

data DNARankZeroToNine : Set where
  rank0Point : DNARankZeroToNine
  rank1VectorLine : DNARankZeroToNine
  rank2StackedVectorSheet : DNARankZeroToNine
  rank3StackedSheetVoxel : DNARankZeroToNine
  rank4ConvolvedVoxelSupervoxel : DNARankZeroToNine
  rank5SupervoxelField : DNARankZeroToNine
  rank6CoupledFieldBundle : DNARankZeroToNine
  rank7QuotientBasinAtlas : DNARankZeroToNine
  rank8RecursiveClosurePacket : DNARankZeroToNine
  rank9PacketWithinSuccessorSupervoxel : DNARankZeroToNine

rankName : DNARankZeroToNine → String
rankName rank0Point = "point / identity"
rankName rank1VectorLine = "vector / line"
rankName rank2StackedVectorSheet = "stacked vectors / sheet"
rankName rank3StackedSheetVoxel = "stacked sheets / voxel"
rankName rank4ConvolvedVoxelSupervoxel = "convolved voxels / supervoxel"
rankName rank5SupervoxelField = "supervoxel field"
rankName rank6CoupledFieldBundle = "coupled field bundle"
rankName rank7QuotientBasinAtlas = "chemistry quotient-basin atlas"
rankName rank8RecursiveClosurePacket = "recursive closure packet"
rankName rank9PacketWithinSuccessorSupervoxel = "rank packet as successor supervoxel cell"

canonicalDNARanks : List DNARankZeroToNine
canonicalDNARanks =
  rank0Point
  ∷ rank1VectorLine
  ∷ rank2StackedVectorSheet
  ∷ rank3StackedSheetVoxel
  ∷ rank4ConvolvedVoxelSupervoxel
  ∷ rank5SupervoxelField
  ∷ rank6CoupledFieldBundle
  ∷ rank7QuotientBasinAtlas
  ∷ rank8RecursiveClosurePacket
  ∷ rank9PacketWithinSuccessorSupervoxel
  ∷ []

------------------------------------------------------------------------
-- Finite rank packet versus symbolic recursive depth.

data DNAClosureReading : Set where
  finiteRankReading : DNAClosureReading
  finiteFourPowerCarrierReading : DNAClosureReading
  configurationSpaceReading : DNAClosureReading
  recursiveTowerReading : DNAClosureReading
  surrealScaleBookkeepingReading : DNAClosureReading

record DNARecursiveRankPacket : Set where
  constructor mkDNARecursiveRankPacket
  field
    ranks : List DNARankZeroToNine
    localFourAdicLift : Lift.DNAFourAdicLiftReceipt
    packetIsOneSuccessorCell : Bool
    successorPacketMaterialised : Bool
    recursiveDepthHasCanonicalTop : Bool
    rankEqualsTowerHeight : Bool
    surrealReadingIsBookkeepingNotChemistryLaw : Bool

open DNARecursiveRankPacket public

canonicalDNARecursiveRankPacket : DNARecursiveRankPacket
canonicalDNARecursiveRankPacket =
  mkDNARecursiveRankPacket
    canonicalDNARanks
    Lift.canonicalDNAFourAdicLiftReceipt
    true
    false
    false
    false
    true

record DNARankZeroToNineClosureReceipt : Set where
  constructor mkDNARankZeroToNineClosureReceipt
  field
    rankAtlasPresent : Bool
    pointLineSheetVoxelSupervoxelOrderPreserved : Bool
    ranksZeroThroughNineLocallyAvailable : Bool
    packetCanBeNestedAsSuccessorCell : Bool
    tetrationComesFromRecursiveConfigurationClosure : Bool
    tetrationComesFromTensorRankAlone : Bool
    finiteCarrierConfusedWithFullStateSpace : Bool
    existingStageAtlasIsCoordinateAnalogyOnly : Bool
    closureBoundaryHolds : Bool
    closureBoundaryHoldsIsTrue : closureBoundaryHolds ≡ true

open DNARankZeroToNineClosureReceipt public

canonicalDNARankZeroToNineClosureReceipt : DNARankZeroToNineClosureReceipt
canonicalDNARankZeroToNineClosureReceipt =
  mkDNARankZeroToNineClosureReceipt
    true true true true true false false true true refl

existingStageAtlasWitness : StageAtlas.StageAtlasZeroToEleven
existingStageAtlasWitness = StageAtlas.atlas-9

module DASHI.Analysis.NonArchimedeanHadamardTwistedSectorBidiExact where

------------------------------------------------------------------------
-- SOURCE-SPECIFIC BIDI NARROWING FROM THE ACTUAL LEAN REPO
--
-- `CollatzRelMatrix.D'_block_diag` already proves the concrete Hadamard block
-- diagonalization of the directed matrix and places `twistedDirMatrix` in the
-- antisymmetric block.  Therefore reverse proof search must not reopen the
-- entire D_n -> twisted-sector decomposition.
--
-- The live same-object frontier is narrower:
--
--   concrete twistedDirMatrix
--     -> exact character/monomial rechart
--     -> group-label + scalar-action compatibility
--     -> owned period/weight algebra
--     -> owned generic monomial power reduction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude


data BridgeStage : Set where
  directedMatrixToHadamardBlocks : BridgeStage
  twistedSectorExtraction : BridgeStage
  twistedSectorToCharacterMonomial : BridgeStage
  characterOrbitPeriodAndWeight : BridgeStage
  genericMonomialPowerReduction : BridgeStage
  scalarPowerTransportBackToSpatial : BridgeStage


data StageStatus : Set where
  owned : StageStatus
  live : StageStatus
  downstream : StageStatus

stageStatus : BridgeStage → StageStatus
stageStatus directedMatrixToHadamardBlocks = owned
stageStatus twistedSectorExtraction = owned
stageStatus twistedSectorToCharacterMonomial = live
stageStatus characterOrbitPeriodAndWeight = owned
stageStatus genericMonomialPowerReduction = owned
stageStatus scalarPowerTransportBackToSpatial = downstream

hadamardSplitAlreadyOwned :
  stageStatus directedMatrixToHadamardBlocks ≡ owned
hadamardSplitAlreadyOwned = refl

twistedSectorAlreadyOwned :
  stageStatus twistedSectorExtraction ≡ owned
twistedSectorAlreadyOwned = refl

monomializationIsLiveFrontier :
  stageStatus twistedSectorToCharacterMonomial ≡ live
monomializationIsLiveFrontier = refl

record HadamardTwistedSectorBoundary : Set where
  constructor hadamardTwistedSectorBoundary
  field
    rebuildDirectedBlockDiagonalization : Bool
    rebuildTwistedSectorDefinition : Bool
    constructTwistedToCharacterSameObjectWeld : Bool
    reproveGenericMonomialPower : Bool
    preserveConcreteTwistedBlockIdentity : Bool

canonicalHadamardTwistedSectorBoundary : HadamardTwistedSectorBoundary
canonicalHadamardTwistedSectorBoundary =
  hadamardTwistedSectorBoundary
    false
    false
    true
    false
    true

highestAlphaRemainingStages : List BridgeStage
highestAlphaRemainingStages =
  twistedSectorToCharacterMonomial ∷
  scalarPowerTransportBackToSpatial ∷
  []

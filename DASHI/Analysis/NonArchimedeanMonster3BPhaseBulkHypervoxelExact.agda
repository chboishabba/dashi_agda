module DASHI.Analysis.NonArchimedeanMonster3BPhaseBulkHypervoxelExact where

------------------------------------------------------------------------
-- SOURCE-17 DYADIC BULK INSIDE THE MONSTER 3B C3 PHASE HYPERVOXEL
--
-- At source twisted level 17, the finite character carrier has cardinality
-- 2^16 = 65536.  DASHI's existing Monster 3B arithmetic chart decomposes each
-- C3 phase multiplicity around exactly that baseline:
--
--   (65663,65610,65610)
--     = (65536,65536,65536) + (127,74,74).
--
-- This is an exact fibre decomposition of multiplicities, not a claim that the
-- source dyadic operator realizes the Monster representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanMonster3BDyadicCorrespondenceBidiExact as Corr
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as M3B

addPhase :
  M3B.ThreePhaseMultiplicity →
  M3B.ThreePhaseMultiplicity →
  M3B.ThreePhaseMultiplicity
addPhase
  (M3B.threePhaseMultiplicity a0 a1 a2)
  (M3B.threePhaseMultiplicity b0 b1 b2) =
  M3B.threePhaseMultiplicity (a0 + b0) (a1 + b1) (a2 + b2)

source17ReplicatedBulk : M3B.ThreePhaseMultiplicity
source17ReplicatedBulk =
  M3B.threePhaseMultiplicity
    Corr.sourceTwistedCardinalityAt17
    Corr.sourceTwistedCardinalityAt17
    Corr.sourceTwistedCardinalityAt17

monster3BResidualFibre : M3B.ThreePhaseMultiplicity
monster3BResidualFibre =
  M3B.threePhaseMultiplicity
    M3B.invariantDyadicCorrection
    M3B.nontrivialDyadicCorrection
    M3B.nontrivialDyadicCorrection

source17BulkPlusResidualIsMonster3B :
  addPhase source17ReplicatedBulk monster3BResidualFibre
  ≡ M3B.monsterW3B
source17BulkPlusResidualIsMonster3B = refl

source17ReplicatedBulkDimension : Nat
source17ReplicatedBulkDimension =
  M3B.phaseDimension source17ReplicatedBulk

source17ReplicatedBulkDimensionIs196608 :
  source17ReplicatedBulkDimension ≡ 196608
source17ReplicatedBulkDimensionIs196608 = refl

monster3BResidualDimension : Nat
monster3BResidualDimension =
  M3B.phaseDimension monster3BResidualFibre

monster3BResidualDimensionIs275 :
  monster3BResidualDimension ≡ 275
monster3BResidualDimensionIs275 = refl

source17BulkPlusResidualDimensionIsMonsterW :
  source17ReplicatedBulkDimension + monster3BResidualDimension ≡ 196883
source17BulkPlusResidualDimensionIsMonsterW = refl

------------------------------------------------------------------------
-- The C3 character residual lives entirely in the residual fibre because the
-- replicated 65536 bulk is phase-balanced.
------------------------------------------------------------------------

residualCharacterDefectIs53 :
  M3B.zeta monster3BResidualFibre + 53
  ≡ M3B.invariant monster3BResidualFibre
residualCharacterDefectIs53 = refl

record PhaseBulkHypervoxelBoundary : Set where
  constructor phase-bulk-hypervoxel-boundary
  field
    source17BulkReplicatesAcrossC3Phases : Bool
    monsterDifferenceLivesInResidualFibre : Bool
    balancedDyadicBulkContributesC3CharacterDefect : Bool
    residualCarriesCharacterDefect : Bool
    arithmeticBulkDecompositionImpliesRepresentationEmbedding : Bool
    residualDimensionImpliesAlbertOrG2Representation : Bool

canonicalPhaseBulkHypervoxelBoundary : PhaseBulkHypervoxelBoundary
canonicalPhaseBulkHypervoxelBoundary =
  phase-bulk-hypervoxel-boundary
    true
    true
    false
    true
    false
    false

------------------------------------------------------------------------
-- BIDI reading:
--
-- The bulk is already exact.  Any proposed Monster correspondence must explain
-- the residual action/character, not merely reproduce the 2^16 bulk count.
------------------------------------------------------------------------

data ResidualCorrespondenceTarget : Set where
  explain275ResidualDimension : ResidualCorrespondenceTarget
  explain53CharacterDefect : ResidualCorrespondenceTarget
  identifyResidualRepresentation : ResidualCorrespondenceTarget
  intertwineSourceBulkWithMonsterPhaseAction : ResidualCorrespondenceTarget

record ResidualSearchBoundary : Set where
  constructor residual-search-boundary
  field
    bulkCardinalitySearchStillOpen : Bool
    residualCharacterSearchIsLive : Bool
    residualRepresentationSearchIsLive : Bool
    sourceMonsterActionIntertwinerIsLive : Bool

canonicalResidualSearchBoundary : ResidualSearchBoundary
canonicalResidualSearchBoundary =
  residual-search-boundary false true true true

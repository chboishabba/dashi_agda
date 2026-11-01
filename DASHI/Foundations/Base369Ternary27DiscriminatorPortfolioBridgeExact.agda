module DASHI.Foundations.Base369Ternary27DiscriminatorPortfolioBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata

------------------------------------------------------------------------
-- BASE369 / 27-CELL DISCRIMINATOR PORTFOLIO BRIDGE
--
-- One 27-voxel is used as a typed three-axis carrier, not as semantics itself.
-- The full 27^3 = 19683 fabric then carries three distinct experiment views:
-- epistemic, governance/resource, and adaptive-context state.
------------------------------------------------------------------------

data GainLevel : Set where gainLow gainMedium gainHigh : GainLevel
data RelevanceLevel : Set where relevanceLow relevanceConditional relevanceHigh : RelevanceLevel
data SplitLevel : Set where noSplit partialSplit strictSplit : SplitLevel

data CostDesirability : Set where costly balancedCost cheap : CostDesirability
data AuthorityLevel : Set where blocked conditionalAuthority admitted : AuthorityLevel
data PermissionLevel : Set where permissionAbsent permissionConditional permissionPresent : PermissionLevel

data ResolutionLevel : Set where unresolved partlyResolved resolved : ResolutionLevel

gainTrit : GainLevel → Trit.SSPTrit
gainTrit gainLow = Trit.sspNegOne
gainTrit gainMedium = Trit.sspZero
gainTrit gainHigh = Trit.sspPosOne

relevanceTrit : RelevanceLevel → Trit.SSPTrit
relevanceTrit relevanceLow = Trit.sspNegOne
relevanceTrit relevanceConditional = Trit.sspZero
relevanceTrit relevanceHigh = Trit.sspPosOne

splitTrit : SplitLevel → Trit.SSPTrit
splitTrit noSplit = Trit.sspNegOne
splitTrit partialSplit = Trit.sspZero
splitTrit strictSplit = Trit.sspPosOne

costTrit : CostDesirability → Trit.SSPTrit
costTrit costly = Trit.sspNegOne
costTrit balancedCost = Trit.sspZero
costTrit cheap = Trit.sspPosOne

authorityTrit : AuthorityLevel → Trit.SSPTrit
authorityTrit blocked = Trit.sspNegOne
authorityTrit conditionalAuthority = Trit.sspZero
authorityTrit admitted = Trit.sspPosOne

permissionTrit : PermissionLevel → Trit.SSPTrit
permissionTrit permissionAbsent = Trit.sspNegOne
permissionTrit permissionConditional = Trit.sspZero
permissionTrit permissionPresent = Trit.sspPosOne

resolutionTrit : ResolutionLevel → Trit.SSPTrit
resolutionTrit unresolved = Trit.sspNegOne
resolutionTrit partlyResolved = Trit.sspZero
resolutionTrit resolved = Trit.sspPosOne

record EpistemicExperimentVoxel : Set where
  constructor epistemicExperimentVoxel
  field
    gain : GainLevel
    relevance : RelevanceLevel
    splitting : SplitLevel
open EpistemicExperimentVoxel public

record GovernanceExperimentVoxel : Set where
  constructor governanceExperimentVoxel
  field
    costDesirability : CostDesirability
    authority : AuthorityLevel
    permission : PermissionLevel
open GovernanceExperimentVoxel public

record AdaptiveContextVoxel : Set where
  constructor adaptiveContextVoxel
  field
    targetResolution : ResolutionLevel
    pathResolution : ResolutionLevel
    consumerClosure : ResolutionLevel
open AdaptiveContextVoxel public

epistemicPoint : EpistemicExperimentVoxel → Geometry.Ternary27Point
epistemicPoint e = Geometry.ternary27Point
  (gainTrit (gain e))
  (relevanceTrit (relevance e))
  (splitTrit (splitting e))

governancePoint : GovernanceExperimentVoxel → Geometry.Ternary27Point
governancePoint g = Geometry.ternary27Point
  (costTrit (costDesirability g))
  (authorityTrit (authority g))
  (permissionTrit (permission g))

contextPoint : AdaptiveContextVoxel → Geometry.Ternary27Point
contextPoint c = Geometry.ternary27Point
  (resolutionTrit (targetResolution c))
  (resolutionTrit (pathResolution c))
  (resolutionTrit (consumerClosure c))

record DiscriminatorPortfolioFabric : Set where
  constructor discriminatorPortfolioFabric
  field
    epistemic : EpistemicExperimentVoxel
    governance : GovernanceExperimentVoxel
    context : AdaptiveContextVoxel
open DiscriminatorPortfolioFabric public

asHyperformalPoint : DiscriminatorPortfolioFabric → Geometry.TernaryHyperformalPoint
asHyperformalPoint p = Geometry.ternaryHyperformalPoint
  (epistemicPoint (epistemic p))
  (governancePoint (governance p))
  (contextPoint (context p))

canonicalCandidate : DiscriminatorPortfolioFabric
canonicalCandidate = discriminatorPortfolioFabric
  (epistemicExperimentVoxel gainHigh relevanceHigh strictSplit)
  (governanceExperimentVoxel cheap admitted permissionPresent)
  (adaptiveContextVoxel resolved partlyResolved unresolved)

canonicalEpistemicCorner :
  Strata.voxelStratum (Geometry.interactionVoxel (asHyperformalPoint canonicalCandidate))
  ≡ Strata.cornerStratum
canonicalEpistemicCorner = refl

portfolioCarrierCount : Nat
portfolioCarrierCount = Geometry.hyperfabricStateCount

portfolioCarrierCountIs19683 : portfolioCarrierCount ≡ 19683
portfolioCarrierCountIs19683 = Geometry.hyperfabricStateCountIs19683

record Base369DiscriminatorPortfolioBoundary : Set where
  constructor base369DiscriminatorPortfolioBoundary
  field
    oneViewHasTwentySevenCarrierStates : Bool
    threeViewsHaveNineteenThousandSixHundredEightyThreeCarrierStates : Bool
    sameTritAcrossAxesMeansSameSemantics : Bool
    geometricCornerMeansScientificallyOptimal : Bool
    hypervoxelAdjacencyCanRepresentOneCoordinateRevision : Bool
    geometryCreatesAuthority : Bool

canonicalBase369DiscriminatorPortfolioBoundary : Base369DiscriminatorPortfolioBoundary
canonicalBase369DiscriminatorPortfolioBoundary =
  base369DiscriminatorPortfolioBoundary true true false false true false

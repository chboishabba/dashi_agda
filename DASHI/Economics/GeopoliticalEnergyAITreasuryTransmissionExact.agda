module DASHI.Economics.GeopoliticalEnergyAITreasuryTransmissionExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.String using (String)

import DASHI.Economics.GlobalFundingLiquidityRealisationExact as Funding

------------------------------------------------------------------------
-- GEOPOLITICAL / ENERGY / AI / TREASURY TRANSMISSION GRAPH
--
-- This is a typed candidate mechanism, not a political-equivalence theorem and
-- not a claim that any named state controls another actor.  Each edge requires
-- independent empirical admission before systemic promotion.
------------------------------------------------------------------------

data GeopoliticalNode : Set where
  usFiscal : GeopoliticalNode
  treasuryLongEnd : GeopoliticalNode
  dollarFX : GeopoliticalNode
  japanJPYJGB : GeopoliticalNode
  chinaCompute : GeopoliticalNode
  aiInfrastructure : GeopoliticalNode
  hormuz : GeopoliticalNode
  babElMandeb : GeopoliticalNode
  oilMarket : GeopoliticalNode
  goldReserveLiquidity : GeopoliticalNode

data TransmissionKind : Set where
  fundingTransmission : TransmissionKind
  collateralTransmission : TransmissionKind
  fxTransmission : TransmissionKind
  inflationTransmission : TransmissionKind
  termPremiumTransmission : TransmissionKind
  computeCompetitionTransmission : TransmissionKind
  reserveLiquidityTransmission : TransmissionKind

record CandidateEdge : Set where
  constructor candidateEdge
  field
    fromNode : GeopoliticalNode
    toNode : GeopoliticalNode
    kind : TransmissionKind
    empiricallyAdmitted : Bool
    deterministic : Bool

open CandidateEdge public

oilToInflation : CandidateEdge
oilToInflation =
  candidateEdge oilMarket treasuryLongEnd inflationTransmission false false

chinaComputeToAIResidualValue : CandidateEdge
chinaComputeToAIResidualValue =
  candidateEdge chinaCompute aiInfrastructure computeCompetitionTransmission false false

yenToTreasuryFunding : CandidateEdge
yenToTreasuryFunding =
  candidateEdge japanJPYJGB treasuryLongEnd fundingTransmission false false

goldLiquiditySignal : CandidateEdge
goldLiquiditySignal =
  candidateEdge goldReserveLiquidity dollarFX reserveLiquidityTransmission false false

data GeopoliticalAssociationImpliesControlPermission : Set where
data ChokepointStressImpliesOilShockPermission : Set where
data ChineseComputeCompetitionImpliesUSCollapsePermission : Set where
data GoldMovementImpliesDollarCollapsePermission : Set where

associationDoesNotAutoProveControl :
  GeopoliticalAssociationImpliesControlPermission → ⊥
associationDoesNotAutoProveControl ()

chokepointStressDoesNotAutoProveOilShock :
  ChokepointStressImpliesOilShockPermission → ⊥
chokepointStressDoesNotAutoProveOilShock ()

computeCompetitionDoesNotAutoProveUSCollapse :
  ChineseComputeCompetitionImpliesUSCollapsePermission → ⊥
computeCompetitionDoesNotAutoProveUSCollapse ()

goldMovementDoesNotAutoProveDollarCollapse :
  GoldMovementImpliesDollarCollapsePermission → ⊥
goldMovementDoesNotAutoProveDollarCollapse ()

record MultiObjectiveDollarSystem : Set where
  constructor multiObjectiveDollarSystem
  field
    reserveStatus : Trit
    treasuryLiquidity : Trit
    exchangeRateStability : Trit
    domesticFinancingCost : Trit
    inflationControl : Trit
    tradeCompetitiveness : Trit
    objectivesAlwaysCompatible : Bool

open MultiObjectiveDollarSystem public

canonicalObjectivesNeedNotAlign : MultiObjectiveDollarSystem
canonicalObjectivesNeedNotAlign =
  multiObjectiveDollarSystem zer zer zer zer zer zer false

record GoldTopologyBoundary : Set where
  constructor goldTopologyBoundary
  field
    selectiveFinancialChannelRetrenchment : Bool
    physicalGoldChannelStillExists : Bool
    reserveGoldVenueShift : Bool
    provesBlanketPaperGoldBan : Bool
    provesDollarCollapse : Bool

canonicalGoldTopologyBoundary : GoldTopologyBoundary
canonicalGoldTopologyBoundary =
  goldTopologyBoundary true true true false false

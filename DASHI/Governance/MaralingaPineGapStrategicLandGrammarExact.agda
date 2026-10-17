module DASHI.Governance.MaralingaPineGapStrategicLandGrammarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.MontefioreRothschildAustralianGoldSourceAtlasExact as Sources
import DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact as Pine
import DASHI.Governance.AustraliaUSAllianceSovereigntyGenealogyExact as Alliance

------------------------------------------------------------------------
-- MARALINGA / PINE GAP SHARED STRATEGIC-LAND GRAMMAR
--
-- Shared abstraction is deliberately weaker than programme lineage.
------------------------------------------------------------------------

data StrategicTerritorialUseCase : Set where
  maralingaNuclearProvingGround : StrategicTerritorialUseCase
  pineGapJointIntelligenceFacility : StrategicTerritorialUseCase

data SharedDimension : Set where
  indigenousCountryRenderedStrategicSite : SharedDimension
  allianceSecurityPurpose : SharedDimension
  remotenessLogisticsDiscourse : SharedDimension
  landAccessControl : SharedDimension
  humanPresenceLegibility : SharedDimension
  secrecyMeasurementAdministrativeAbstraction : SharedDimension

data CaseSpecificConsequence : Set where
  nuclearTestingAndContamination : CaseSpecificConsequence
  remoteConflictIntelligenceLegibility : CaseSpecificConsequence

pineGapSite : Pine.IntelligenceSite
pineGapSite = Pine.pineGap

pineGapCountry : Pine.CountryCarrier
pineGapCountry = Pine.arrernteCountry

pineGapBoundary : Pine.IntelligenceCircuitBoundary
pineGapBoundary = Pine.canonicalIntelligenceCircuitBoundary

pineGapScale : Pine.IntelligenceScale
pineGapScale = Pine.jointGlobalStrategic

record StrategicCaseReceipt : Set where
  constructor strategic-case-receipt
  field
    case : StrategicTerritorialUseCase
    countryDescription : String
    sourceDescription : String
    sharedDimensions : List SharedDimension
    caseSpecificConsequence : CaseSpecificConsequence
    historicalPaid : Bool
open StrategicCaseReceipt public

maralingaReceipt : StrategicCaseReceipt
maralingaReceipt = strategic-case-receipt
  maralingaNuclearProvingGround
  "Pitjantjatjara and Yankunytjatjara traditional lands / Aboriginal Country"
  "National Archives of Australia Maralinga official-history source"
  (indigenousCountryRenderedStrategicSite ∷ allianceSecurityPurpose ∷ remotenessLogisticsDiscourse ∷ landAccessControl ∷ humanPresenceLegibility ∷ secrecyMeasurementAdministrativeAbstraction ∷ [])
  nuclearTestingAndContamination
  true

pineGapReceipt : StrategicCaseReceipt
pineGapReceipt = strategic-case-receipt
  pineGapJointIntelligenceFacility
  "Arrernte Country"
  "Existing DASHI Pine Gap source/ontology owners"
  (indigenousCountryRenderedStrategicSite ∷ allianceSecurityPurpose ∷ remotenessLogisticsDiscourse ∷ landAccessControl ∷ humanPresenceLegibility ∷ secrecyMeasurementAdministrativeAbstraction ∷ [])
  remoteConflictIntelligenceLegibility
  true

------------------------------------------------------------------------
-- The common grammar pays comparison, not historical descent.
------------------------------------------------------------------------

data SharedStrategicLandGrammarCreatesProgrammeLineage : Set where
data SharedGrammarCreatesSpecificTargetingChain : Set where
data MaralingaContaminationTransfersToPineGap : Set where
data PineGapIntelligenceFunctionTransfersToMaralinga : Set where

sharedStrategicLandGrammarDoesNotCreateProgrammeLineage :
  SharedStrategicLandGrammarCreatesProgrammeLineage → ⊥
sharedStrategicLandGrammarDoesNotCreateProgrammeLineage ()

sharedGrammarDoesNotCreateSpecificTargetingChain : SharedGrammarCreatesSpecificTargetingChain → ⊥
sharedGrammarDoesNotCreateSpecificTargetingChain ()

maralingaContaminationDoesNotTransferToPineGap : MaralingaContaminationTransfersToPineGap → ⊥
maralingaContaminationDoesNotTransferToPineGap ()

pineGapIntelligenceFunctionDoesNotTransferToMaralinga : PineGapIntelligenceFunctionTransfersToMaralinga → ⊥
pineGapIntelligenceFunctionDoesNotTransferToMaralinga ()

record StrategicLandBoundary : Set where
  constructor strategic-land-boundary
  field
    existingPineGapOwnerReused : Bool
    existingAllianceSovereigntyOwnerReused : Bool
    sharedGrammarPaid : Bool
    programmeLineagePaid : Bool
    specificTargetingChainPaid : Bool
    caseSpecificConsequencesCollapsed : Bool
open StrategicLandBoundary public

canonicalStrategicLandBoundary : StrategicLandBoundary
canonicalStrategicLandBoundary = strategic-land-boundary true true true false false false

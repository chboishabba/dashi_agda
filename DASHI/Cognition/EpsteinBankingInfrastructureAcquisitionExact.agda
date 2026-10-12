module DASHI.Cognition.EpsteinBankingInfrastructureAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BANKING / TRANSACTION INFRASTRUCTURE ACQUISITION OWNER
--
-- This owner separates institution, executive, account/transaction,
-- SAR/compliance, regulatory, and civil-settlement surfaces.  Senate or media
-- findings are attributed as such; civil settlements do not create admissions;
-- regulatory findings do not automatically establish criminal liability.
------------------------------------------------------------------------

data BankNode : Set where
  jpmorgan : BankNode
  deutscheBank : BankNode
  bankOfAmerica : BankNode
  bnyMellon : BankNode
  goldmanSachs : BankNode
  hsbc : BankNode

data BankingSurface : Set where
  accountRelationship : BankingSurface
  transactionFlow : BankingSurface
  sarOrAMLReporting : BankingSurface
  executiveRelationship : BankingSurface
  regulatoryFinding : BankingSurface
  civilSettlement : BankingSurface
  congressionalInvestigationFinding : BankingSurface

record BankingReceipt : Set where
  constructor banking-receipt
  field
    institution : BankNode
    surface : BankingSurface
    sourceClass : String
    description : String
    relationEstablished : Bool
    criminalLiabilityEstablishedByThisReceipt : Bool
    admissionEstablishedByThisReceipt : Bool
open BankingReceipt public

jpmorganSettlementReceipt : BankingReceipt
jpmorganSettlementReceipt = banking-receipt
  jpmorgan civilSettlement
  "2023 civil settlement / court record"
  "JPMorgan agreed to a USD 290m settlement of Epstein survivor claims; settlement itself does not constitute an admission of liability."
  true false false

deutscheRegulatoryReceipt : BankingReceipt
deutscheRegulatoryReceipt = banking-receipt
  deutscheBank regulatoryFinding
  "New York Department of Financial Services 2020 consent-order reporting"
  "DFS imposed a USD 150m penalty covering compliance failures including Deutsche Bank's relationship with Epstein."
  true false false

bankOfAmericaSettlementReceipt : BankingReceipt
bankOfAmericaSettlementReceipt = banking-receipt
  bankOfAmerica civilSettlement
  "2026 Reuters / civil settlement"
  "Bank of America agreed to pay USD 72.5m to settle survivor claims while denying wrongdoing; court approval remained required at reporting time."
  true false false

senateJPMorganReceipt : BankingReceipt
senateJPMorganReceipt = banking-receipt
  jpmorgan congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges delayed screening/reporting of Epstein suspicious activity and broader failures that enabled ready access to funds."
  true false false

senateDeutscheReceipt : BankingReceipt
senateDeutscheReceipt = banking-receipt
  deutscheBank congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges delayed/non-timely reporting of substantial suspicious Epstein transactions."
  true false false

senateBOAReceipt : BankingReceipt
senateBOAReceipt = banking-receipt
  bankOfAmerica congressionalInvestigationFinding
  "Senate Finance Committee 2026 follow-the-money report"
  "Senate Finance alleges failures to timely screen/report large transfers including Leon Black->Epstein payments."
  true false false

record FinanceFrontStatus : Set where
  constructor finance-front-status
  field
    senateReportsAtLeast14BQuestionable : Bool
    jpmorganSettlement290m : Bool
    deutscheDFS150mPenalty : Bool
    bankOfAmericaSettlement725m : Bool
    executiveLevelExpansionRequired : Bool
    transactionLevelExpansionRequired : Bool
    sarLevelExpansionRequired : Bool
    bankFrontCurrentlyHighestGlobalAcquisitionValue : Bool
open FinanceFrontStatus public

currentFinanceFrontStatus : FinanceFrontStatus
currentFinanceFrontStatus = finance-front-status
  true true true true true true true true

------------------------------------------------------------------------
-- ATTRIBUTION / PROMOTION FIREWALLS
------------------------------------------------------------------------

data SenateFindingImpliesCriminalConviction : Set where
data SettlementImpliesAdmission : Set where
data RegulatoryFindingImpliesTraffickingParticipation : Set where
data BankRelationshipImpliesExecutiveKnowledge : Set where
data SuspiciousTransactionImpliesUnderlyingCrimeProved : Set where

senateFindingDoesNotCreateConviction : SenateFindingImpliesCriminalConviction → ⊥
senateFindingDoesNotCreateConviction ()

settlementDoesNotCreateAdmission : SettlementImpliesAdmission → ⊥
settlementDoesNotCreateAdmission ()

regulatoryFindingDoesNotCreateTraffickingParticipation :
  RegulatoryFindingImpliesTraffickingParticipation → ⊥
regulatoryFindingDoesNotCreateTraffickingParticipation ()

bankRelationshipDoesNotCreateExecutiveKnowledge : BankRelationshipImpliesExecutiveKnowledge → ⊥
bankRelationshipDoesNotCreateExecutiveKnowledge ()

suspiciousTransactionDoesNotCreateUnderlyingCrimeProof :
  SuspiciousTransactionImpliesUnderlyingCrimeProved → ⊥
suspiciousTransactionDoesNotCreateUnderlyingCrimeProof ()

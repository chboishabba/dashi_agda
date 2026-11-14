module DASHI.Governance.LombardiAustralianColonialFinanceTerminalMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Governance.MontefioreRothschildAustralianGoldSourceAtlasExact as Sources
import DASHI.Governance.MontefioreRothschildAustralianGoldNetworkExact as Gold
import DASHI.Governance.LombardiNarrativeStructureAdapterExact as Narrative
import DASHI.Governance.MaralingaPineGapStrategicLandGrammarExact as Land
import DASHI.Governance.AustralianColonialExtractionNarrativeStructureExact as Extraction
import DASHI.Governance.LombardiBCCIHistoricalFixtureExact as BCCI
import DASHI.Governance.NarrativeStructureEvidenceAdapterExact as Method

------------------------------------------------------------------------
-- TERMINAL MAX-CUT
------------------------------------------------------------------------

record TerminalBoundary : Set where
  constructor terminal-boundary
  field
    sourceAtlasPaid : Bool
    montefioreGoldFiniteNetworkPaid : Bool
    correctedFamilySemanticsPaid : Bool
    identityNoncausalFirewallPaid : Bool
    lombardiCoarseObserverPaid : Bool
    coarseFineCollisionPaid : Bool
    pineGapExistingOwnerReused : Bool
    maralingaPineGapSharedGrammarPaid : Bool
    programmeLineagePaid : Bool
    colonialExtractionCompositionPaid : Bool
    bcciIndependentHistoricalFixturePaid : Bool
    epsteinStyleMethodABIPaid : Bool
    sharedMethodCreatesSharedNetwork : Bool
    graphPathCreatesCausalChain : Bool
    artworkCreatesHistoricalReceipt : Bool
open TerminalBoundary public

canonicalTerminalBoundary : TerminalBoundary
canonicalTerminalBoundary = terminal-boundary
  true true true true true true true true false true true true false false false

------------------------------------------------------------------------
-- Concrete remaining acquisition frontier.
------------------------------------------------------------------------

data AcquisitionDebt : Set where
  exactRothschildAccountBookIdentifiers : AcquisitionDebt
  exactGoldShipmentInsuranceCommissionProfitRecords : AcquisitionDebt
  bankOfAustralasiaNamedTransactionRecords : AcquisitionDebt
  probateEstateAccumulationRecords : AcquisitionDebt
  southAustralianLandFinanceTransactionReceipts : AcquisitionDebt
  maralingaPineGapPersonnelInstitutionalProgrammeContinuity : AcquisitionDebt
  maralingaPineGapSharedAdministrationRecords : AcquisitionDebt
  independentBackingForArtworkOnlyBCCIEdges : AcquisitionDebt

record AcquisitionTarget : Set where
  constructor acquisition-target
  field
    debt : AcquisitionDebt
    priority : Nat
    question : String
    truthValueEncodedByPriority : Bool
open AcquisitionTarget public

canonicalAcquisitionFrontier : List AcquisitionTarget
canonicalAcquisitionFrontier =
  acquisition-target exactRothschildAccountBookIdentifiers 100
    "Acquire exact N. M. Rothschild & Sons correspondence/account-book identifiers for named Australian gold transactions." false
  ∷ acquisition-target exactGoldShipmentInsuranceCommissionProfitRecords 100
    "Acquire same-object shipment, insurance, commission and profit-sharing records for specific consignments." false
  ∷ acquisition-target bankOfAustralasiaNamedTransactionRecords 99
    "Acquire Bank of Australasia records tying named Montefiore actors to specific gold-rush transactions." false
  ∷ acquisition-target probateEstateAccumulationRecords 97
    "Acquire probate/estate records sufficient to trace accumulation without equating inheritance and operating control." false
  ∷ acquisition-target southAustralianLandFinanceTransactionReceipts 96
    "Acquire South Australian colonisation/land-finance receipts linking offices, transactions and counterparties." false
  ∷ acquisition-target maralingaPineGapPersonnelInstitutionalProgrammeContinuity 100
    "Search for direct personnel/institutional/programme continuity between British nuclear-test administration and Pine Gap; keep lineage unpaid absent direct receipts." false
  ∷ acquisition-target maralingaPineGapSharedAdministrationRecords 95
    "Acquire records that support or falsify stronger shared-administration hypotheses across the two strategic-land cases." false
  ∷ acquisition-target independentBackingForArtworkOnlyBCCIEdges 98
    "Independently source any Lombardi/BCCI edge before promoting it beyond artwork representation." false
  ∷ []

record VerificationBoundary : Set where
  constructor verification-boundary
  field
    sourceWritten : Bool
    redFirstContractWritten : Bool
    exactHeadKernelRunObserved : Bool
    ciRequiredForSourceMaxCut : Bool
open VerificationBoundary public

canonicalVerificationBoundary : VerificationBoundary
canonicalVerificationBoundary = verification-boundary true true false false

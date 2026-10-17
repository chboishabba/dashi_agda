module DASHI.Cognition.EpsteinRothschildAgreementContext20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackRothschildTransactionAtlas20261014Exact as Tx

------------------------------------------------------------------------
-- SOUTHERN TRUST / ROTHSCHILD AGREEMENT CONTEXT
--
-- Released 2015 agreements are source-attributed contractual instruments.
-- They establish agreed scope/fees, not independent proof that every described
-- service was performed or that a later wire settled a specific version.
------------------------------------------------------------------------

data AgreementScope : Set where
  riskAnalysis : AgreementScope
  algorithmApplication : AgreementScope
  estatePlanning : AgreementScope
  strategicBusinessMatters : AgreementScope
  outstandingUSMatters : AgreementScope

record AgreementReceipt : Set where
  constructor agreement-receipt
  field
    date : String
    efta : String
    rothParty : String
    southernTrustSignatory : String
    feeUSD : Nat
    scopes : List AgreementScope
    paymentTrigger : String
    executedBySouthernTrust : Bool
    provesServicesPerformed : Bool
    provesSpecificWireSettlement : Bool
open AgreementReceipt public

oct5RiskAlgorithmAgreement : AgreementReceipt
oct5RiskAlgorithmAgreement = agreement-receipt
  "2015-10-05"
  "EFTA00584898 / duplicate lineage"
  "Ariane de Rothschild / Edmond de Rothschild Holding SA"
  "Jeffrey Epstein for Southern Trust Company Inc."
  25000000
  (riskAnalysis ∷ algorithmApplication ∷ outstandingUSMatters ∷ [])
  "USD 25m payable under the instrument's stated US-matters trigger"
  true false false

oct5StrategicBusinessAgreement : AgreementReceipt
oct5StrategicBusinessAgreement = agreement-receipt
  "2015-10-05"
  "EFTA00585615 / duplicate lineage"
  "Edmond de Rothschild (Geneve) SA"
  "Jeffrey Epstein for Southern Trust Company Inc."
  25000000
  (strategicBusinessMatters ∷ [])
  "USD 25m by stated November 2015 deadline"
  true false false

septEstateRiskDraft : AgreementReceipt
septEstateRiskDraft = agreement-receipt
  "2015-09"
  "EFTA00310331"
  "Ariane de Rothschild, family and Edmond de Rothschild Holding SA"
  "Southern Trust / Epstein signature status must be read from exact carrier"
  25000000
  (riskAnalysis ∷ estatePlanning ∷ algorithmApplication ∷ [])
  "tiered/settlement-linked compensation described in released version"
  false false false

allAgreementContexts : List AgreementReceipt
allAgreementContexts =
  oct5RiskAlgorithmAgreement ∷ oct5StrategicBusinessAgreement ∷ septEstateRiskDraft ∷ []

record RothschildContextBoundary : Set where
  constructor rothschild-context-boundary
  field
    agreementsExist : Bool
    agreementsNameSouthernTrust : Bool
    agreementValueApproximatelyMatchesLocatedWires : Bool
    december2015WiresExist : Bool
    contractualContextForWiresPaid : Bool
    exactWireToSpecificAgreementSettlementPaid : Bool
    agreementProvesWorkPerformed : Bool
    agreementOrWireProvesWrongdoing : Bool
open RothschildContextBoundary public

canonicalRothschildContextBoundary : RothschildContextBoundary
canonicalRothschildContextBoundary = rothschild-context-boundary
  true true true true true false false false

data MatchingAmountImpliesSpecificSettlement : Set where
data AgreementImpliesPerformance : Set where
data ContractOrWireImpliesWrongdoing : Set where

matchingAmountDoesNotCreateSpecificSettlement : MatchingAmountImpliesSpecificSettlement → ⊥
matchingAmountDoesNotCreateSpecificSettlement ()

agreementDoesNotCreatePerformance : AgreementImpliesPerformance → ⊥
agreementDoesNotCreatePerformance ()

contractOrWireDoesNotCreateWrongdoing : ContractOrWireImpliesWrongdoing → ⊥
contractOrWireDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Acquisition now targets version resolution and performance evidence.
------------------------------------------------------------------------

data RothschildDebt : Set where
  agreementVersionLineage : RothschildDebt
  wireSettlementInstruction : RothschildDebt
  workProductAndCorrespondence : RothschildDebt
  USMatterResolutionChronology : RothschildDebt
  algorithmWorkSubstance : RothschildDebt

record RothschildAcquisition : Set where
  constructor rothschild-acquisition
  field
    debt : RothschildDebt
    priority : Nat
    question : String
open RothschildAcquisition public

canonicalRothschildAcquisition : List RothschildAcquisition
canonicalRothschildAcquisition =
  rothschild-acquisition wireSettlementInstruction 100
    "Acquire wire instructions, invoices, remittance correspondence or accounting entries tying the December 2015 institutional/personal Rothschild transfers to a particular released agreement version."
  ∷ rothschild-acquisition agreementVersionLineage 99
    "Resolve the multiple September-November 2015 drafts/executed copies into a version graph: party, scope, fee, trigger, signatures and supersession."
  ∷ rothschild-acquisition workProductAndCorrespondence 99
    "Acquire work product and correspondence showing what Southern Trust actually did under the agreements rather than treating contract recitals as performance proof."
  ∷ rothschild-acquisition algorithmWorkSubstance 98
    "Resolve what 'risk analysis' and 'application and use of certain algorithms' meant operationally, including data, models, personnel and outputs."
  ∷ rothschild-acquisition USMatterResolutionChronology 97
    "Join the agreement triggers to the exact US regulatory/DOJ matter chronology without inferring influence over the government outcome."
  ∷ []

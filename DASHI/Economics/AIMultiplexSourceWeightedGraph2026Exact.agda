module DASHI.Economics.AIMultiplexSourceWeightedGraph2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AnthropicProspectusCapitalRecovery2026Exact as Anthropic

------------------------------------------------------------------------
-- SOURCE-WEIGHTED MULTIPLEX GRAPH CARRIER
--
-- This module is the formal counterpart of dashiTRADE's runtime weighted
-- graph.  A named relationship is not admitted to the economic graph merely
-- because two firms appear in the same story: an admitted weighted edge needs
-- a channel, a notional, a source receipt, an observation date and an explicit
-- admission witness.  Proposed / exploratory transactions remain candidates.
------------------------------------------------------------------------

data EdgeAdmissionStatus : Set where
  admittedContractual : EdgeAdmissionStatus
  reportedProposal : EdgeAdmissionStatus
  unresolvedStatus : EdgeAdmissionStatus

record SourceWeightedEconomicEdge : Set where
  constructor sourceWeightedEconomicEdge
  field
    from : String
    to : String
    channel : Capital.FlowChannel
    notionalMillionUSD : Nat
    observationDate : String
    source : Source.AttributedSource
    status : EdgeAdmissionStatus
    sourceWritten : Bool
    sourceWrittenIsTrue : sourceWritten ≡ true

open SourceWeightedEconomicEdge public

record CandidateEconomicEdge : Set where
  constructor candidateEconomicEdge
  field
    from : String
    to : String
    channel : Capital.FlowChannel
    reportedNotionalMillionUSD : Nat
    observationDate : String
    source : Source.AttributedSource
    reasonNotAdmitted : String

open CandidateEconomicEdge public

anthropicBroadcomSupplierFinanceEdge : SourceWeightedEconomicEdge
anthropicBroadcomSupplierFinanceEdge = sourceWeightedEconomicEdge
  "Broadcom"
  "Anthropic"
  Capital.debt
  42000
  "2026-10-01"
  Anthropic.reutersBroadcomLoan2026
  admittedContractual
  true
  refl

anthropicBroadcomCapacityCommitmentEdge : SourceWeightedEconomicEdge
anthropicBroadcomCapacityCommitmentEdge = sourceWeightedEconomicEdge
  "Anthropic"
  "Broadcom"
  Capital.services
  125200
  "2026-10-01"
  Anthropic.reutersBroadcomLoan2026
  admittedContractual
  true
  refl

------------------------------------------------------------------------
-- Coordinate derivation requires receipts, not prose impressions.
------------------------------------------------------------------------

record TerminalConductanceInputCertificate : Set where
  constructor terminalConductanceInputCertificate
  field
    terminalRevenueMillionUSD : Nat
    totalDemandSideInflowMillionUSD : Nat
    terminalRevenueCoverageComplete : Bool
    terminalRevenueCoverageCompleteIsTrue :
      terminalRevenueCoverageComplete ≡ true
    receipt : String

open TerminalConductanceInputCertificate public

record EntanglementInputCertificate : Set where
  constructor entanglementInputCertificate
  field
    totalGraphWeightMillionUSD : Nat
    internalCycleWeightMillionUSD : Nat
    supplierFinancedDemandMillionUSD : Nat
    sourceCoverageComplete : Bool
    sourceCoverageCompleteIsTrue : sourceCoverageComplete ≡ true
    receipt : String

open EntanglementInputCertificate public

record ConcentrationInputCertificate : Set where
  constructor concentrationInputCertificate
  field
    totalRevenueMillionUSD : Nat
    customerRevenueVectorReceipt : String
    sourceCoverageComplete : Bool
    sourceCoverageCompleteIsTrue : sourceCoverageComplete ≡ true

open ConcentrationInputCertificate public

------------------------------------------------------------------------
-- Current max-cut residual: supplier-finance topology is source-written, but
-- terminal independent revenue coverage for the whole connected component is
-- not yet source-complete.  We therefore refuse to manufacture conductance.
------------------------------------------------------------------------

data WeightedGraphResidual : Set where
  terminalRevenueCoverageOpen : WeightedGraphResidual
  customerRevenueVectorOpen : WeightedGraphResidual
  rolloverScheduleOpen : WeightedGraphResidual
  realisedROICVectorOpen : WeightedGraphResidual
  weightedGraphCoordinatesComplete : WeightedGraphResidual

record CurrentWeightedGraphCut : Set where
  constructor currentWeightedGraphCut
  field
    supplierFinanceEdgePresent : Bool
    supplierFinanceEdgePresentIsTrue : supplierFinanceEdgePresent ≡ true
    reciprocalCommitmentEdgePresent : Bool
    reciprocalCommitmentEdgePresentIsTrue : reciprocalCommitmentEdgePresent ≡ true
    terminalCoverageComplete : Bool
    terminalCoverageCompleteIsFalse : terminalCoverageComplete ≡ false
    concentrationCoverageComplete : Bool
    concentrationCoverageCompleteIsFalse : concentrationCoverageComplete ≡ false
    residual : WeightedGraphResidual

open CurrentWeightedGraphCut public

currentOctober2026WeightedGraphCut : CurrentWeightedGraphCut
currentOctober2026WeightedGraphCut = currentWeightedGraphCut
  true refl
  true refl
  false refl
  false refl
  terminalRevenueCoverageOpen

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data FinancingEdgeImpliesRevenuePermission : Set where
data CommitmentEdgeImpliesTerminalCashPermission : Set where
data NamedCounterpartyImpliesConcentrationPermission : Set where
data ProposedTransactionImpliesAdmittedEdgePermission : Set where

financingEdgeDoesNotAutoCreateRevenue :
  FinancingEdgeImpliesRevenuePermission → ⊥
financingEdgeDoesNotAutoCreateRevenue ()

commitmentEdgeDoesNotAutoCreateTerminalCash :
  CommitmentEdgeImpliesTerminalCashPermission → ⊥
commitmentEdgeDoesNotAutoCreateTerminalCash ()

namedCounterpartyDoesNotAutoCloseConcentration :
  NamedCounterpartyImpliesConcentrationPermission → ⊥
namedCounterpartyDoesNotAutoCloseConcentration ()

reportedProposalDoesNotAutoBecomeAdmittedEdge :
  ProposedTransactionImpliesAdmittedEdgePermission → ⊥
reportedProposalDoesNotAutoBecomeAdmittedEdge ()

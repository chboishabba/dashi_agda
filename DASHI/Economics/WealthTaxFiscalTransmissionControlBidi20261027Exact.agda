module DASHI.Economics.WealthTaxFiscalTransmissionControlBidi20261027Exact where

-- Fiscal collection / control transmission finite counterexamples.
-- DASHI-original source-written model 2026-10-27, research direction:
-- Johl Brown; OpenAI ChatGPT assistance. No empirical or kernel claims.
-- The original tax bases and query/fibre owners are imported, not redefined.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_)
open import Data.Empty using (⊥)

import DASHI.Economics.WealthInheritanceVacancyTaxMaxCut20261027Exact as Tax
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- ORIGINAL REGULATORY SOURCE ROLES (NON-PROMOTING)
-- ASIC and AASB texts own their own legal/accounting propositions. These
-- texts motivate the votes/control distinction, not the synthetic 10:1
-- construction or any claim about an actual corporation.
------------------------------------------------------------------------

record ControlSourceReceipt : Set where
  constructor control-source-receipt
  field
    originalAuthor : String
    datedSource : String
    canonicalURL : String
    boundedProposition : String
    nonClaim : String
open ControlSourceReceipt public

asicShareholderRights : ControlSourceReceipt
asicShareholderRights = control-source-receipt
  "Australian Securities and Investments Commission"
  "Shareholder rights and responsibilities; consulted 2026-10-27"
  "https://www.asic.gov.au/for-business-and-companies/companies/company-share-and-shareholder-rules-and-changes/shareholder-rights-and-responsibilities"
  "different share classes may have different voting rights; member votes and majority resolution rules depend on company arrangements"
  "not a claim that majority votes alone settle every kind of company control"

aasb10ControlConditions : ControlSourceReceipt
aasb10ControlConditions = control-source-receipt
  "Australian Accounting Standards Board; AASB 10"
  "Compiled AASB 10; version 2024-12-31"
  "https://www.legislation.gov.au/F2015L01617/2024-12-31/2024-12-31/text/original/epub/OEBPS/document_1/document_1.html"
  "control can depend on contractual rights and relevant activities; majority voting is straightforward only absent other arrangements"
  "not an assertion of the specific financial control of a named real company"

sgxDualClass : ControlSourceReceipt
sgxDualClass = control-source-receipt
  "Singapore Exchange"
  "Equity securities listing rules, Chapter 2; accessed 2026-10-27"
  "https://rulebook.qasgx.com/rulebook/chapter-2-equity-securities"
  "the dual-class listing structure specifies multiple voting class and maximum 10 votes per such share"
  "SGX listing constraints do not automatically govern Australian companies"

------------------------------------------------------------------------
-- A formal tax liability is NOT a cash receipt, and a cash receipt is not
-- administrative expenditure nor a realised social investment.
------------------------------------------------------------------------

record FiscalExecution : Set where
  constructor fiscal-execution
  field
    netWealthAssessed : Nat
    taxPaidCash : Nat
    collectionCostCash : Nat
    appropriatedCareCash : Nat
open FiscalExecution public

assessedLiability : FiscalExecution → Nat
assessedLiability state =
  Tax.hundredPercentWealthExcess 3
    (Tax.owned-net-wealth (netWealthAssessed state))

worldDueUnpaid : FiscalExecution
worldDueUnpaid = fiscal-execution 5 0 1 0

worldDuePaid : FiscalExecution
worldDuePaid = fiscal-execution 5 2 1 0

worldDuePaidSpent : FiscalExecution
worldDuePaidSpent = fiscal-execution 5 2 1 2

worldDuePaidHigherCost : FiscalExecution
worldDuePaidHigherCost = fiscal-execution 5 2 3 0

liabilitySameUnpaidPaid :
  assessedLiability worldDueUnpaid ≡ assessedLiability worldDuePaid
liabilitySameUnpaidPaid = refl

collectionDiffers :
  taxPaidCash worldDueUnpaid ≡ taxPaidCash worldDuePaid → ⊥
collectionDiffers ()

collectionNotDeterminedByLiability :
  INF.NonFactorabilityWitness assessedLiability taxPaidCash
collectionNotDeterminedByLiability =
  INF.nonFactorabilityWitness
    worldDueUnpaid worldDuePaid liabilitySameUnpaidPaid collectionDiffers

liabilityAloneDoesNotDetermineCollection :
  INF.FactorsThrough assessedLiability taxPaidCash → ⊥
liabilityAloneDoesNotDetermineCollection =
  INF.witnessRulesOutEveryFlatFactorisation
    collectionNotDeterminedByLiability

paidCashEqual :
  taxPaidCash worldDuePaid ≡ taxPaidCash worldDuePaidSpent
paidCashEqual = refl

appropriationDiffers :
  appropriatedCareCash worldDuePaid ≡
  appropriatedCareCash worldDuePaidSpent → ⊥
appropriationDiffers ()

appropriationNotDeterminedByCash :
  INF.NonFactorabilityWitness taxPaidCash appropriatedCareCash
appropriationNotDeterminedByCash =
  INF.nonFactorabilityWitness
    worldDuePaid worldDuePaidSpent paidCashEqual appropriationDiffers

cashReceiptsDoNotDetermineCareAppropriation :
  INF.FactorsThrough taxPaidCash appropriatedCareCash → ⊥
cashReceiptsDoNotDetermineCareAppropriation =
  INF.witnessRulesOutEveryFlatFactorisation
    appropriationNotDeterminedByCash

costsDifferDespiteSameCash :
  collectionCostCash worldDuePaid ≡
  collectionCostCash worldDuePaidHigherCost → ⊥
costsDifferDespiteSameCash ()

collectionCostsNotDeterminedByCash :
  INF.FactorsThrough taxPaidCash collectionCostCash → ⊥
collectionCostsNotDeterminedByCash =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      worldDuePaid worldDuePaidHigherCost refl
      costsDifferDespiteSameCash)

------------------------------------------------------------------------
-- An assessed tax receipt can be adequate for its own query, while unsafe
-- for cash collection, collection costs or public appropriation queries.
------------------------------------------------------------------------

data FiscalQuery : Set where
  taxDue : FiscalQuery
  actualCollection : FiscalQuery
  collectionCost : FiscalQuery
  careAppropriation : FiscalQuery

fiscalAnswer : FiscalQuery → FiscalExecution → Nat
fiscalAnswer taxDue world = assessedLiability world
fiscalAnswer actualCollection world = taxPaidCash world
fiscalAnswer collectionCost world = collectionCostCash world
fiscalAnswer careAppropriation world = appropriatedCareCash world

fiscalSemantics : Query.QuerySemantics FiscalExecution FiscalQuery Nat
fiscalSemantics = Query.querySemantics fiscalAnswer

taxDueAdequate :
  Query.AdequateFor assessedLiability fiscalSemantics taxDue
taxDueAdequate =
  Query.factorsForQuery
    {project = assessedLiability}
    {semantics = fiscalSemantics}
    {query = taxDue}
    (λ due → due) (λ _ → refl)

actualCollectionDefect :
  Query.QueryAdequacyDefect
    assessedLiability fiscalSemantics actualCollection
actualCollectionDefect =
  Query.queryAdequacyDefect
    {project = assessedLiability}
    {semantics = fiscalSemantics}
    {query = actualCollection}
    worldDueUnpaid worldDuePaid
    liabilitySameUnpaidPaid collectionDiffers

taxDueNotAdequateToInferActualCollection :
  Query.AdequateFor
    assessedLiability fiscalSemantics actualCollection → ⊥
taxDueNotAdequateToInferActualCollection =
  Query.queryAdequacyDefectBlocksFactorisation actualCollectionDefect

------------------------------------------------------------------------
-- In-kind transfer and dual-class votes: loss of an ORDINARY share block
-- can leave a weighted super-voting founder block intact. It is not a
-- realistic firm data object; legal voting mechanics vary by jurisdiction.
------------------------------------------------------------------------

record ShareVoteState : Set where
  constructor share-vote-state
  field
    ownerOrdinaryShares : Nat
    ownerSuperVotingShares : Nat
    allOrdinaryShares : Nat
    allSuperVotingShares : Nat
open ShareVoteState public

ownerWeightedVotes : ShareVoteState → Nat
ownerWeightedVotes state =
  ownerOrdinaryShares state + 10 * ownerSuperVotingShares state

totalWeightedVotes : ShareVoteState → Nat
totalWeightedVotes state =
  allOrdinaryShares state + 10 * allSuperVotingShares state

votesBeforeTransfer : ShareVoteState
votesBeforeTransfer = share-vote-state 6 3 20 3

votesAfterSixOrdinaryTransferred : ShareVoteState
votesAfterSixOrdinaryTransferred = share-vote-state 0 3 20 3

originalVotes36 : ownerWeightedVotes votesBeforeTransfer ≡ 36
originalVotes36 = refl

postTransferVotes30 :
  ownerWeightedVotes votesAfterSixOrdinaryTransferred ≡ 30
postTransferVotes30 = refl

totalVotes50 :
  totalWeightedVotes votesAfterSixOrdinaryTransferred ≡ 50
totalVotes50 = refl

afterTransferVotesRemainAboveHalf :
  2 * ownerWeightedVotes votesAfterSixOrdinaryTransferred ≡ 60
afterTransferVotesRemainAboveHalf = refl

-- The exact 60 versus 50 numerical values establish a strict majority
-- only given the stylised weighted-vote allocation. No outside law imported.
afterTransferFullVotes :
  totalWeightedVotes votesBeforeTransfer ≡
  totalWeightedVotes votesAfterSixOrdinaryTransferred
afterTransferFullVotes = refl

------------------------------------------------------------------------
-- A yearly 100% above-threshold assessment is not a continuous-time hard
-- cap when positive growth occurs *between* assessment dates.
------------------------------------------------------------------------

postAssessmentHoldings : Nat
postAssessmentHoldings =
  Tax.netWealthAfterExcessTax 3 (Tax.owned-net-wealth 5)

assessmentClearsExcess : postAssessmentHoldings ≡ 3
assessmentClearsExcess = refl

interimStock : Nat
interimStock = postAssessmentHoldings + 2

interimStockFive : interimStock ≡ 5
interimStockFive = refl

interimAboveThresholdAgain :
  interimStock ∸ 3 ≡ 2
interimAboveThresholdAgain = refl

nextAssessmentAgainThree :
  Tax.netWealthAfterExcessTax
    3 (Tax.owned-net-wealth interimStock) ≡ 3
nextAssessmentAgainThree = refl

------------------------------------------------------------------------
-- Non-promotion fences. This module makes no assertion about collection
-- probabilities, fiscal multipliers, real companies, or achieved care.
------------------------------------------------------------------------

data AssessmentIsCollection : Set where
data AppropriationGuaranteesCareAccess : Set where
data TransferredValueProvesLostCorporateControl : Set where
data AnnualCapIsContinuousCap : Set where

assessmentIsNotAutomaticallyCollection :
  AssessmentIsCollection → ⊥
assessmentIsNotAutomaticallyCollection ()

appropriationIsNotAutomaticallyAccess :
  AppropriationGuaranteesCareAccess → ⊥
appropriationIsNotAutomaticallyAccess ()

wealthTransferIsNotAutomaticallyControlTransfer :
  TransferredValueProvesLostCorporateControl → ⊥
wealthTransferIsNotAutomaticallyControlTransfer ()

annualSnapshotIsNotContinuousBound :
  AnnualCapIsContinuousCap → ⊥
annualSnapshotIsNotContinuousBound ()

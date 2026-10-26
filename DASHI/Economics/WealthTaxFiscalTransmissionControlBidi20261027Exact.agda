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

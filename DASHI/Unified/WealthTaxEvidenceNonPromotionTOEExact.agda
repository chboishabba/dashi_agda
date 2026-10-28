module DASHI.Unified.WealthTaxEvidenceNonPromotionTOEExact where

-- TOE consumer for original DASHI Economics/Philosophy/Sociology owners.
-- No new political philosophy, economic causal law or empirical certificate.
-- The finite proofs are source-written by the respective existing modules.
-- Research direction: Johl Brown; ChatGPT assisted integration 2026-10-27.
-- Original Piketty, Crenshaw, Fraser, Collins, Arnstein, Marx, FATF, OECD,
-- Fagereng et al. and historical sources retain their dated original claims.
-- Ibrahim 2017 FLN navigation is not a wealth-tax proof or Monster action.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_≤_; _⊓_; _∸_)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attributed
import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Sources
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Economics.WealthInheritanceVacancyTaxMaxCut20261027Exact as Base
import DASHI.Economics.WealthTaxPowerCareSociologyBidi20261027Exact as Soc
import DASHI.Economics.WealthTaxFiscalTransmissionControlBidi20261027Exact as Fiscal
import DASHI.Economics.WealthTaxDashiTradeMarketMaterialBidiExact as DashiTradeTax

-- Flow/stock tax bases are separate even when numerical liabilities agree.
toeWealthIsNotIncomeTax :
  Base.incomeHundredAboveThreshold ≡
  Base.wealthHundredAboveThreshold → ⊥
toeWealthIsNotIncomeTax = Base.incomeTaxIsNotStockCap

-- Corporate multinational top-ups do not equal a personal stock cap.
toeGloBEIsNotPersonalStockCap :
  Base.multinationalGloBEProfitTopUp ≡
  Base.wealthHundredAboveThreshold → ⊥
toeGloBEIsNotPersonalStockCap =
  Base.corporateMinimumTaxIsNotPersonalWealthCap

-- Hypothetical idle equity and statutory vacant residential property do not
-- share a legal taxable object merely because first-year rates can match.
toeProposedIdleEquityLevyIsNotVacancyTax :
  Base.proposedDurationEscalatingIdleEquityLevy ≡
  Base.vacantHomesStatusLevy → ⊥
toeProposedIdleEquityLevyIsNotVacancyTax =
  Base.idleEquityIsNotVacantHouse

toeIdleEquityAIScheduleDoesNotCreateStatute :
  Base.AIIdleEquityProposalIsEnactedLaw → ⊥
toeIdleEquityAIScheduleDoesNotCreateStatute =
  Base.aiIdleEquitySuggestionCannotSelfEnact

-- Source-written exact witness: one tax observation cannot recover votes.
toeTaxReceiptDoesNotDetermineVoting :
  INF.FactorsThrough Soc.assessedTax Soc.controllingVotes → ⊥
toeTaxReceiptDoesNotDetermineVoting =
  Soc.votesCannotFactorThroughTaxReceipt

-- Source-written exact witness: the same observation cannot recover care.
toeTaxReceiptDoesNotDetermineCare :
  INF.FactorsThrough Soc.assessedTax Soc.accessibleCareCapacity → ⊥
toeTaxReceiptDoesNotDetermineCare =
  Soc.careCannotFactorThroughTaxReceipt

-- The tax amount cannot identify whether the liability was paid.
toeAssessmentDoesNotDetermineCashCollection :
  INF.FactorsThrough Fiscal.assessedLiability Fiscal.taxPaidCash → ⊥
toeAssessmentDoesNotDetermineCashCollection =
  Fiscal.liabilityAloneDoesNotDetermineCollection

-- The cash receipt cannot determine which budget appropriations followed.
toeCashCollectionDoesNotDetermineCareAppropriation :
  INF.FactorsThrough Fiscal.taxPaidCash Fiscal.appropriatedCareCash → ⊥
toeCashCollectionDoesNotDetermineCareAppropriation =
  Fiscal.cashReceiptsDoNotDetermineCareAppropriation

-- A matching AI-risk feature alone does not identify legal tax liability.
toeAIRiskScoreDoesNotDetermineTaxLiability :
  INF.FactorsThrough
    Fiscal.auditSignal Fiscal.auditedIllustrativeWealthLiability → ⊥
toeAIRiskScoreDoesNotDetermineTaxLiability =
  Fiscal.riskSignalAloneIsNotTaxAuthority

-- Interpretive source provenance cannot certify real-world tax incidence.
toeAuthoredPoliticalTextDoesNotProveOutcome :
  Base.AnyPoliticalTextProvesContemporaryPolicyOutcome → ⊥
toeAuthoredPoliticalTextDoesNotProveOutcome =
  Base.authoredTheoryIsNotOutcomeProof

toeFiniteWorldsDoNotProvePolicyCausation :
  Soc.FiniteTaxCounterexampleProvesCausalOutcome → ⊥
toeFiniteWorldsDoNotProvePolicyCausation =
  Soc.finiteWitnessDoesNotCertifyRealWorldCausation

toeInequalityTheoryDoesNotFixUniversalTaxRate :
  Soc.SocialTheoryDictatesOneTaxRate → ⊥
toeInequalityTheoryDoesNotFixUniversalTaxRate =
  Soc.socialTheoryDoesNotDictateOneTaxRate

-- Reuse the CORE attributed-source and evidence proof owners.
-- Neither a bibliography entry nor a duplicated report can supply
-- independent confirmation, empirical effect or Agda theorem authority.
toeAnyAttributedCitationImportsNoTheorem :
  (source : Attributed.AttributedSource) →
  Attributed.citationImportsProof source ≡ false
toeAnyAttributedCitationImportsNoTheorem =
  Attributed.citationImportsProofIsFalse

toeAnyAttributedCitationCreatesNoAuthority :
  (source : Attributed.AttributedSource) →
  Attributed.citationCreatesAuthority source ≡ false
toeAnyAttributedCitationCreatesNoAuthority =
  Attributed.citationCreatesAuthorityIsFalse

toeSnowballCitationDoesNotProveTaxEffect :
  Snowball.CitationCreatesProof → ⊥
toeSnowballCitationDoesNotProveTaxEffect =
  Snowball.citationDoesNotCreateProof

toeSourceStatementDoesNotEstablishSystemicEffect :
  Sources.SourcePropositionImpliesSystemicClassificationPermission → ⊥
toeSourceStatementDoesNotEstablishSystemicEffect =
  Sources.sourcePropositionDoesNotAutoPromoteToSystemicClassification

toeSecondaryReportDoesNotBecomeIndependentStudy :
  Sources.SameContentImpliesIndependentProducerPermission → ⊥
toeSecondaryReportDoesNotBecomeIndependentStudy =
  Sources.sameContentDoesNotAutoPromoteToIndependentProducer

toeRepublishedOECDChapterIsNotNewIndependentProducer :
  Evidence.independent ≡ Evidence.sharedLineage → ⊥
toeRepublishedOECDChapterIsNotNewIndependentProducer =
  Evidence.independent≠sharedLineage

toePaperCannotSupplyKernelCertification :
  Sources.SourceReceiptImpliesPromotionStepPermission → ⊥
toePaperCannotSupplyKernelCertification =
  Sources.sourceReceiptDoesNotAutoPromoteToPromotionStep

-- Existing standalone dashiTRADE and Agda finance owners are independent
-- of the tax policy: the same assessed liability does not select executable
-- market actions; a price/demand headline does not grant refinance capacity.
toeTaxDoesNotFixTradeBuy :
  INF.FactorsThrough DashiTradeTax.taxAssessed DashiTradeTax.canBuy → ⊥
toeTaxDoesNotFixTradeBuy =
  DashiTradeTax.taxAmountCannotFixBuy

toeDemandDoesNotFixRefinance :
  INF.FactorsThrough
    DashiTradeTax.capitalDemandSignal DashiTradeTax.refinanceViability → ⊥
toeDemandDoesNotFixRefinance =
  DashiTradeTax.headlineDemandCannotFixRefinance

toeMarketDirectionDoesNotFixCollection :
  INF.FactorsThrough
    DashiTradeTax.candidateDirection DashiTradeTax.taxCollected → ⊥
toeMarketDirectionDoesNotFixCollection =
  DashiTradeTax.marketDirectionCannotFixCollection

toeTaxLiabilityDoesNotCreateBrokerOrder :
  DashiTradeTax.AssessedLiabilityCreatesMarketOrder → ⊥
toeTaxLiabilityDoesNotCreateBrokerOrder =
  DashiTradeTax.taxLiabilityIsNotTradingPermission

-- Funding paths use the inherited market/finance fibres, not a fresh
-- economic theorem. Collected cash cannot determine liquidation volume.
toeTaxPaymentCannotDetermineSharesSold :
  INF.FactorsThrough
    DashiTradeTax.taxPaymentForRoute DashiTradeTax.shareUnitsSold → ⊥
toeTaxPaymentCannotDetermineSharesSold =
  DashiTradeTax.paidTaxCannotDetermineUnitsSold

-- A volume count is not an executable price-impact or transaction-cost quote.
toeShareVolumeCannotDetermineExecutionCost :
  INF.FactorsThrough
    DashiTradeTax.shareUnitsSold DashiTradeTax.executionCashCost → ⊥
toeShareVolumeCannotDetermineExecutionCost =
  DashiTradeTax.saleVolumeCannotDetermineExecutionCost

-- Share settlement is not a measure of machines, workers or power capacity.
toeSharesSoldCannotDetermineInstalledCapacity :
  INF.FactorsThrough
    DashiTradeTax.shareUnitsSold DashiTradeTax.installedMachineUnits → ⊥
toeSharesSoldCannotDetermineInstalledCapacity =
  DashiTradeTax.saleVolumeCannotDeterminePhysicalCapacity

-- Owner-registered transfer classes, not aggregate transaction count, pay
-- the same-object voting-control inference. The finite link is synthetic.
toeShareSaleCountDoesNotFixWeightedVoting :
  INF.FactorsThrough
    DashiTradeTax.routedUnitsSold DashiTradeTax.weightedOwnerVotesAfter → ⊥
toeShareSaleCountDoesNotFixWeightedVoting =
  DashiTradeTax.quantityCannotFixVotingControl

-- Conditional positive accounting identity under explicit no-liquidity,
-- no-credit assumptions. Does not assert that any real taxpayer must sell.
toeNoCashNoCreditNeedsSaleProceeds :
  (route : DashiTradeTax.FundingRoute) →
  DashiTradeTax.unrestrictedCash route ≡ zero →
  DashiTradeTax.newLoanCash route ≡ zero →
  DashiTradeTax.grossSaleCash route ≡
    DashiTradeTax.taxPaymentForRoute route
    + DashiTradeTax.executionCashCost route
toeNoCashNoCreditNeedsSaleProceeds =
  DashiTradeTax.noOtherFundingImpliesSaleProceeds

-- New bounded settlement seam: the existence of an order or of an
-- executed fill is insufficient to reconstruct cleared units.
-- These are source-owned INF examples, not broker/custody confirmations.
toeSubmittedOrderDoesNotIdentifySettlement :
  INF.FactorsThrough
    DashiTradeTax.submittedUnits DashiTradeTax.settledShareCount → ⊥
toeSubmittedOrderDoesNotIdentifySettlement =
  DashiTradeTax.submittedOrderDoesNotDetermineSettlement

toeExecutedVolumeDoesNotIdentifySettlement :
  INF.FactorsThrough
    DashiTradeTax.executedShareCount DashiTradeTax.settledShareCount → ⊥
toeExecutedVolumeDoesNotIdentifySettlement =
  DashiTradeTax.executionDoesNotDetermineSettlement

toeTwoFillCashIdentity :
  DashiTradeTax.grossSaleCash
    (DashiTradeTax.settledFundingRoute DashiTradeTax.twoPricesThreeProceeds)
  ≡ DashiTradeTax.firstSettledUnits DashiTradeTax.twoPricesThreeProceeds
      * DashiTradeTax.firstUnitPrice DashiTradeTax.twoPricesThreeProceeds
    + DashiTradeTax.secondSettledUnits DashiTradeTax.twoPricesThreeProceeds
      * DashiTradeTax.secondUnitPrice DashiTradeTax.twoPricesThreeProceeds
toeTwoFillCashIdentity =
  DashiTradeTax.twoFillCashConservation

-- Settlement cash is an optional, separately timed source of payment.
-- The finite conditional chronology has no permission to infer bridge loans,
-- exchange settlement, or observed taxpayer payments from a quotation.
toeEarlierTaxReceiptCannotUseLaterSaleWithoutBridge :
  (lag : Nat) → 1 ≡ 3 + lag → ⊥
toeEarlierTaxReceiptCannotUseLaterSaleWithoutBridge =
  DashiTradeTax.priorCashReceiptHasNoForwardSettlementLink

-- Same settled unit count does not identify which issuer/class rights
-- moved. Explicit synthetic labels are not beneficial-ownership evidence.
toeSaleUnitsCannotIdentifySecurityClass :
  INF.FactorsThrough
    DashiTradeTax.saleUnitsOfInstrument DashiTradeTax.instrumentClass → ⊥
toeSaleUnitsCannotIdentifySecurityClass =
  DashiTradeTax.saleVolumeCannotIdentifyInstrumentClass

-- Source-labelled synthetic settlement and share-class reconciliation:
-- exact fixture equality does not authenticate any real tax/custody record.
toeSyntheticSettlementOwnerClassWeld :
  DashiTradeTax.SettlementOwnershipWeld
toeSyntheticSettlementOwnerClassWeld =
  DashiTradeTax.syntheticOrdinaryWeld

-- Official ASX clearing netting is a distinct source/observer plane.
-- Net received cash does not identify gross orders or investor proceeds.
toeNetReceiptDoesNotDetermineGrossTrades :
  INF.FactorsThrough DashiTradeTax.netReceivedCash
    DashiTradeTax.grossSellCash → ⊥
toeNetReceiptDoesNotDetermineGrossTrades =
  DashiTradeTax.netReceiptCannotRecoverGrossTurnover

------------------------------------------------------------------------
-- CONDITIONAL SOURCE-OWNED GENERIC MATHEMATICS (2026-10-28).
-- An imported theorem is not an executed compiler or empirical receipt.
------------------------------------------------------------------------

toeAssessmentDayFullPaymentLeavesMinimum :
  (threshold wealth : Nat) →
  Base.netWealthAfterExcessTax threshold (Base.owned-net-wealth wealth)
    ≡ wealth ⊓ threshold
toeAssessmentDayFullPaymentLeavesMinimum =
  Base.netWealthAfterFullyPaidExcessEqualsMin

toeExcessLiabilityZeroBelowThreshold :
  (threshold wealth : Nat) →
  wealth ≤ threshold →
  Base.hundredPercentWealthExcess threshold
    (Base.owned-net-wealth wealth) ≡ zero
toeExcessLiabilityZeroBelowThreshold =
  Base.hundredPercentLiabilityZeroBelowThreshold

toeTaxLiabilityMonotoneAtFixedThreshold :
  (threshold : Nat) {smaller larger : Nat} →
  smaller ≤ larger →
  Base.hundredPercentWealthExcess threshold
    (Base.owned-net-wealth smaller)
    ≤ Base.hundredPercentWealthExcess threshold
        (Base.owned-net-wealth larger)
toeTaxLiabilityMonotoneAtFixedThreshold =
  Base.wealthLiabilityMonotoneAtFixedThreshold

toeGenericExecutedQuantityBound :
  (receipt : DashiTradeTax.CountReconciledOrder) →
  DashiTradeTax.executedCount receipt ≤ DashiTradeTax.submittedCount receipt
toeGenericExecutedQuantityBound =
  DashiTradeTax.genericExecutedCountBoundedBySubmitted

toeGenericSettledQuantityBound :
  (receipt : DashiTradeTax.CountReconciledOrder) →
  DashiTradeTax.settledCount receipt ≤ DashiTradeTax.executedCount receipt
toeGenericSettledQuantityBound =
  DashiTradeTax.genericSettledCountBoundedByExecuted

toeArbitraryFillCashRequiresReconciliation :
  (batch : DashiTradeTax.CashReconciledFillBatch) →
  DashiTradeTax.recordedGrossCash batch ≡
    DashiTradeTax.grossFromFiniteSettledFills
      (DashiTradeTax.settledFills batch)
toeArbitraryFillCashRequiresReconciliation =
  DashiTradeTax.genericSettledProceedsIsExactPriceQuantitySum

toePureSellerBuyerShareCountConserved :
  (t : DashiTradeTax.PureIssuedClassTransfer) →
  DashiTradeTax.sellerUnitsBefore t + DashiTradeTax.buyerUnitsBefore t
    ≡ DashiTradeTax.sellerUnitsAfter t + DashiTradeTax.buyerUnitsAfter t
toePureSellerBuyerShareCountConserved =
  DashiTradeTax.shareClassTransferPreservesIssuedSupply

toeCapitalStockRequiresPhysicalReconciliation :
  (period : DashiTradeTax.PhysicalCapacityPeriod) →
  DashiTradeTax.installedAfter period ≡
    (DashiTradeTax.installedBefore period
      + DashiTradeTax.commissionedUnits period)
      ∸ DashiTradeTax.retiredUnits period
toeCapitalStockRequiresPhysicalReconciliation =
  DashiTradeTax.physicalCapitalStockFlowConservation

toeDeliveredCareCannotExceedStaffHours :
  (service : DashiTradeTax.DeliveredCareCapacity) →
  DashiTradeTax.actuallyDeliveredHours service ≤
    DashiTradeTax.actualStaffHours service
toeDeliveredCareCannotExceedStaffHours =
  DashiTradeTax.deliveredCareHoursBoundedByStaffAndEquipment

-- The canonical multi-axis Pareto relation is an existing theorem owner.
-- These source-written application proofs do not invent welfare weights.
toeParetoDominanceReflexive :
  {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  (candidate : Pareto.Model problem) →
  Pareto.WeaklyDominates costs candidate candidate
toeParetoDominanceReflexive =
  DashiTradeTax.paretoDominanceReflexive

toeParetoDominanceTransitive :
  {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  {first second third : Pareto.Model problem} →
  Pareto.WeaklyDominates costs first second →
  Pareto.WeaklyDominates costs second third →
  Pareto.WeaklyDominates costs first third
toeParetoDominanceTransitive =
  DashiTradeTax.paretoDominanceTransitive

toeSyntheticPolicyCostsAreIncomparable :
  (Pareto.WeaklyDominates DashiTradeTax.policyTradeoffCosts
    DashiTradeTax.lowAdministrativeCost DashiTradeTax.increasedCareCapacity
   ⊎ Pareto.WeaklyDominates DashiTradeTax.policyTradeoffCosts
    DashiTradeTax.increasedCareCapacity DashiTradeTax.lowAdministrativeCost)
    → ⊥
toeSyntheticPolicyCostsAreIncomparable =
  DashiTradeTax.paretoOrderDoesNotTotallyRankTheseOptions

-- A participant's gross/net cash requires explicit investor allocations.
-- Amount conservation is conditional on reconciled allocation evidence;
-- no account identity or actual CHESS batch is fabricated.
toeInvestorAllocationsMustReconcileToParticipant :
  (allocation : DashiTradeTax.ParticipantInvestorAllocation) →
  DashiTradeTax.sumInvestorCashUnits
    (DashiTradeTax.investorGrossSales allocation)
    ≡ DashiTradeTax.sumInvestorCashUnits
        (DashiTradeTax.investorGrossPurchases allocation)
      + DashiTradeTax.netReceivedCash
          (DashiTradeTax.netBatch allocation)
toeInvestorAllocationsMustReconcileToParticipant =
  DashiTradeTax.investorAllocationsSumToParticipantObligation

-- Single-instrument DvP is a conditional dual-leg receipt, not proof of
-- actual ASX/CHESS settlement, legal finality or taxpayer source identity.
toeSingleInstrumentDvPFixture :
  DashiTradeTax.SingleInstrumentDvPBatch
toeSingleInstrumentDvPFixture =
  DashiTradeTax.syntheticDeliveredDvP

toeDvPCashAndTitleRequireSameFinalEpoch :
  (batch : DashiTradeTax.SingleInstrumentDvPBatch) →
  DashiTradeTax.cashFinalityEpoch batch ≡
    DashiTradeTax.titleFinalityEpoch batch
toeDvPCashAndTitleRequireSameFinalEpoch =
  DashiTradeTax.deliveryVersusPaymentCashAndTitleCoMove

toeParticipantDvPConservesBothLegs :
  (batch : DashiTradeTax.SingleInstrumentDvPBatch) →
  DashiTradeTax.DirectionBalanced
    (DashiTradeTax.cashDirection (DashiTradeTax.linkedCashBatch batch))
    (DashiTradeTax.grossSellSettlementCash (DashiTradeTax.linkedCashBatch batch))
    (DashiTradeTax.grossBuySettlementCash (DashiTradeTax.linkedCashBatch batch))
    (DashiTradeTax.netSettlementCashMagnitude (DashiTradeTax.linkedCashBatch batch))
  × DashiTradeTax.SecurityQuantityBalanced
      (DashiTradeTax.securityDirection batch)
      (DashiTradeTax.grossDeliveredUnits batch)
      (DashiTradeTax.grossReceivedUnits batch)
      (DashiTradeTax.netSecurityUnits batch)
toeParticipantDvPConservesBothLegs =
  DashiTradeTax.aggregateNetPositionsRespectGrossCashAndSecurityTotals

-- Conditional no-phantom-financial-wealth result for a matched
-- cash/debt borrowing receipt. No lending feasibility or market observation.
toeBorrowingMustMatchNewDebt :
  (loan : DashiTradeTax.MatchedBorrowingBalance) →
  DashiTradeTax.debtAfterBorrowing loan ≡
    DashiTradeTax.cashBorrowed loan + DashiTradeTax.debtBeforeBorrowing loan
toeBorrowingMustMatchNewDebt =
  DashiTradeTax.loanProceedsIncreaseLiabilities

toeBorrowingDoesNotByItselfIncreaseCashLessDebt :
  (loan : DashiTradeTax.MatchedBorrowingBalance) →
  DashiTradeTax.cashAfterBorrowing loan ∸
    DashiTradeTax.debtAfterBorrowing loan
    ≡ DashiTradeTax.cashBeforeBorrowing loan ∸
        DashiTradeTax.debtBeforeBorrowing loan
toeBorrowingDoesNotByItselfIncreaseCashLessDebt =
  DashiTradeTax.borrowedCashDoesNotByItselfRaiseNetCashMinusDebt

-- Repository import alone is a source-reachability relationship.
-- It is NOT an Agda kernel certification receipt or a substitute for an
-- observed, exact-head compiler run. No ESD imports are changed.

-- Follow-on economic separation exports. These consume the existing model;
-- TOE reachability does not certify theorem checking or real-world events.

toePrincipalRemittanceIsBoundedByReconciledAssessment :
  (collection : DashiTradeTax.NoAdjustmentCollection) →
  DashiTradeTax.remittedPrincipalUnits collection ≤
    DashiTradeTax.assessedLiabilityUnits collection
toePrincipalRemittanceIsBoundedByReconciledAssessment =
  DashiTradeTax.remittanceBoundedByAssessedLiabilityUnderNoPenalties

toePublicBudgetRequiresReconciledSourcesAndOutflows :
  (budget : DashiTradeTax.ReconciledPublicCashBudget) →
  DashiTradeTax.budgetOutflow budget ≤
    DashiTradeTax.availablePublicCash budget
toePublicBudgetRequiresReconciledSourcesAndOutflows =
  DashiTradeTax.cashBudgetConservationWithCostsAndTransfers

toeCareAppropriationDoesNotProveDeliveredHours :
  INF.FactorsThrough
    DashiTradeTax.careAppropriationAmount
    DashiTradeTax.deliveredCareServiceHours → ⊥
toeCareAppropriationDoesNotProveDeliveredHours =
  DashiTradeTax.careAppropriatedDoesNotDetermineCareDelivered

toeBalancedTaxPaymentDoesNotProveLiquidity :
  INF.FactorsThrough
    DashiTradeTax.identicalRouteCashReceipt
    DashiTradeTax.externalFundsAccessible → ⊥
toeBalancedTaxPaymentDoesNotProveLiquidity =
  DashiTradeTax.routeBalanceDoesNotEstablishLiquidityOrTiming

toeClearingNetDoesNotAuthenticateTaxpayer :
  INF.FactorsThrough
    DashiTradeTax.participantNetCashProjection
    DashiTradeTax.unverifiedInvestorKey → ⊥
toeClearingNetDoesNotAuthenticateTaxpayer =
  DashiTradeTax.participantNetStatementDoesNotIdentifyIndividualTaxpayer

toeTwoOptionParetoWitnessHasDistinctMinimalChoices :
  DashiTradeTax.TwoOptionUndominated
    DashiTradeTax.lowAdministrativeCost
  × DashiTradeTax.TwoOptionUndominated
      DashiTradeTax.increasedCareCapacity
toeTwoOptionParetoWitnessHasDistinctMinimalChoices =
  DashiTradeTax.finiteParetoTradeoffHasTwoDistinctMinimalOptions

-- Unique IDs and per-fill chronology remain conditional local contracts.
-- Neither labels nor exact token uniqueness authenticate a real fill.
toeDistinctLocalFillTokensAndClassLabels :
  (batch : DashiTradeTax.ChronologicalIdentifiedFillBatch) →
  DashiTradeTax.UniqueFillTokens (DashiTradeTax.timestampedFills batch)
  × DashiTradeTax.AllFillLabelsMatch
      (DashiTradeTax.requestedIssuerLabel batch)
      (DashiTradeTax.requestedSecurityClassLabel batch)
      (DashiTradeTax.timestampedFills batch)
toeDistinctLocalFillTokensAndClassLabels =
  DashiTradeTax.uniqueFillIdentityAndMonotoneEventTime

toeDuplicateLocalFillTokenIsRejected :
  DashiTradeTax.UniqueFillTokens
    (DashiTradeTax.syntheticFill7 ∷ DashiTradeTax.syntheticFill7 ∷ []) → ⊥
toeDuplicateLocalFillTokenIsRejected =
  DashiTradeTax.duplicateSevenTokenRejected

-- Composed D11 × D12: exact cash/price sequence plus local token
-- uniqueness. The joined local sequence is not a real broker event.
toeCashReconciledFillsMustShareIdentitySequence :
  (batch : DashiTradeTax.JoinedPriceIdentityBatch) →
  (DashiTradeTax.recordedGrossCash (DashiTradeTax.settledCashBatch batch)
    ≡ DashiTradeTax.grossFromFiniteSettledFills
        (DashiTradeTax.pricedProjection (DashiTradeTax.joinedFills batch)))
  × DashiTradeTax.UniqueFillTokens
      (DashiTradeTax.timedProjection (DashiTradeTax.joinedFills batch))
toeCashReconciledFillsMustShareIdentitySequence =
  DashiTradeTax.joinedIdentityAndCashReconcile

-- H06/H07 existing-owner reuse, not independent new theorems.
-- An author's published argument does not confer DASHI proof authorship.
toeOriginalAuthorDoesNotAutomaticallyOwnDashiProof :
  Sources.SourceArgumentImpliesDASHIFormalisationOwnershipPermission → ⊥
toeOriginalAuthorDoesNotAutomaticallyOwnDashiProof =
  Sources.sourceArgumentDoesNotAutoPromoteToDASHIFormalisationOwnership

-- Secondary narrative does not become an original source producer.
toeDerivedSummaryDoesNotBecomeOriginalEvidence :
  Sources.SecondaryReportImpliesPrimarySourceAuthorityPermission → ⊥
toeDerivedSummaryDoesNotBecomeOriginalEvidence =
  Sources.secondaryReportDoesNotAutoPromoteToPrimaryAuthority

-- 2026-10-28 scoped, source-owned valuation / identity / policy exports.
-- Delegating exports. The implementation and proof provenance stay in the
-- existing economics module. Source reachability is NOT kernel verification.
open DashiTradeTax public using
  ( ScopedNetWealthSnapshot
  ; netWealthBalanceIsWellTyped
  ; TransferWithUnalteredPlant
  ; disposalPreservesExternalAssetTransferAccounting
  ; controllingVotesRequireVerifiedRightsAndAgreements
  ; persistentTransactionIdentityCannotFollowFromValueOrDigest
  ; OfficialSettlementAdmission
  ; actualSettlementFinalityRequiresOfficialReceipt
  ; financialClaimChangeDoesNotIdentifyPhysicalOutput
  ; RivalTaxBaseComparison
  ; rivalPolicyTaxBasesRemainComparableButDistinct
  ; TaggedPolicyScenario
  ; StatutoryPolicyAdmission
  ; policyScenarioRequiresStatuteOrHypotheticalTag
  ; FinitePolicyAccountingPeriod
  ; finitePolicyStateTransitionPreservesAccounting
  ; ExplicitBehaviourAssumptions
  ; behaviouralResponseParametersAreExplicitAssumptions
  ; SharedInitialPolicyComparison
  ; sameInitialStateDifferentInterventionComparison
  ; syntheticModelCannotIdentifyObservedCausalEffect
  ; TaggedFundingReceipt
  ; cashSourceUseIsSingleCounted
  ; FinancedRouteAdmission
  ; routeFundingFeasibleGivenLiquidityCollateralAndTiming
  ; OwnerIssuerSecurityAdmission
  ; authenticatedOwnerIssuerInstrumentClassKey
  ; MatchedPolicyEffectAdmission
  ; measuredPolicyEffectRequiresSameObjectInputs
  ; noUniqueOptimalTaxRateFromParetoOrderAlone
  ; RankedMember
  ; FiniteRankMinimum
  ; finiteNonemptyRankMinimum
  ; StrictlyDominatesAdmissible
  ; NonemptyRankedParetoFront
  ; finiteParetoFrontierNonemptyGivenStrictRank
  ; FiniteAxisStrictWitness
  ; finiteAxisCostSum
  ; finiteAxisCostSumMonotone
  ; finiteAxisSumStrict
  ; strictImprovedAxisFromFiniteCoverage
  ; finiteParetoFrontierIsNonempty
  ; FundingTokenAbsent
  ; UniqueFundingTokens
  ; finiteFundingPartitionConservesUnits
  ; CanonicalFundingEntry
  ; CanonicalFundingBatch
  ; canonicalClaimCannotBeReusedInLaterPosition
  ; canonicalFundingTotalsReconcile
  ; distinctFixtureFundingBatch
  ; fixtureFundingBatchConservesSeven
  ; duplicateFixtureFundingTokenIsRejected
  ; AustralianEquityHoldingMode
  ; OfficialHolderRegistration
  ; holderModeCannotBecomeLegalTitleByNameMatch
  ; MarketRecordKind
  ; executionRecordIsNotOfficialFinality
  ; clearingNetIsNotOfficialFinality
  ; officialSettlementIsNotBeneficiaryAllocation
  )

-- Explicit boundary aliases stay close to TOE use sites.
toeVotesAloneCannotDetermineLegalControl :
  INF.FactorsThrough
    DashiTradeTax.arithmeticVotes
    DashiTradeTax.externallyAssumedEffectiveControl → ⊥
toeVotesAloneCannotDetermineLegalControl =
  DashiTradeTax.controllingVotesRequireVerifiedRightsAndAgreements

toeDigestAloneCannotIdentifyHistoricalTransaction :
  INF.FactorsThrough
    DashiTradeTax.arbitraryDigestLabel
    DashiTradeTax.distinctHistoricalEventLabel → ⊥
toeDigestAloneCannotIdentifyHistoricalTransaction =
  DashiTradeTax.persistentTransactionIdentityCannotFollowFromValueOrDigest

toeFinancialClaimAloneCannotDetermineRealOutput :
  INF.FactorsThrough
    DashiTradeTax.investorFinancialClaimUnits
    DashiTradeTax.physicalOutputUnits → ⊥
toeFinancialClaimAloneCannotDetermineRealOutput =
  DashiTradeTax.financialClaimChangeDoesNotIdentifyPhysicalOutput

toeSyntheticForecastCannotEstablishObservedEffect :
  INF.FactorsThrough
    DashiTradeTax.modelPredictionUnits
    DashiTradeTax.independentlySuppliedOutcomeUnits → ⊥
toeSyntheticForecastCannotEstablishObservedEffect =
  DashiTradeTax.syntheticModelCannotIdentifyObservedCausalEffect

toeEvenTwoPolicyOptionsMayHaveDifferentParetoMinimalRates :
  ((candidate : DashiTradeTax.HypotheticalPolicyOutcome) →
    DashiTradeTax.TwoOptionUndominated candidate →
    DashiTradeTax.rateTagForOutcome candidate
      ≡ DashiTradeTax.exampleZeroRate) → ⊥
toeEvenTwoPolicyOptionsMayHaveDifferentParetoMinimalRates =
  DashiTradeTax.noUniqueOptimalTaxRateFromParetoOrderAlone

-- Exact source ownership for the three distinct 2026 wealth-tax estimands.
-- These disjoint source-target types are *not* independent causal studies by
-- construction and do not combine estimates without a separate study model.
toeRingFirmStudyIsNotFagerengPortfolioEstimand :
  Base.norwegianJointReformFirmMigrationResponse
    ≡ Base.norwegianPortfolioEquityPremiumAllocation → ⊥
toeRingFirmStudyIsNotFagerengPortfolioEstimand =
  Base.ringFirmResponseIsNotFagerengPortfolioResponse

toeRingFirmStudyIsNotJakobsenMigrationAggregateEstimand :
  Base.norwegianJointReformFirmMigrationResponse
    ≡ Base.scandinavianRateMigrationAggregateResponse → ⊥
toeRingFirmStudyIsNotJakobsenMigrationAggregateEstimand =
  Base.ringFirmResponseIsNotJakobsenAggregateResponse

-- I07 non-vacuous witness: the original two synthetic cost axes are
-- explicitly complete and both candidate models are admitted/adequate.
toeSyntheticTwoAxisPolicyFrontierIsNonempty :
  DashiTradeTax.NonemptyRankedParetoFront DashiTradeTax.policyTradeoffCosts
    (λ candidate →
      DashiTradeTax.finiteAxisCostSum DashiTradeTax.policyTradeoffCosts
        (DashiTradeTax.administrationAxis ∷ DashiTradeTax.careShortfallAxis ∷ [])
        (Pareto.model candidate))
    DashiTradeTax.admittedCheapAdministration
    (DashiTradeTax.admittedCareCapacity ∷ [])
toeSyntheticTwoAxisPolicyFrontierIsNonempty =
  DashiTradeTax.twoAxisPolicyFrontierIsNonempty

-- C06 typed finite-batch proof surface. A unique *local* source key is
-- not an independently verified historical economic claim identifier.
toeCanonicalFundingClaimIsNotReusedWithinFiniteBatch :
  {Claim : Set} {canonicalClaimToken : Claim → Nat} →
  (batch : DashiTradeTax.CanonicalFundingBatch Claim canonicalClaimToken) →
  (first : DashiTradeTax.CanonicalFundingEntry Claim canonicalClaimToken) →
  (rest : List (DashiTradeTax.CanonicalFundingEntry Claim canonicalClaimToken)) →
  DashiTradeTax.fundingClaims batch ≡ first ∷ rest →
  (later : DashiTradeTax.CanonicalFundingEntry Claim canonicalClaimToken) →
  DashiTradeTax.RankedMember later rest →
  DashiTradeTax.economicClaim first
    ≡ DashiTradeTax.economicClaim later → ⊥
toeCanonicalFundingClaimIsNotReusedWithinFiniteBatch =
  DashiTradeTax.canonicalClaimCannotBeReusedInLaterPosition

toeBatchSourcePartitionAccountsForEachTaggedClaimOnce :
  {Claim : Set} {canonicalClaimToken : Claim → Nat} →
  (batch : DashiTradeTax.CanonicalFundingBatch Claim canonicalClaimToken) →
  DashiTradeTax.fundingPartitionTotal
    (DashiTradeTax.fundingEntryTags (DashiTradeTax.fundingClaims batch))
    ≡ DashiTradeTax.fundingReceiptsTotal
        (DashiTradeTax.fundingEntryTags (DashiTradeTax.fundingClaims batch))
toeBatchSourcePartitionAccountsForEachTaggedClaimOnce =
  DashiTradeTax.canonicalFundingTotalsReconcile

-- Market authority boundary: even a completed CHESS settlement is not
-- automatically an authenticated downstream beneficial custody allocation.
toeOfficialSettlementAndCustodyAllocationRemainDistinct :
  DashiTradeTax.officialDvPSettlementReceipt
    ≡ DashiTradeTax.validatedBeneficialCustodyAllocation → ⊥
toeOfficialSettlementAndCustodyAllocationRemainDistinct =
  DashiTradeTax.officialSettlementIsNotBeneficiaryAllocation


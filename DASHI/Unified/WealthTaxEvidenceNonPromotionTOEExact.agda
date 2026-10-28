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
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attributed
import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Sources
import DASHI.Core.IntersectionalNonFactorability as INF
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

-- Repository import alone is a source-reachability relationship.
-- It is NOT an Agda kernel certification receipt or a substitute for an
-- observed, exact-head compiler run. No ESD imports are changed.

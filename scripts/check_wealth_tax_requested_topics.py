#!/usr/bin/env python3
"""Fail-closed 42-topic coverage inventory for two user-supplied conversations.

A row checks whether a topic is *explicitly* addressed with a status and
attribution boundary. This test does not prove the truth of sources, verify
legal statements or certify Agda proof terms.

DASHI source-written code: research direction Johl Brown;
OpenAI ChatGPT assistance, 2026-10-27. Prior philosophical/empirical
author ownership remains in the referenced canonical sources.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "Docs/economics/WealthTaxOriginalConversationsFullCoverage20261027.md"

ROW = re.compile(
    r"^\| (T[0-9]{2}) ([^|\n]+?) \| (COVERED_SOURCE_BOUND|FORMAL_FINITE|OPEN_EMPIRICAL) "
    r"\| ([^\n]+?) \| ([^\n]+?) \|$",
    re.MULTILINE,
)
EXPECTED = {f"T{i:02d}" for i in range(1, 43)}
OWNERS = (
    "DASHI/Economics/WealthInheritanceVacancyTaxMaxCut20261027Exact.agda",
    "DASHI/Economics/WealthTaxPowerCareSociologyBidi20261027Exact.agda",
    "DASHI/Economics/WealthTaxFiscalTransmissionControlBidi20261027Exact.agda",
    "DASHI/Economics/WealthTaxDashiTradeMarketMaterialBidiExact.agda",
    "DASHI/Unified/WealthTaxEvidenceNonPromotionTOEExact.agda",
)
PHILOSOPHY_OR_SOCIETY = (
    "Marx", "Engels", "anarch", "postmodern", "Lyotard", "Baudrillard",
    "accelerationism", "Nick Land", "Varoufakis", "techno", "Federici",
    "Fraser", "Crenshaw", "Collins", "Yarvin", "blackpill", "Doomer",
    "fourth-wave", "Pareto",
)
POLICY_AND_HISTORY = (
    "Musk", "Piketty", "Henry George", "Adam Smith", "Roosevelt",
    "94%", "buy, borrow, die", "Vancouver", "Victoria", "AI",
    "inheritance", "Samsung", "Pillar Two", "UK SDRT",
    "Beneficial ownership", "assessed", "collected",
    "causal", "Ibrahim",
)

def main() -> None:
    text = DOC.read_text(encoding="utf-8")
    rows = ROW.findall(text)
    observed = Counter(id for id, _, _, _, _ in rows)
    missing = EXPECTED - observed.keys()
    unexpected = observed.keys() - EXPECTED
    duplicates = {id: count for id, count in observed.items() if count != 1}
    assert not missing, f"Missing requested topic IDs: {sorted(missing)}"
    assert not unexpected, f"Unknown topic IDs: {sorted(unexpected)}"
    assert not duplicates, f"Duplicate topic IDs: {duplicates}"
    assert len(rows) == 42, f"expected 42 rows, got {len(rows)}"
    for id, label, status, claim, source in rows:
        assert len(claim.strip()) > 35, f"{id} missing substantive scope"
        assert len(source.strip()) > 30, f"{id} missing source/boundary"
        if status == "OPEN_EMPIRICAL":
            assert ("required" in claim.lower() or "not" in claim.lower()
                    or "pending" in claim.lower() or "need" in claim.lower()
                    or "must" in claim.lower() or "uncorroborated" in claim.lower()
                    or "no " in claim.lower()), f"{id}: gap must remain explicit"
    for term in PHILOSOPHY_OR_SOCIETY + POLICY_AND_HISTORY:
        assert term.lower() in text.lower(), f"topic phrase absent: {term}"
    for owner in OWNERS:
        assert (ROOT / owner).is_file(), f"missing live formal owner: {owner}"
    script = (ROOT / "scripts/check_wealth_tax_maxcut.py").read_text(encoding="utf-8")
    for symbol in ("test_finite_caps", "test_assessment_collection_appropriation_are_distinct",
                   "test_dual_class_voting_post_transfer", "test_assessment_vs_interim_growth"):
        assert symbol in script, f"missing bounded regression: {symbol}"
    root_source = (ROOT / "DASHI/Everything.agda").read_text(encoding="utf-8")
    bridge_module = "import DASHI.Unified.WealthTaxEvidenceNonPromotionTOEExact"
    assert bridge_module in root_source, "TOE consumer not attached to canonical import graph"
    bridge = (ROOT / OWNERS[-1]).read_text(encoding="utf-8")
    for symbol in (
        "toeWealthIsNotIncomeTax",
        "toeTaxReceiptDoesNotDetermineVoting",
        "toeTaxReceiptDoesNotDetermineCare",
        "toeAssessmentDoesNotDetermineCashCollection",
        "toeCashCollectionDoesNotDetermineCareAppropriation",
        "toeAIRiskScoreDoesNotDetermineTaxLiability",
        "toeFiniteWorldsDoNotProvePolicyCausation",
        "toeAnyAttributedCitationImportsNoTheorem",
        "toeAnyAttributedCitationCreatesNoAuthority",
        "toeSnowballCitationDoesNotProveTaxEffect",
        "toeSourceStatementDoesNotEstablishSystemicEffect",
        "toeSecondaryReportDoesNotBecomeIndependentStudy",
        "toeRepublishedOECDChapterIsNotNewIndependentProducer",
        "toePaperCannotSupplyKernelCertification",
        "toeTaxDoesNotFixTradeBuy",
        "toeDemandDoesNotFixRefinance",
        "toeMarketDirectionDoesNotFixCollection",
        "toeTaxLiabilityDoesNotCreateBrokerOrder",
        "toeTaxPaymentCannotDetermineSharesSold",
        "toeShareVolumeCannotDetermineExecutionCost",
        "toeSharesSoldCannotDetermineInstalledCapacity",
        "toeShareSaleCountDoesNotFixWeightedVoting",
        "toeNoCashNoCreditNeedsSaleProceeds",
        "toeSubmittedOrderDoesNotIdentifySettlement",
        "toeExecutedVolumeDoesNotIdentifySettlement",
        "toeTwoFillCashIdentity",
        "toeEarlierTaxReceiptCannotUseLaterSaleWithoutBridge",
        "toeSaleUnitsCannotIdentifySecurityClass",
        "toeSyntheticSettlementOwnerClassWeld",
        "toeNetReceiptDoesNotDetermineGrossTrades",
        "toeAssessmentDayFullPaymentLeavesMinimum",
        "toeExcessLiabilityZeroBelowThreshold",
        "toeTaxLiabilityMonotoneAtFixedThreshold",
        "toeGenericExecutedQuantityBound",
        "toeGenericSettledQuantityBound",
        "toeArbitraryFillCashRequiresReconciliation",
        "toePureSellerBuyerShareCountConserved",
        "toeCapitalStockRequiresPhysicalReconciliation",
        "toeDeliveredCareCannotExceedStaffHours",
        "toeParetoDominanceReflexive",
        "toeParetoDominanceTransitive",
        "toeSyntheticPolicyCostsAreIncomparable",
        "toeInvestorAllocationsMustReconcileToParticipant",
        "toeSingleInstrumentDvPFixture",
        "toeDvPCashAndTitleRequireSameFinalEpoch",
        "toeParticipantDvPConservesBothLegs",
        "toeBorrowingMustMatchNewDebt",
        "toeBorrowingDoesNotByItselfIncreaseCashLessDebt",
        "toePrincipalRemittanceIsBoundedByReconciledAssessment",
        "toePublicBudgetRequiresReconciledSourcesAndOutflows",
        "toeCareAppropriationDoesNotProveDeliveredHours",
        "toeBalancedTaxPaymentDoesNotProveLiquidity",
        "toeClearingNetDoesNotAuthenticateTaxpayer",
        "toeTwoOptionParetoWitnessHasDistinctMinimalChoices",
        "toeDistinctLocalFillTokensAndClassLabels",
        "toeDuplicateLocalFillTokenIsRejected",
        "toeCashReconciledFillsMustShareIdentitySequence",
        "toeOriginalAuthorDoesNotAutomaticallyOwnDashiProof",
        "toeDerivedSummaryDoesNotBecomeOriginalEvidence",
    ):
        assert symbol in bridge, f"missing source-owned TOE boundary: {symbol}"
    # These are direct aliases of EXISTING source and evidence owners.
    # A missing owner defeats provenance reachability even when the alias
    # name remains present in the TOE consumer.
    for owner_module in (
        "DASHI.Core.AttributedSourceCore",
        "DASHI.Core.EvidenceHyperfabricExact",
        "DASHI.Core.SnowballAttributionProvenanceInvariantExact",
        "DASHI.Economics.SourceAttributionPromotionBoundaryExact",
    ):
        expected_import = "import " + owner_module
        assert expected_import in bridge, (
            f"source-owned non-promotion module is no longer imported: {owner_module}"
        )
        owner_path = ROOT / (owner_module.replace(".", "/") + ".agda")
        assert owner_path.is_file(), f"source/evidence owner absent: {owner_path}"
    assert not re.search(r"(?m)^\s*(postulate|{-#\s*TERMINATING)", bridge), (
        "thin TOE bridge must use source-owned theorem aliases, not axioms"
    )
    # The shadow bridge must use the pre-existing Agda trading, finance and
    # generic non-factorability owners. No standalone runtime is imported.
    dashi_tax_bridge = (ROOT / OWNERS[-2]).read_text(encoding="utf-8")
    for original_owner in (
        "DASHI.Core.IntersectionalNonFactorability",
        "DASHI.Finance.DashiTradeFibreBridgeExact",
        "DASHI.Trading.DashiTradeDreamOptionConeExact",
        "DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact",
        "DASHI.Economics.WealthTaxFiscalTransmissionControlBidi20261027Exact",
        "DASHI.Core.AdmissibleConsumerMDLHyperfabricExact",
    ):
        assert "import " + original_owner in dashi_tax_bridge, (
            "missing inherited dashiTRADE/finance/tax owner: " + original_owner
        )
    for theorem in (
        "taxAmountCannotFixBuy", "headlineDemandCannotFixRefinance",
        "marketDirectionCannotFixCollection",
        "taxLiabilityIsNotTradingPermission", "holdStillAvailable",
        "paidTaxCannotDetermineUnitsSold",
        "saleVolumeCannotDetermineExecutionCost",
        "saleVolumeCannotDeterminePhysicalCapacity",
        "fundingBalances", "cashFunded", "assetSaleFunded", "debtFunded",
        "FundingVoteReconciliation", "ordinarySaleLink", "superVotingSaleLink",
        "quantityCannotFixVotingControl",
        "noOtherFundingImpliesSaleProceeds",
        "TwoFillSettlementLink", "submittedWithoutFill",
        "executedUnsettled", "twoPricesThreeProceeds",
        "submittedOrderDoesNotDetermineSettlement",
        "executionDoesNotDetermineSettlement", "twoFillCashConservation",
        "MatchedSettlementTaxChronology",
        "priorCashReceiptHasNoForwardSettlementLink",
        "IdentifiedClassSettlement", "ClassCompatibleWithTransfer",
        "syntheticOrdinarySettlement", "syntheticSuperSettlement",
        "saleVolumeCannotIdentifyInstrumentClass",
        "SettlementOwnershipWeld", "syntheticOrdinaryWeld",
        "syntheticSuperVotingWeld", "ParticipantClearingBatch",
        "noClearedTransactions", "offsettingClearedTransactions",
        "netReceiptCannotRecoverGrossTurnover",
        "CountReconciledOrder",
        "genericExecutedCountBoundedBySubmitted",
        "genericSettledCountBoundedByExecuted",
        "genericSettledCountBoundedBySubmitted",
        "CashReconciledFillBatch",
        "genericSettledProceedsIsExactPriceQuantitySum",
        "PureIssuedClassTransfer",
        "shareClassTransferPreservesIssuedSupply",
        "PhysicalCapacityPeriod",
        "physicalCapitalStockFlowConservation",
        "DeliveredCareCapacity",
        "deliveredCareHoursBoundedByStaffAndEquipment",
        "paretoDominanceReflexive", "paretoDominanceTransitive",
        "policyTradeoffCosts", "paretoOrderDoesNotTotallyRankTheseOptions",
        "ParticipantInvestorAllocation",
        "investorAllocationsSumToParticipantObligation",
        "DirectionalClearingBatch", "directionalParticipantCashBalance",
        "SingleInstrumentDvPBatch",
        "aggregateNetPositionsRespectGrossCashAndSecurityTotals",
        "deliveryVersusPaymentCashAndTitleCoMove",
        "MatchedBorrowingBalance", "loanProceedsIncreaseLiabilities",
        "borrowedCashDoesNotByItselfRaiseNetCashMinusDebt",
        "NoAdjustmentCollection", "remittanceBoundedByAssessedLiabilityUnderNoPenalties",
        "ReconciledPublicCashBudget", "cashBudgetConservationWithCostsAndTransfers",
        "careAppropriatedDoesNotDetermineCareDelivered",
        "routeBalanceDoesNotEstablishLiquidityOrTiming",
        "participantNetStatementDoesNotIdentifyIndividualTaxpayer",
        "FixedInputConstructionFeasibility",
        "finiteParetoTradeoffHasTwoDistinctMinimalOptions",
        "ChronologicalIdentifiedFillBatch", "TimestampedFill",
        "TokenAbsent", "UniqueFillTokens", "AllFillLabelsMatch",
        "uniqueFillIdentityAndMonotoneEventTime",
        "duplicateSevenTokenRejected",
        "JoinedPriceIdentityBatch", "JoinedPriceIdentityFill",
        "joinedIdentityAndCashReconcile", "syntheticPriceIdentityBatch",
    ):
        assert theorem in dashi_tax_bridge, "missing tax-market gate: " + theorem
    # Follow-on must remain within the original application and TOE
    # owner, with no synthetic receipt upgraded to verified market evidence.
    for symbol in (
        "ScopedNetWealthSnapshot",
        "cashSourceUseIsSingleCounted",
        "disposalPreservesExternalAssetTransferAccounting",
        "routeFundingFeasibleGivenLiquidityCollateralAndTiming",
        "controllingVotesRequireVerifiedRightsAndAgreements",
        "persistentTransactionIdentityCannotFollowFromValueOrDigest",
        "actualSettlementFinalityRequiresOfficialReceipt",
        "financialClaimChangeDoesNotIdentifyPhysicalOutput",
        "rivalPolicyTaxBasesRemainComparableButDistinct",
        "StatutoryPolicyAdmission",
        "finitePolicyStateTransitionPreservesAccounting",
        "ExplicitBehaviourAssumptions",
        "sameInitialStateDifferentInterventionComparison",
        "syntheticModelCannotIdentifyObservedCausalEffect",
        "authenticatedOwnerIssuerInstrumentClassKey",
        "measuredPolicyEffectRequiresSameObjectInputs",
        "noUniqueOptimalTaxRateFromParetoOrderAlone",
    ):
        assert symbol in dashi_tax_bridge, f"missing source-owned economy gate: {symbol}"
    for symbol in (
        "toeVotesAloneCannotDetermineLegalControl",
        "toeDigestAloneCannotIdentifyHistoricalTransaction",
        "toeFinancialClaimAloneCannotDetermineRealOutput",
        "toeSyntheticForecastCannotEstablishObservedEffect",
        "toeEvenTwoPolicyOptionsMayHaveDifferentParetoMinimalRates",
    ):
        assert symbol in bridge, f"missing TOE evidence firewall: {symbol}"
    assert "open DashiTradeTax public using" in bridge, (
        "follow-on sources not reachable from original TOE consumer"
    )
    assert not re.search(r"(?m)^\s*(postulate|{-#\s*TERMINATING)", dashi_tax_bridge), (
        "cross-domain application must not introduce axioms or termination bypass"
    )
    workflow = (ROOT / ".github/workflows/philosophy.yml").read_text(encoding="utf-8")
    assert "dashi-agda-preflight --root ." in workflow, "semantic preflight no longer scheduled"
    assert "agda $AGDA_FLAGS DASHI/Unified/WealthTaxEvidenceNonPromotionTOEExact.agda" in workflow, (
        "TOE bridge has no compiler-stage gate"
    )
    for owner in OWNERS:
        assert owner in workflow, f"no CI reference for Agda owner: {owner}"
    for label in ("oecdSocialProtection2026", "fagerengGuisoRing2026",
                  "chatzouzIMF2026", "euCommissionWealthTax2026"):
        source = (ROOT / OWNERS[0]).read_text(encoding="utf-8")
        assert label in source, f"missing 2026 independent economic source: {label}"
    # Claim-specific original-root coverage, not evidence of empirical truth.
    tax_source = (ROOT / OWNERS[0]).read_text(encoding="utf-8")
    social_source = (ROOT / OWNERS[1]).read_text(encoding="utf-8")
    base = (ROOT / OWNERS[0]).read_text(encoding="utf-8")
    for theorem in (
        "hundredPercentLiabilityZeroBelowThreshold",
        "netWealthAfterFullyPaidExcessEqualsMin",
        "wealthLiabilityNeverExceedsAssessedWealth",
        "wealthLiabilityMonotoneAtFixedThreshold",
    ):
        assert theorem in base, f"missing general tax/threshold theorem: {theorem}"
    for symbol in ("proposedDurationEscalatingIdleEquityLevy",
                   "proposalIdleEquityRateBasisPoints",
                   "sourceAIProposedRatesAreNotVictoriaLaw"):
        assert symbol in tax_source, f"pasted 1/2/5 proposal lost: {symbol}"
    for symbol in ("bellHooks2000", "baudrillard1981", "kropotkin1892"):
        assert symbol in social_source, f"original philosophical author omitted: {symbol}"
    assert "test_ai_proposed_idle_equity_schedule_is_not_victoria_vrlt" in script, (
        "proposal versus actual-law negative-control regression absent"
    )
    for term in ("1%/2%/5%", "1%/2%/3%", "bell hooks", "Baudrillard", "Kropotkin"):
        assert term.casefold() in text.casefold(), (
            f"requested original-source or proposal detail omitted: {term}"
        )
    statuses = Counter(status for _, _, status, _, _ in rows)
    print(f"PASS: {len(rows)} distinct sourced/typed topic rows; "
          f"statuses {dict(sorted(statuses.items()))}; "
          "three fiscal Agda owners, one trade application and one TOE bridge; CI gates.")
    print("This is a coverage receipt, NOT a truth or Agda kernel receipt.")

if __name__ == "__main__":
    main()

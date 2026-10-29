#!/usr/bin/env python3
"""Static source/benefit-incidence contract for existing Woogaroo + Springfield work.

This asserts authoring consistency, chronology and typed anti-promotion gates.
It is not an execution of Agda, a reproduction of financial cash-flows,
a legal opinion, or an empirically paid benefit to any named politician.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "DASHI/Law/SensibLawWoogarooSecondThirdOrderIncidenceBridge20261027Exact.agda"
GAIN = ROOT / "DASHI/Law/SensibLawWoogarooGainLossSnowballAdapterExact.agda"
ROLL = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
DOCUMENT = ROOT / "Docs/SaveWoogarooForestGainLossSnowballAudit.md"
RESEARCH = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"


def main() -> None:
    assert all(p.exists() for p in (BRIDGE, GAIN, ROLL, DOCUMENT, RESEARCH))
    bridge, gain, roll, doc, note = [p.read_text(encoding="utf-8") for p in
                                    (BRIDGE, GAIN, ROLL, DOCUMENT, RESEARCH)]
    assert bridge.count("Source.mkNoDOISource") == 7
    assert bridge.count("Source.publicAttribution") == 7
    assert bridge.count("= incidence-path") == 9
    assert bridge.count("→ ⊥") == 9
    assert bridge.count("false refl") >= 9
    assert bridge.count("  incidence-cut ") == 7
    assert "record IncidenceCut : Set where" in bridge
    assert "sourceLevelValueOrOptionIdentified" in bridge
    assert "grossGainIdentified" not in bridge
    assert "sourceAcquisitionPriority" in bridge and "presentPayment : Bool" in bridge
    assert "signedFederalDecisionAndCounsel" in bridge
    assert "exactCouncilVillage2And3ChargeNotices" in bridge
    assert "signedCherishStocklandTitleDeed" in bridge
    assert "sameParcelEcologicalOffsetAndPublicSpend" in bridge


    # Canonical LAW owner and unmerged Cognition method donor remain distinct.
    assert "GainLossSnowballAdapterExact as GainLoss" in bridge
    assert "PostApprovalPoliticalGasBenefit20261027Exact as Post" in bridge
    assert "AttachmentSameObjectAudit20261027Exact as Attachment" in bridge
    assert "priorLocalPlanningOption = GainLoss.developerPrecinctOption" in bridge
    assert "priorEconomicIncidenceDebt = GainLoss.whoCapturesDevelopmentValue" in bridge
    assert "currentFederalGate = Post.developmentRegulatoryGate" in bridge
    assert "priorIndexedOwnerConsent = Attachment.separateConsentDocumentsOnlyIndexed" in bridge
    assert roll.count("import DASHI.Law.SensibLawWoogarooSecondThirdOrderIncidenceBridge20261027Exact") == 1
    assert "SpringfieldLayeredValueCaptureParetoExact" in bridge
    assert "ONE-WAY methodological donor" in bridge
    assert "import DASHI.Cognition.Springfield" not in bridge

    # Separate dated source objects, not combined cash or fabricated current receipts.
    for token in ("Queensland Competition Authority", "10000",
                  "313000", "2013-2018", "historical1994",
                  "27 October 2005", "Allgas", "Urban Utilities",
                  "4272/2020/ADP", "5547/2020/ADP",
                  "518 million", "303997515", "7.70",
                  "currentNetIncidencePayment", "false false false false false false"):
        assert token in bridge, token

    for guard in ("historicAssistanceNotNew2026Grant",
                  "citywideThresholdNotTwoVillas",
                  "indexNotPaidCharge", "uuSeparateFromCityCharge",
                  "orionValuationNotWoogarooUplift",
                  "blackRockHoldingNotParcelControl",
                  "gasPlanNotCurrentRevenue",
                  "politicalBenefitNotPersonalGain",
                  "approvalNotRealisation"):
        assert guard in bridge, guard

    # Updating October status must not silently delete September historical evidence.
    assert "federalDecisionStillOpen" in gain
    assert "currentFederalApprovalWithConditions" in gain
    assert "currentFederalLegalReviewExposure" in gain
    assert "federalApprovalNoticeAtom → true" in gain
    assert "federalSignedInstrumentAtom → false" in gain
    assert "currentInfrastructurePaymentsAtom → false" in gain

    assert "16 October 2026" in doc
    assert "approval with conditions" in doc
    assert "second and third order reconciliation" in doc
    assert "A$518m" in doc
    assert "2025 adopted rate resolution cannot be retro-applied" in note
    assert "Source" in note and "net public subsidy" in note
    print("PASS: 7 source entries, 9 typed incidence paths, 9 barriers, 7 open Pareto cuts; historical and current legal states distinct")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Source-contract / chronology sanity check for the separate Oct-27 attachment audit.

Static test only: verifies typed source roles and prevents model-transcript
promotion. No Agda compiler / legal outcome / cash-flow or lobbying causation.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LAW = ROOT / "DASHI/Law/SensibLawWoogarooAttachmentSameObjectAudit20261027Exact.agda"
ROLL = ROOT / "DASHI/Law/SensibLawWoogarooPreservationEverything.agda"
ROAD = ROOT / "DASHI/Law/SensibLawWoogarooLegalPriorityRoadmapExact.agda"
RESEARCH = ROOT / "docs/research/WoogarooPostApprovalGasHousingBenefitMaxCut20261027.md"


def main() -> None:
    assert all(f.exists() for f in (LAW, ROLL, ROAD, RESEARCH))
    law, roll, road, doc = (p.read_text("utf-8") for p in (LAW, ROLL, ROAD, RESEARCH))
    assert law.count("Source.mkNoDOISource") == 14
    assert law.count("Source.publicAttribution") == 14
    assert law.count("= bounded-claim") == 16
    assert law.count("→ ⊥") == 14
    assert law.count("false refl") == 16
    assert "import DASHI.Law.SensibLawWoogarooAttachmentSameObjectAudit20261027Exact" in roll
    assert "import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact as Post" in law
    assert "import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative" in law
    assert "exemptionAuditPriority" in road and "2018 QCA 266" in road
    assert "4272/2020/ADP" in road and "5547/2020/ADP" in road

    # Distinct legal cases and outcomes rather than generic veto or proved default.
    for symbol in ("cherish2018Planning", "aveoInterimOnly", "qcaVetoWrongType",
                   "interimNotFinalBreach", "qldLobbyNotCommonwealthDecision"):
        assert symbol in law, symbol
    assert "[2018] QCA 266" in law and "[2024] QCA 102" in law
    assert "March 2016" in law and "12 October 2018" in law
    assert "courtTextInMirror" in law and "originalSameObjectOpen" in law
    assert "16 January 2025" in law and "9 April 2025" in law and "10 April 2025" in law
    assert "stateStaffNotFederal" in law

    # Numeric denominators and different geographic/legal action identities.
    for value in ("1432", "770387", "25 years", "2300 sq m", "86 km", "2500",
                  "2026/10667", "801.3 ha", "178.7 ha", "1.44 GW"):
        assert value in law, value
    for gate in ("haffNotProjectFunding", "tenancyNotBailout", "municipalGasNotWDDP",
                 "referralNotApproval", "waterProposalNotPayment", "santosNameNotSantoroOwnership",
                 "adpApprovalNotConditionDischarge", "precinctNotADP",
                 "consentLabelNotTitle", "village3NumberNotTypo"):
        assert gate in law, gate
    assert "processed water" in law
    assert "Santos" in law and "Santo Santoro" in law
    assert "not a documentary witness" in doc
    assert "2018 QCA 266" in doc and "11 November 2026" in doc
    assert "2019/8575" in doc and "2026/10667" in doc
    assert "6243/2023/LAP" in doc and "4272/2020/ADP" in doc and "5547/2020/ADP" in doc
    assert "Land Owner\'s Consent" in doc and "Submission Consent" in doc
    assert "Original" in doc and "not a legal opinion" in doc
    print("PASS: 14 source roots + reused Atlas; 16 scoped claims; 14 no-promotion guards; 2024/2025 ADPs")


if __name__ == "__main__":
    main()

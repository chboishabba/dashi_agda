"""Source-contract regression for Woogaroo Springfield × 2026 federal gas policy.

This test checks repository source expressions and source-promotion limits.
It is not Agda kernel checking, evidence that gas prices fell, or evidence
of private instructions between gas producers and political parties.
Original historical, regulator and minister authors remain their own owners.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "DASHI/Governance/WoogarooGasNationalReservationPolicyBridge20261027Exact.agda"
ROLLUP = ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Everything.agda"
GOV = ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda"
WOO = ROOT / "DASHI/Law/SensibLawSpringfieldGasLobbyingOwnershipSnowballExact.agda"
AZURE = ROOT / "DASHI/Law/SensibLawAzureSpringfieldInducedGasDemandExact.agda"
APPROVAL = ROOT / "DASHI/Law/SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact.agda"


def test_existing_owner_imports_and_sibling_climate_reuse():
    s = BRIDGE.read_text()
    assert "import DASHI.Governance.ClimateGenealogyTypedCasesExact as Gas" in s
    assert "import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Woogaroo" in s
    assert "import DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact as Azure" in s
    assert "import DASHI.Law.SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact as Approval" in s
    assert "originalFirstNineNoGasPromotion = Approval.firstNineSpringfieldIdentityBridge" in s
    assert "reservationIntroducedOriginalOwner = Gas.octoberGasBillsIntroduced2026" in s
    assert "levyWordCollisionOriginalOwner = Gas.sameLevyWordDifferentLegalBases" in s
    assert "historicalSpringfieldAlliance = Woogaroo.springfieldGasAllianceReport" in s
    assert "actualAllgasNetworkLevelOwnership = Azure.allgasCurrentOwnership" in s
    assert "deidentifiedEndpointEvidence = Azure.azureDwellingIdentityObservation" in s
    assert "unpaidNetworkRevenueAmount = Azure.networkUtilisationResidual" in s
    assert "import DASHI.Governance.WoogarooGasNationalReservationPolicyBridge20261027Exact" in ROLLUP.read_text()
    assert "octoberGasBillsIntroduced2026" in GOV.read_text()
    assert "sameLevyWordDifferentLegalBases" in GOV.read_text()
    assert "springfieldGasAllianceReport" in WOO.read_text()
    assert "allgasCurrentOwnership" in AZURE.read_text()
    assert "firstNineSpringfieldIdentityBridge" in APPROVAL.read_text()


def test_march_one_nation_reservation_bill_motion_denominator_collision():
    s = BRIDGE.read_text()
    assert "2026-03-10" in s and "2026-03-12" in s
    assert "offshoreBill15Exports : March15PolicyObject" in s
    assert "marchMotion15Production : March15PolicyObject" in s
    assert "march15LegalBase offshoreBill15Exports = exportedOffshorePetroleumVolume" in s
    assert "march15LegalBase marchMotion15Production = allProductionVolume" in s
    assert "same15DifferentDenominators =" in s
    assert "INF.nonFactorabilityWitness" in s
    assert "samePrinted15DoesNotIdentifyLegalBase =" in s
    assert "INF.witnessRulesOutEveryFlatFactorisation same15DifferentDenominators" in s
    assert "NOT a binding gas-reservation Act" in s
    assert "NOT the native Act" in s or "not enacted" in s
    assert "Murray Watt moved debate procedure" in s


def test_policy_versions_and_producer_originals_not_multiplier_or_private_tasking():
    s = BRIDGE.read_text()
    actors = (
        "hansonMayPolicyPivot", "oneNationJuneOriginalPolicy", "senexMayReservationObjection",
        "senexSeptemberDetailedSubmission", "fedOctober2026Package",
        "fedOctoberRegulatoryLicenceLevy", "aemcAllgasMarch2026"
    )
    for a in actors:
        assert a + " = scoped-gas-receipt" in s
    assert "2026-05-21" in s and "2026-06-09" in s
    assert "2026-05-08" in s and "2026-09-24" in s and "2026-10-14" in s
    assert "2026-09-24" > "2026-09-10"  # semantic chronological guard
    assert "cannot retroactively cause earlier 10 September" in s
    assert "NAMED consultation source/tasking" in s
    assert "no named Senex/Hancock instruction" in s
    assert "NOT a proposed 25% export SALES ad valorem tax" in s
    assert "current Allgas" not in s or "Stonepeak" in s


def test_distinct_export_local_and_developer_layers():
    s = BRIDGE.read_text()
    m = re.search(r"data GasSystemLayer : Set where(.*?)data DistinctGasObject", s, re.S)
    assert m
    for term in ("exportLicensing", "domesticWholesaleProduction", "localDistributionAsset",
                 "householdRetailService", "housingDeveloperInclusion"):
        assert term + " : GasSystemLayer" in m.group(1)
    assert "exportLicenceNotLocalDistributionAsset ()" in s
    assert "distributionAssetNotDeveloperContract ()" in s
    assert "introducedIsNotAssented ()" in s
    assert "partyPivotIsNotCommencedSupply ()" in s


def test_15_field_positional_source_ceiling_never_promotes_woogaroo_profit():
    s = BRIDGE.read_text()
    r = s[s.index("record WoogarooGasPolicyBoundary : Set where"):s.index("open WoogarooGasPolicyBoundary public")]
    names = re.findall(r"^\s+(\w+) : Bool$", r, re.M)
    assert len(names) == 15
    start = s.index("canonicalWoogarooGasPolicyBoundary = woogaroo-gas-policy-boundary")
    stop = s.index("\n\n", start)
    vals = re.findall(r"\b(?:true|false)\b", s[start:stop])
    assert len(vals) == 15
    flags = dict(zip(names, vals))
    for k in ("original2004InfrastructureAllianceReported",
              "currentAllgasNetworkLevelStonepeakOwnerDocumented",
              "fixedAndThroughputNetworkTariffPossible",
              "originalMarch15ReservePositionRecorded",
              "MayJuneOneNationPivotOriginalPublisherPresent",
              "SenexMayAndSeptemberPolicyResponsePresent",
              "introducedOctoberFederalPackageDocumented"):
        assert flags[k] == "true", k
    for k in ("localExactMIRNDistributorAndRetailerAuthenticated",
              "upstreamLNGMoleculeToLocalConnectionMatched",
              "endpointSpecificRevenueMeasured",
              "SenexHancockToHansonExactOriginalPolicyInstructionVerified",
              "signedAndCommencedFederalSchemeVerified",
              "federalCostRecoveryLevyIs25PctExportValueTax",
              "SpringfieldLobbyistMeetingSubjectGasPaid",
              "measurableWoogarooBenefitCausedByFederalPolicy"):
        assert flags[k] == "false", k
    for k in ("noSpecificGasLobbyingPaid = refl",
              "noLocalMoleculeTransferPaid = refl",
              "noHancockSenexPartyTaskPaid = refl",
              "noPriceOutcomeProven = refl"):
        assert k in s

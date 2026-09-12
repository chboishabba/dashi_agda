from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawSpringfieldGasLobbyingOwnershipSnowballExact.agda": [
        "module DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact where",
        "azureDevelopmentGroupIdentity",
        "springfieldAzureEmploymentLineage",
        "springfieldAzureProjectPartnership",
        "azureLnpDonation2019A",
        "azureLnpDonation2019B",
        "springfieldRegisteredLobbyistMeeting2025",
        "springfieldEnergexGasAllianceLocator",
        "azureNameCollisionDoesNotPayIdentity",
        "formerEmploymentDoesNotCreateControl",
        "projectPartnershipDoesNotCreateCommonOwnership",
        "politicalDonationDoesNotCreateInfluence",
        "lobbyingMeetingDoesNotCreateDecisionOutcome",
        "infrastructureAllianceDoesNotCreateAssetOwnership",
        "secondaryGasReportDoesNotPayPrimaryAgreement",
        "gasAssetLineageResidual",
        "currentOwnershipResidual",
        "canonicalInfluenceSnowballBoundary",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact"
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Springfield gas/lobbying/ownership snowball static contract: OK")

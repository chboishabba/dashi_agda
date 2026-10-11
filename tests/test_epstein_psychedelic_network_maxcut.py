from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Cognition/EpsteinPsychedelicSourceAtlasExact.agda": [
        "EFTA02458524",
        "EFTA00814480",
        "EFTA01054265",
        "EFTA00957006",
        "EFTA00984429",
        "EFTA00865569",
        "Rick Doblin",
        "ibogaine",
        "scopolamine",
    ],
    "DASHI/Cognition/EpsteinPsychedelicNetworkEvidenceExact.agda": [
        "EvidenceGradedGenealogyCore",
        "directDocumentedTransfer",
        "fundingOrganisationalLink",
        "oneStrongEdgeDoesNotEstablishUniversalNetwork",
        "documentedInterestDoesNotEstablishAdministration",
    ],
    "DASHI/Cognition/EpsteinPsychedelicParetoSnowballExact.agda": [
        "SensibLawFiniteRequirementParetoFrontierExact",
        "GinoYuCorpus",
        "DoblinMAPSIntersection",
        "ScopolamineTrumpetSameObject",
        "paretoRoutingCreatesTruth",
    ],
    "DASHI/Cognition/EpsteinPsychedelicNetworkValidation.agda": [
        "canonicalEpsteinPsychedelicBoundary",
        "currentEpsteinPsychedelicRoute",
    ],
}


def test_epstein_psychedelic_network_surface_exists_and_keeps_boundaries():
    for rel, needles in EXPECTED.items():
        path = ROOT / rel
        assert path.exists(), f"missing production owner: {rel}"
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            assert needle in text, f"{needle!r} missing from {rel}"


def test_cognition_rollup_exports_epstein_psychedelic_network():
    rollup = (ROOT / "DASHI/Cognition/Everything.agda").read_text(encoding="utf-8")
    for module in EXPECTED:
        module_name = module.removesuffix(".agda").replace("/", ".")
        assert f"import {module_name}" in rollup

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Unified/GovernedFleetResidualTOEHandoffExact.agda"
VALIDATION = ROOT / "DASHI/Unified/GovernedFleetResidualTOEHandoffValidation.agda"
HYPER = ROOT / "DASHI/Unified/R559IbrahimFleetHyperfabricTOEExact.agda"
MANIFEST = ROOT / "DASHI/Unified/Fleet58ManifestAcquisitionExact.agda"
TOE = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
UNIFIER = ROOT / "DASHI/Unifier.agda"
UNIFIED = ROOT / "DASHI/Unified/Everything.agda"

def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(ROOT)}"
    return path.read_text(encoding="utf-8", errors="strict")

def test_final_handoff_reuses_current_canonical_owners() -> None:
    text = read(OWNER)
    for token in (
        "GovernedLegalWorkflowTOEBridgeExact",
        "R559IbrahimFleetHyperfabricTOEExact",
        "Fleet58ManifestAcquisitionExact",
        "NavierStokesBM2TOEConvergenceExact",
        "canonicalGovernedFleetResidualTOEHandoff",
    ):
        assert token in text

def test_fleet_partition_and_dispatch_wall_are_exact() -> None:
    owner = read(OWNER)
    manifest = read(MANIFEST)
    for token in (
        "fleetFormalGapCountIs58",
        "fleetDischargedFibresRemain584",
        "fleetContradictionGapsRemain44",
        "fleet58DoesNotIdentifyYMGate458",
        "namedManifestStillMissing",
        "perGapDispatchStillDisabled",
    ):
        assert token in owner
    assert "named58ManifestAcquired = false" in manifest
    assert "perGapDispatchEnabled = named58ManifestAcquired" in manifest

def test_current_fleet_hyperfabric_uses_equality_api() -> None:
    text = read(HYPER)
    for stale in (
        "Fleet.FleetEigenPriorityCreatesProof",
        "Fleet.FleetExternalCountCreatesFormalDischarge",
        "Fleet.FleetDischargedFibreRetargetPermission",
        "Fleet.FleetContradictionGapReclassificationPermission",
    ):
        assert stale not in text
    for token in (
        "Fleet.eigenvalueMagnitudeCreatesProofAuthority",
        "Fleet.externalCountCreatesFormalProof",
        "Fleet.dischargedFibresRemainDischarged",
        "Fleet.contradictionGapsRemainSeparate",
    ):
        assert token in text

def test_all_three_toe_facades_reach_same_handoff() -> None:
    assert "toeGovernedFleetResidualTOEHandoff" in read(TOE)
    assert "unifierGovernedFleetResidualTOEHandoff" in read(UNIFIER)
    assert "unifiedGovernedFleetResidualTOEHandoff" in read(UNIFIED)
    validation = read(VALIDATION)
    for token in (
        "toeHandoffMatchesOwner",
        "unifierHandoffMatchesOwner",
        "unifiedHandoffMatchesOwner",
    ):
        assert token in validation

def test_legal_authority_firewalls_reach_toe_root() -> None:
    text = read(TOE)
    for token in (
        "toeGovernedLegalCandidateDoesNotCreateAuthority",
        "toeGovernedCurrentValidityDoesNotCreateApplicability",
        "toeGovernedSemanticAdmissionDoesNotCreateLegalAuthority",
        "toeGovernedDocumentRoleDoesNotCreateLegalAuthority",
    ):
        assert token in text

def test_no_trust_escape_or_esd_import_in_new_owner() -> None:
    for path in (OWNER, VALIDATION):
        text = read(path)
        for token in ("postulate", "allow-unsolved-metas", "TERMINATING", "NO_POSITIVITY_CHECK", "{!!}"):
            assert token not in text
        assert "import dashi_digital_esd" not in text.lower()
        assert "import DASHI.ESD" not in text

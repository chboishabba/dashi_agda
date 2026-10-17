from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ATTACH = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29VendoredSourceAttachmentExact.agda"
TAIL = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29TailWeakSimulationExact.agda"
NOTICE = ROOT / "vendor" / "meta-introspector-aok" / "NOTICE.md"
LICENSE = ROOT / "vendor" / "meta-introspector-aok" / "LICENSE.AGPL-3.0"
REPLAY = ROOT / "scripts" / "verify_goldbach30_29_replay.py"


def test_attachment_receipt_is_fail_closed():
    text = ATTACH.read_text()
    assert "ff3f10a3e4c72771ac415a7f4bfb70a209478025" in text
    assert "ff748e1d68bf01d19e0c0998f6ac8d3a1c73e2f3" in text
    assert "782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b" in text
    assert "0ad25db4bd1d86c452db3f9602ccdbe172438f52" in text
    assert "exactProgramSourceObjectsVendored = true" in text
    assert "sourceDrivenFractranReplayAvailable = true" in text
    assert "semanticMainLoopsDuplicateDetected = true" in text
    assert "semanticBuildAuthorityPaid = false" in text
    assert "crossProverProofTransportPaid = false" in text
    assert "concreteFractranCheckpointFormalAttachmentPaid = false" in text
    assert "licenseNoticePresent = true" in text
    assert "exactLicenseBlobVendored = false" in text


def test_tail_weak_simulation_records_stuttering_shape():
    text = TAIL.read_text()
    assert "TailPhase" in text
    assert "oldToNewPhase" in text
    assert "oldTransferPairMatchesNewTransferPair" in text
    assert "oldTerminalStepMatchesThreeNewSteps" in text
    assert "weakTailConsumerPreserved" in text
    assert "wholeMachineWeakBisimulationPaid = false" in text


def test_vendor_notice_and_license_surface_present():
    assert NOTICE.exists()
    assert LICENSE.exists()
    notice = NOTICE.read_text()
    assert "Mike Dupont / meta-introspector" in notice
    assert "AGPL-3.0" in notice
    assert "does **not** claim" in notice
    license_text = LICENSE.read_text()
    assert "GNU AFFERO GENERAL PUBLIC LICENSE" in license_text
    assert "Version 3, 19 November 2007" in license_text
    assert "0ad25db4bd1d86c452db3f9602ccdbe172438f52" in license_text
    assert "does not claim to" in license_text
    assert "byte-identical" in license_text


def test_replay_consumes_vendored_sources_directly():
    text = REPLAY.read_text()
    assert "VENDOR29_PROGRAM" in text
    assert "VENDOR30_PROGRAM" in text
    assert "extract_fractran_program" in text
    assert "fractran_step" in text
    assert "verify_direct_fractran_step_bridge" in text

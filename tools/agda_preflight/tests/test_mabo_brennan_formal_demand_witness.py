from pathlib import Path


MODULE = Path("DASHI/Law/SensibLawMaboBrennanRecognitionFormalDemandExact.agda")

DEMAND_REF = "formal-demand:mabo:sha256:13390b7c3eff34f6c4f55344f752c2d2cef0297faa0b8d88c7531524d3a98b00"
OBLIGATION_REF = "legal-obligation:sha256:0e2069ea33d2b65d1217f6d968ec68c40b70a7cccfb2657465d5e744d88a3203"
RESIDUAL_REF = "legal-residual:sha256:b4d23fa12e52365ad69824b861cfbd00338e850e2e83ab3083f85be001042801"
PNF_REVISION_REF = "pnf-factor-revision:real-matter:mabo:brennan:recognition:v1"
SOURCE_REVISION_REF = "external-source-revision:sha256:ba30975a1421963fc13c8e2a40c58d466c49c8236db4676557942a5ed3fad7a0"
STATEMENT_DIGEST = "sha256:a5577814404b3140006d54df57f46e49c24f55cf63701c2569ff38a5c8b9e224"


def source() -> str:
    return MODULE.read_text(encoding="utf-8")


def test_live_mabo_demand_coordinates_are_pinned_exactly() -> None:
    text = source()
    for value in (
        DEMAND_REF,
        OBLIGATION_REF,
        RESIDUAL_REF,
        PNF_REVISION_REF,
        SOURCE_REVISION_REF,
        STATEMENT_DIGEST,
    ):
        assert text.count(f'"{value}"') == 1


def test_witness_reuses_exact_reviewed_brennan_and_recognition_owners() -> None:
    text = source()
    assert "Mabo.brennanSurvivalProposition" in text
    assert "Mabo.brennanDawsonResidual" in text
    assert "Mabo.searchTargetsRecognitionBasis" in text
    assert "Foothold.canonicalMaboFoothold" in text
    assert "Foothold.maboRecognisesRatherThanLegislativelyCreates" in text


def test_truth_remains_unresolved_and_no_authority_is_promoted() -> None:
    text = source()
    assert "Status.truthUnresolved" in text
    assert "reviewedTruthStatusIsUnresolved" in text
    assert "createsJudicialAuthority = false" in text
    assert "createsLegalAuthority = false" in text
    assert "promotesApplicability = false" in text
    assert "promotesClaimTruth = false" in text
    assert "formalPremiseOnly = true" in text


def test_source_comments_keep_kernel_proof_boundary_narrow() -> None:
    text = source()
    assert "does not prove judicial truth" in text
    assert "does not establish legal applicability" in text
    assert "does not promote claim truth" in text

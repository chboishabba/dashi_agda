from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_ddtl4_same_spv_finance_to_site_mapping_is_paid_but_not_gpu_identity():
    text = (ROOT / "DASHI/Economics/AICoreWeaveDDTL4PolarisForgeMapping20261016Exact.agda").read_text(encoding="utf-8")
    for marker in [
        "sameBorrowerSPVIsPaid",
        "polarisForge1SiteIdentityPaid",
        "building2And3LeaseLinkPaid",
        "exactFinancedMWStillOpen",
        "gpuGenerationStillOpen",
        "customerIdentityStillOpen",
    ]:
        assert marker in text

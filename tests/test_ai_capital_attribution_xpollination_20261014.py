from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_aggregate_customer_cash_realisation():
    require("DASHI/Economics/AICoreWeaveAggregateCustomerCashRealisation20261014Exact.agda", [
        "operatingCashFlowMillionUSDIs3663",
        "accountsReceivableDecreaseMillionUSDIs628",
        "aggregateCustomerCashReceiptObserved",
        "aggregateCashDoesNotIdentifyNamedPayer",
        "aggregateCashDoesNotCreateTerminalIndependence",
    ])


def test_stack_layer_return_noncollapse():
    require("DASHI/Economics/AIInfrastructureStackReturnNonCollapse20261014Exact.agda", [
        "landlordRecognisedRevenueAndTenantNegativeSpreadCoexist",
        "landlordPositiveCoordinateDoesNotCreateTenantPositiveReturn",
        "tenantNegativeSpreadDoesNotCreateLandlordFailure",
    ])


def test_policy_reviewed_causal_attribution_gate():
    require("DASHI/Economics/AIPolicyReviewedCausalAttribution20261014Exact.agda", [
        "GenericHumanReviewReceipt",
        "ExactReviewItemBinding",
        "reviewDoesNotCreateIdentification",
        "identificationDoesNotCreateReview",
        "reviewedCausalBridgeDoesNotCreateIntentionalCapture",
    ])


def test_rollup_imports_attribution_xpollination():
    require("DASHI/Economics/AIEntanglementEverything2026.agda", [
        "AICoreWeaveAggregateCustomerCashRealisation20261014Exact",
        "AIInfrastructureStackReturnNonCollapse20261014Exact",
        "AIPolicyReviewedCausalAttribution20261014Exact",
    ])

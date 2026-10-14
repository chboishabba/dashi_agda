from agda_preflight.discovery import classify_surface_role


def test_only_numbered_rounds_are_historical_snapshots():
    assert classify_surface_role("DASHI.Physics.Closure.FooRound12Exact") == "historical_snapshot"
    assert classify_surface_role("DASHI.Core.RoundTrip") == "canonical"

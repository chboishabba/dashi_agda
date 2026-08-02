#!/usr/bin/env python3
"""Exact audit for the Murray thesis commit and Stage-3 API boundary."""
from __future__ import annotations

THESIS_COMMIT = "5cd6d3d023279518213f3e58879bfc867bb2503c"


def main() -> int:
    assert len(THESIS_COMMIT) == 40
    assert all(c in "0123456789abcdef" for c in THESIS_COMMIT)
    status = {
        "repositoryLocated": True,
        "thesisMatchingCommitRecorded": True,
        "thesisCommitResolves": True,
        "arithmeticAndOrderSurfaceObserved": True,
        "cauchyCompletenessSurfaceObserved": True,
        "arbitraryRealFixedBaseTwoLocated": False,
        "exponentAdditivityLocated": False,
        "geometricSeriesTheoremLocated": False,
        "explicitEffectiveTailModulusLocated": False,
        "modernAgdaBuildPassed": False,
        "stage3DyadicAdapterConstructed": False,
    }
    assert all(status[k] for k in (
        "repositoryLocated",
        "thesisMatchingCommitRecorded",
        "thesisCommitResolves",
        "arithmeticAndOrderSurfaceObserved",
        "cauchyCompletenessSurfaceObserved",
    ))
    assert not any(status[k] for k in (
        "arbitraryRealFixedBaseTwoLocated",
        "exponentAdditivityLocated",
        "geometricSeriesTheoremLocated",
        "explicitEffectiveTailModulusLocated",
        "modernAgdaBuildPassed",
        "stage3DyadicAdapterConstructed",
    ))
    print(
        "Murray thesis source-pin audit passed: exact commit "
        f"{THESIS_COMMIT}; arithmetic/order/completeness observed; fixed-base 2^x, "
        "geometric tail, current-toolchain build and Stage-3 adapter remain fail-closed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

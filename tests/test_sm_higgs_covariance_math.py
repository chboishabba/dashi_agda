from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import sys
from typing import Any, Callable

import pytest


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import sm_higgs_covariance_math as covmath  # type: ignore[import-not-found]


def _function(*names: str) -> Callable[..., Any]:
    for name in names:
        candidate = getattr(covmath, name, None)
        if callable(candidate):
            return candidate
    raise AssertionError(f"missing covariance helper function; tried {', '.join(names)}")


def _validate_positive_definite(matrix: list[list[float]]) -> Any:
    return _function(
        "validate_positive_definite_matrix",
        "validate_covariance_matrix",
        "assert_positive_definite",
        "assert_covariance_positive_definite",
    )(matrix)


def _chi2(
    observed: list[float],
    expected: list[float],
    covariance: list[list[float]],
) -> float:
    value = _function(
        "covariant_chi2",
        "compute_covariant_chi2",
        "compute_chi2",
        "chi2",
    )(observed, expected, covariance)
    if isinstance(value, dict):
        value = value.get("chi2")
    return float(value)


def _canonical_digest(payload: dict[str, Any]) -> str:
    value = _function(
        "canonical_json_digest",
        "stable_canonical_json_digest",
        "sha256_canonical_json",
        "stable_digest",
    )(payload)
    if isinstance(value, dict):
        value = value.get("sha256") or value.get("digest")
    assert isinstance(value, str)
    return value


def _independent_canonical_digest(payload: dict[str, Any]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def test_positive_definite_matrix_is_accepted() -> None:
    matrix = [
        [4.0, 1.0, 0.5],
        [1.0, 3.0, 0.25],
        [0.5, 0.25, 2.0],
    ]

    result = _validate_positive_definite(matrix)

    if isinstance(result, bool):
        assert result is True
    elif isinstance(result, dict):
        assert result.get("positive_definite", True) is True
        assert result.get("rank", 3) == 3


def test_non_symmetric_covariance_is_rejected() -> None:
    matrix = [
        [1.0, 0.25],
        [0.5, 1.0],
    ]

    with pytest.raises(ValueError, match="symmet|covariance|positive|definite"):
        _validate_positive_definite(matrix)


def test_singular_covariance_is_rejected() -> None:
    matrix = [
        [1.0, 2.0],
        [2.0, 4.0],
    ]

    with pytest.raises(ValueError, match="singular|positive|definite|rank"):
        _validate_positive_definite(matrix)


def test_covariant_chi2_uses_full_inverse_covariance() -> None:
    observed = [2.0, 5.0]
    expected = [1.0, 3.0]
    covariance = [
        [2.0, 0.5],
        [0.5, 1.0],
    ]

    assert math.isclose(
        _chi2(observed, expected, covariance),
        4.0,
        rel_tol=0.0,
        abs_tol=1.0e-12,
    )


def test_canonical_json_digest_is_stable_over_key_order() -> None:
    left = {
        "observable": "pT_yy",
        "bins": [0.0, 10.0, 20.0],
        "covariance": [[1.0, 0.1], [0.1, 2.0]],
        "metadata": {"doi": "10.17182/hepdata.example.v1/t1", "version": 1},
    }
    right = {
        "metadata": {"version": 1, "doi": "10.17182/hepdata.example.v1/t1"},
        "covariance": [[1.0, 0.1], [0.1, 2.0]],
        "bins": [0.0, 10.0, 20.0],
        "observable": "pT_yy",
    }

    digest = _canonical_digest(left)

    assert digest == _canonical_digest(right)
    assert digest == _independent_canonical_digest(left)

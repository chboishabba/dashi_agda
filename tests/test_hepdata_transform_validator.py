from __future__ import annotations

from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.hepdata_transform_validator import (  # type: ignore[import-not-found]
    TRANSFORM_VOCAB,
    validate_transform_choice,
)


def test_transform_vocab_is_closed() -> None:
    assert set(TRANSFORM_VOCAB) == {
        "raw",
        "gradient",
        "whitened",
        "other-declared",
    }


def test_validate_transform_choice_returns_full_spec() -> None:
    spec = validate_transform_choice("raw")

    assert spec.name == "raw"
    assert spec.preserves_metric_geometry is True
    assert spec.requires_regularization is False
    assert spec.comparable_group == "native"
    assert "metric_ready=true" in spec.preconditions


def test_invalid_transform_rejected_without_alias_fallback() -> None:
    with pytest.raises(ValueError, match="undeclared transform"):
        validate_transform_choice("grad")

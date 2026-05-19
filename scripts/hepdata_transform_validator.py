#!/usr/bin/env python3
from __future__ import annotations

try:
    from hepdata_projection_contract import (  # type: ignore[import-not-found]
        TRANSFORM_VOCAB,
        TransformKind,
        TransformSpec,
    )
except ModuleNotFoundError:
    from scripts.hepdata_projection_contract import (
        TRANSFORM_VOCAB,
        TransformKind,
        TransformSpec,
    )


def validate_transform_choice(transform_name: str) -> TransformSpec:
    """
    Validate that a future projection lane selected one declared transform.

    This helper is intentionally vocabulary-only:
    it does not inspect any measurement surface and it does not perform
    projection.
    """

    if transform_name not in TRANSFORM_VOCAB:
        raise ValueError(
            f"undeclared transform: {transform_name!r}. "
            "Expected one of: "
            + ", ".join(sorted(TRANSFORM_VOCAB))
        )
    return TRANSFORM_VOCAB[transform_name]  # type: ignore[index]


__all__ = [
    "TransformKind",
    "TransformSpec",
    "TRANSFORM_VOCAB",
    "validate_transform_choice",
]

"""Small covariance-aware comparison helpers for SM Higgs adapters.

The functions here are deliberately CLI-neutral: callers load or prepare
vectors/matrices, validate covariance structure, then compute chi-square
statistics.  The implementation uses only the Python standard library so it
can run in the repo's lightweight validation environments.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


DEFAULT_SYMMETRY_TOLERANCE = 1.0e-10
DEFAULT_POSITIVE_DEFINITE_TOLERANCE = 1.0e-14


class CovarianceMathError(ValueError):
    """Base class for covariance comparison errors."""


class NumericLoadError(CovarianceMathError):
    """Raised when vector or matrix payloads cannot be loaded as numbers."""


class ShapeError(CovarianceMathError):
    """Raised when vector or matrix dimensions are incompatible."""


class CovarianceValidationError(CovarianceMathError):
    """Raised when a covariance matrix fails structural validation."""


class PositiveDefiniteError(CovarianceValidationError):
    """Raised when Cholesky factorization detects a non-positive pivot."""


@dataclass(frozen=True)
class CovarianceValidation:
    """Validation result for a covariance matrix."""

    dimension: int
    max_asymmetry: float
    cholesky_diagonal: tuple[float, ...]
    determinant_from_cholesky: float


@dataclass(frozen=True)
class ChiSquareResult:
    """Covariance-aware chi-square comparison result."""

    observed: tuple[float, ...]
    expected: tuple[float, ...]
    residual: tuple[float, ...]
    chi2: float
    dof: int
    reduced_chi2: float
    covariance_validation: CovarianceValidation


def coerce_vector(values: Iterable[Any], *, name: str = "vector") -> tuple[float, ...]:
    """Convert a one-dimensional iterable to a tuple of finite floats."""

    if isinstance(values, (str, bytes)):
        raise NumericLoadError(f"{name} must be a sequence of numbers, not a string")

    result: list[float] = []
    for index, value in enumerate(values):
        if isinstance(value, (list, tuple, dict)):
            raise NumericLoadError(f"{name}[{index}] is not a scalar number")
        try:
            number = float(value)
        except (TypeError, ValueError) as exc:
            raise NumericLoadError(f"{name}[{index}] cannot be parsed as a number") from exc
        if not math.isfinite(number):
            raise NumericLoadError(f"{name}[{index}] is not finite")
        result.append(number)

    if not result:
        raise NumericLoadError(f"{name} must not be empty")
    return tuple(result)


def coerce_matrix(values: Iterable[Iterable[Any]], *, name: str = "matrix") -> tuple[tuple[float, ...], ...]:
    """Convert a two-dimensional iterable to a rectangular tuple matrix."""

    if isinstance(values, (str, bytes)):
        raise NumericLoadError(f"{name} must be a sequence of rows, not a string")

    rows: list[tuple[float, ...]] = []
    expected_width: int | None = None
    for row_index, row in enumerate(values):
        try:
            coerced_row = coerce_vector(row, name=f"{name}[{row_index}]")
        except TypeError as exc:
            raise NumericLoadError(f"{name}[{row_index}] is not an iterable row") from exc
        if expected_width is None:
            expected_width = len(coerced_row)
        elif len(coerced_row) != expected_width:
            raise ShapeError(
                f"{name} is ragged: row 0 has width {expected_width}, "
                f"row {row_index} has width {len(coerced_row)}"
            )
        rows.append(coerced_row)

    if not rows:
        raise NumericLoadError(f"{name} must not be empty")
    return tuple(rows)


def load_json_payload(path: str | Path) -> Any:
    """Load a JSON payload from disk."""

    try:
        with Path(path).open("r", encoding="utf-8") as handle:
            return json.load(handle)
    except OSError as exc:
        raise NumericLoadError(f"could not read JSON payload {path!s}") from exc
    except json.JSONDecodeError as exc:
        raise NumericLoadError(f"could not parse JSON payload {path!s}") from exc


def load_json_vector(path: str | Path, *, key: str | None = None, name: str = "vector") -> tuple[float, ...]:
    """Load a vector from a JSON array or from a named JSON object field."""

    payload = load_json_payload(path)
    if key is not None:
        try:
            payload = payload[key]
        except (KeyError, TypeError) as exc:
            raise NumericLoadError(f"JSON payload {path!s} has no vector key {key!r}") from exc
    return coerce_vector(payload, name=name)


def load_json_matrix(path: str | Path, *, key: str | None = None, name: str = "matrix") -> tuple[tuple[float, ...], ...]:
    """Load a matrix from a JSON nested array or from a named JSON object field."""

    payload = load_json_payload(path)
    if key is not None:
        try:
            payload = payload[key]
        except (KeyError, TypeError) as exc:
            raise NumericLoadError(f"JSON payload {path!s} has no matrix key {key!r}") from exc
    return coerce_matrix(payload, name=name)


def load_csv_matrix(path: str | Path, *, name: str = "matrix") -> tuple[tuple[float, ...], ...]:
    """Load a numeric matrix from a comma-separated file without headers."""

    try:
        with Path(path).open("r", encoding="utf-8", newline="") as handle:
            rows = [row for row in csv.reader(handle) if row]
    except OSError as exc:
        raise NumericLoadError(f"could not read CSV matrix {path!s}") from exc
    return coerce_matrix(rows, name=name)


def load_csv_vector(path: str | Path, *, name: str = "vector") -> tuple[float, ...]:
    """Load a numeric vector from a CSV file.

    A single row is interpreted as the vector.  Multiple one-column rows are
    interpreted as a column vector.
    """

    matrix = load_csv_matrix(path, name=name)
    if len(matrix) == 1:
        return coerce_vector(matrix[0], name=name)
    if all(len(row) == 1 for row in matrix):
        return tuple(row[0] for row in matrix)
    raise ShapeError(f"{name} CSV must be one row or one column")


def validate_same_length(left: Sequence[float], right: Sequence[float], *, left_name: str, right_name: str) -> None:
    """Raise if two vectors do not have the same length."""

    if len(left) != len(right):
        raise ShapeError(f"{left_name} length {len(left)} does not match {right_name} length {len(right)}")


def validate_square_matrix(matrix: Sequence[Sequence[float]], *, name: str = "covariance") -> int:
    """Validate that a matrix is square and return its dimension."""

    if not matrix:
        raise CovarianceValidationError(f"{name} must not be empty")
    dimension = len(matrix)
    for row_index, row in enumerate(matrix):
        if len(row) != dimension:
            raise ShapeError(f"{name} row {row_index} has width {len(row)}; expected {dimension}")
    return dimension


def max_symmetric_difference(matrix: Sequence[Sequence[float]]) -> float:
    """Return the maximum absolute asymmetry |a_ij - a_ji|."""

    dimension = len(matrix)
    maximum = 0.0
    for i in range(dimension):
        for j in range(i + 1, dimension):
            maximum = max(maximum, abs(matrix[i][j] - matrix[j][i]))
    return maximum


def validate_symmetric(
    matrix: Sequence[Sequence[float]],
    *,
    tolerance: float = DEFAULT_SYMMETRY_TOLERANCE,
    name: str = "covariance",
) -> float:
    """Validate matrix symmetry within tolerance and return max asymmetry."""

    maximum = max_symmetric_difference(matrix)
    if maximum > tolerance:
        raise CovarianceValidationError(
            f"{name} is not symmetric within tolerance {tolerance:g}; max asymmetry {maximum:g}"
        )
    return maximum


def cholesky_decomposition(
    matrix: Sequence[Sequence[float]],
    *,
    tolerance: float = DEFAULT_POSITIVE_DEFINITE_TOLERANCE,
    name: str = "covariance",
) -> tuple[tuple[float, ...], ...]:
    """Compute a lower-triangular Cholesky factor for a positive-definite matrix."""

    dimension = validate_square_matrix(matrix, name=name)
    lower = [[0.0 for _ in range(dimension)] for _ in range(dimension)]

    for i in range(dimension):
        for j in range(i + 1):
            partial = sum(lower[i][k] * lower[j][k] for k in range(j))
            if i == j:
                pivot = matrix[i][i] - partial
                if pivot <= tolerance:
                    raise PositiveDefiniteError(
                        f"{name} is not positive definite at pivot {i}: {pivot:g} <= {tolerance:g}"
                    )
                lower[i][j] = math.sqrt(pivot)
            else:
                lower[i][j] = (matrix[i][j] - partial) / lower[j][j]

    return tuple(tuple(row) for row in lower)


def validate_covariance(
    covariance: Iterable[Iterable[Any]],
    *,
    expected_dimension: int | None = None,
    symmetry_tolerance: float = DEFAULT_SYMMETRY_TOLERANCE,
    positive_tolerance: float = DEFAULT_POSITIVE_DEFINITE_TOLERANCE,
    name: str = "covariance",
) -> CovarianceValidation:
    """Validate square, symmetric, positive-definite covariance input."""

    matrix = coerce_matrix(covariance, name=name)
    dimension = validate_square_matrix(matrix, name=name)
    if expected_dimension is not None and dimension != expected_dimension:
        raise ShapeError(f"{name} dimension {dimension} does not match expected dimension {expected_dimension}")
    max_asymmetry = validate_symmetric(matrix, tolerance=symmetry_tolerance, name=name)
    cholesky = cholesky_decomposition(matrix, tolerance=positive_tolerance, name=name)
    diagonal = tuple(cholesky[i][i] for i in range(dimension))
    determinant = 1.0
    for value in diagonal:
        determinant *= value * value
    return CovarianceValidation(
        dimension=dimension,
        max_asymmetry=max_asymmetry,
        cholesky_diagonal=diagonal,
        determinant_from_cholesky=determinant,
    )


def residual_vector(observed: Iterable[Any], expected: Iterable[Any]) -> tuple[float, ...]:
    """Return observed - expected after numeric coercion and shape validation."""

    observed_vector = coerce_vector(observed, name="observed")
    expected_vector = coerce_vector(expected, name="expected")
    validate_same_length(observed_vector, expected_vector, left_name="observed", right_name="expected")
    return tuple(left - right for left, right in zip(observed_vector, expected_vector))


def solve_cholesky(lower: Sequence[Sequence[float]], vector: Sequence[float]) -> tuple[float, ...]:
    """Solve L L^T x = vector for x, where L is lower triangular."""

    dimension = len(lower)
    if len(vector) != dimension:
        raise ShapeError(f"vector length {len(vector)} does not match Cholesky dimension {dimension}")

    y = [0.0 for _ in range(dimension)]
    for i in range(dimension):
        partial = sum(lower[i][k] * y[k] for k in range(i))
        y[i] = (vector[i] - partial) / lower[i][i]

    x = [0.0 for _ in range(dimension)]
    for i in range(dimension - 1, -1, -1):
        partial = sum(lower[k][i] * x[k] for k in range(i + 1, dimension))
        x[i] = (y[i] - partial) / lower[i][i]

    return tuple(x)


def chi_square_from_residual(
    residual: Iterable[Any],
    covariance: Iterable[Iterable[Any]],
    *,
    fitted_parameters: int = 0,
    symmetry_tolerance: float = DEFAULT_SYMMETRY_TOLERANCE,
    positive_tolerance: float = DEFAULT_POSITIVE_DEFINITE_TOLERANCE,
) -> tuple[float, int, float, CovarianceValidation]:
    """Compute r^T Sigma^-1 r and degrees-of-freedom metadata."""

    residual = coerce_vector(residual, name="residual")
    if fitted_parameters < 0:
        raise ShapeError("fitted_parameters must be non-negative")
    dof = len(residual) - fitted_parameters
    if dof <= 0:
        raise ShapeError(f"degrees of freedom must be positive; got {dof}")

    matrix = coerce_matrix(covariance, name="covariance")
    validation = validate_covariance(
        matrix,
        expected_dimension=len(residual),
        symmetry_tolerance=symmetry_tolerance,
        positive_tolerance=positive_tolerance,
    )
    lower = cholesky_decomposition(matrix, tolerance=positive_tolerance, name="covariance")
    solved = solve_cholesky(lower, residual)
    chi2 = sum(left * right for left, right in zip(residual, solved))
    return chi2, dof, chi2 / dof, validation


def covariance_chi_square(
    observed: Iterable[Any],
    expected: Iterable[Any],
    covariance: Iterable[Iterable[Any]],
    *,
    fitted_parameters: int = 0,
    symmetry_tolerance: float = DEFAULT_SYMMETRY_TOLERANCE,
    positive_tolerance: float = DEFAULT_POSITIVE_DEFINITE_TOLERANCE,
) -> ChiSquareResult:
    """Compute a covariance-aware chi-square result for observed and expected vectors."""

    observed_vector = coerce_vector(observed, name="observed")
    expected_vector = coerce_vector(expected, name="expected")
    validate_same_length(observed_vector, expected_vector, left_name="observed", right_name="expected")
    residual = tuple(left - right for left, right in zip(observed_vector, expected_vector))
    chi2, dof, reduced_chi2, validation = chi_square_from_residual(
        residual,
        covariance,
        fitted_parameters=fitted_parameters,
        symmetry_tolerance=symmetry_tolerance,
        positive_tolerance=positive_tolerance,
    )
    return ChiSquareResult(
        observed=observed_vector,
        expected=expected_vector,
        residual=residual,
        chi2=chi2,
        dof=dof,
        reduced_chi2=reduced_chi2,
        covariance_validation=validation,
    )


def canonical_json_bytes(payload: Any) -> bytes:
    """Serialize JSON-like payloads into deterministic UTF-8 bytes."""

    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    """Return the SHA-256 hex digest for bytes."""

    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    """Return the SHA-256 hex digest for UTF-8 text."""

    return sha256_bytes(text.encode("utf-8"))


def sha256_json(payload: Any) -> str:
    """Return the SHA-256 hex digest of a canonical JSON payload."""

    return sha256_bytes(canonical_json_bytes(payload))


def canonical_json_digest(payload: Any) -> str:
    """Compatibility alias for deterministic JSON SHA-256 digests."""

    return sha256_json(payload)


stable_canonical_json_digest = canonical_json_digest
sha256_canonical_json = canonical_json_digest
stable_digest = canonical_json_digest


def sha256_file(path: str | Path, *, chunk_size: int = 1024 * 1024) -> str:
    """Return the SHA-256 hex digest of a file."""

    digest = hashlib.sha256()
    try:
        with Path(path).open("rb") as handle:
            for chunk in iter(lambda: handle.read(chunk_size), b""):
                digest.update(chunk)
    except OSError as exc:
        raise NumericLoadError(f"could not read file for digest {path!s}") from exc
    return digest.hexdigest()


def result_as_dict(result: ChiSquareResult) -> dict[str, Any]:
    """Convert a chi-square result into a deterministic JSON-ready mapping."""

    validation = result.covariance_validation
    return {
        "observed": list(result.observed),
        "expected": list(result.expected),
        "residual": list(result.residual),
        "chi2": result.chi2,
        "dof": result.dof,
        "reduced_chi2": result.reduced_chi2,
        "covariance_validation": {
            "dimension": validation.dimension,
            "max_asymmetry": validation.max_asymmetry,
            "cholesky_diagonal": list(validation.cholesky_diagonal),
            "determinant_from_cholesky": validation.determinant_from_cholesky,
        },
    }


def validate_positive_definite_matrix(matrix: Iterable[Iterable[Any]]) -> dict[str, Any]:
    """Compatibility wrapper returning JSON-ready covariance validation metadata."""

    validation = validate_covariance(matrix)
    return {
        "positive_definite": True,
        "rank": validation.dimension,
        "dimension": validation.dimension,
        "max_asymmetry": validation.max_asymmetry,
        "determinant_from_cholesky": validation.determinant_from_cholesky,
        "cholesky_diagonal": list(validation.cholesky_diagonal),
    }


validate_covariance_matrix = validate_positive_definite_matrix
assert_positive_definite = validate_positive_definite_matrix
assert_covariance_positive_definite = validate_positive_definite_matrix


def covariant_chi2(
    observed: Iterable[Any],
    expected: Iterable[Any],
    covariance: Iterable[Iterable[Any]],
) -> dict[str, Any]:
    """Compatibility wrapper returning the full covariance chi-square payload."""

    return result_as_dict(covariance_chi_square(observed, expected, covariance))


compute_covariant_chi2 = covariant_chi2
compute_chi2 = covariant_chi2
chi2 = covariant_chi2

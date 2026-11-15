#!/usr/bin/env python3
"""Synthetic MP sanity check. NOT observed S&P 500 data or PNF evidence."""
import json
import numpy as np

def spectrum(x):
    n, p = x.shape
    x = x - x.mean(axis=0)
    sd = np.sqrt(np.sum(x*x, axis=0) / (n-1))
    if np.any(sd == 0):
        raise ValueError("constant column")
    c = (x/sd).T @ (x/sd) / (n-1)
    eigenvalues = np.linalg.eigvalsh(c)
    upper = (1 + np.sqrt(p/(n-1)))**2
    mask = (eigenvalues > 0) & (eigenvalues <= upper)
    cleaned = eigenvalues.copy()
    if mask.any():
        cleaned[mask] = eigenvalues[mask].mean()
    assert np.allclose(c, c.T, atol=1e-12)
    assert abs(np.trace(c) - p) < 1e-8
    assert eigenvalues.min() > -1e-8
    assert cleaned.min() > -1e-8
    # Spectral clipping preserves PSD but generally does NOT preserve the
    # correlation diagonal. Explicit congruence is a separate operation.
    eigvecs = np.linalg.eigh(c)[1]
    cleaned_cov = (eigvecs * cleaned) @ eigvecs.T
    raw_diag_error = float(np.max(np.abs(np.diag(cleaned_cov) - 1)))
    d = np.diag(cleaned_cov)
    assert np.all(d > 0), "diagonal normalization needs strictly positive diagonal"
    normalized = cleaned_cov / np.sqrt(np.outer(d, d))
    assert np.min(np.linalg.eigvalsh(normalized)) >= -1e-8
    assert np.max(np.abs(np.diag(normalized) - 1)) < 1e-8
    return {
        "raw_cleaned_max_diagonal_error": raw_diag_error,
        "normalized_min_eigenvalue": float(np.linalg.eigvalsh(normalized)[0]),
        "normalized_max_diagonal_error": float(np.max(np.abs(np.diag(normalized)-1))),
        "max_eigenvalue": float(eigenvalues[-1]),
        "min_eigenvalue": float(eigenvalues[0]),
        "above_MP_edge": int(np.count_nonzero(eigenvalues > upper)),
        "trace": float(np.trace(c)),
        "cleaned_min_eigenvalue": float(cleaned.min()),
        "cleaned_trace": float(cleaned.sum()),
        "cleaned_unit_diagonal_not_guaranteed": True,
    }

def main():
    seed, n, p, rho = 20261109, 200, 120, 0.25
    rng = np.random.default_rng(seed)
    null = rng.normal(size=(n,p))
    common = np.sqrt(rho)*rng.normal(size=(n,1)) + np.sqrt(1-rho)*rng.normal(size=(n,p))
    shuffled = np.column_stack([common[rng.permutation(n),j] for j in range(p)])
    result = {
        "source": "synthetic_only",
        "seed": seed, "samples": n, "features": p,
        "rho": rho, "aspect_ratio": p/(n-1),
        "mp_upper": (1+np.sqrt(p/(n-1)))**2,
        "population_market_eigenvalue": 1+(p-1)*rho,
        "population_residual_eigenvalue": 1-rho,
        "independent": spectrum(null),
        "common_factor": spectrum(common),
        "shuffled": spectrum(shuffled),
    }
    print(json.dumps(result, sort_keys=True, indent=2))

if __name__ == "__main__":
    main()

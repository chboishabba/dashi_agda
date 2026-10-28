#!/usr/bin/env python3
"""Exact-rational inverse-stability diagnostic for the Goodman sound fixture.

This file does NOT implement an acoustic field equation or validate a physical
sensor. It illustrates the existing DASHI RobustExperimentInferenceFrontierExact
boundary: injectivity does not supply a UNIFORM bound on inversion error across
an admissible family. Each finite nonsingular matrix remains continuously
invertible. No human/weapon effects, clinical claims or Monster representations.
"""
from fractions import Fraction as F
from json import dumps


def forward(n: int, x: tuple[F, F]) -> tuple[F, F]:
    """A_n = [[1,0],[1,1/n]] on two abstract hidden coordinates."""
    if not isinstance(n, int) or n <= 0:
        raise ValueError("n must be a positive integer")
    return x[0], x[0] + x[1] / n


def inverse(n: int, y: tuple[F, F]) -> tuple[F, F]:
    if not isinstance(n, int) or n <= 0:
        raise ValueError("n must be a positive integer")
    return y[0], n * (y[1] - y[0])


def norm_inf(v: tuple[F, F]) -> F:
    return max(abs(v[0]), abs(v[1]))


def run() -> list[dict]:
    results = []
    two_channel_checks = 0
    for n in (1, 2, 10, 100, 1000, 10000):
        # det(A_n) = 1/n, nonzero; exact inverse recovers any rational x.
        determinant = F(1, n)
        assert determinant > 0
        hidden = (F(2, 3), F(5, 7))
        y = forward(n, hidden)
        assert inverse(n, y) == hidden

        # An uncertainty of 1/n in the second observed channel admits
        # an equally compatible hidden state with x2 changed by exactly 1.
        # It does not identify which state generated a noisy observation.
        perturbed_y = (y[0], y[1] + F(1, n))
        reconstructed = inverse(n, perturbed_y)
        measurement_error = norm_inf((perturbed_y[0]-y[0], perturbed_y[1]-y[1]))
        hidden_error = norm_inf((reconstructed[0]-hidden[0], reconstructed[1]-hidden[1]))
        assert measurement_error == F(1, n)
        assert hidden_error == 1
        assert hidden_error / measurement_error == n

        # In infinity norm the EXACT operator norms are
        # ||A_n||_inf = 1 + 1/n, ||A_n^-1||_inf = 2n.
        # Hence the condition number is 2(n+1).
        inverse_norm = 2*n
        forward_norm = 1 + F(1, n)
        condition = forward_norm * inverse_norm
        assert condition == 2*(n+1)

        # Two-channel errors distinguish source uncertainty from
        # correlated/common-mode cancellation. This is exact algebra,
        # NOT a probabilistic covariance calibration.
        for first_error, second_error in (
            (F(1, n), F(0)),
            (F(0), F(1, n)),
            (F(1, n), F(1, n)),
            (F(1, n), -F(1, n)),
        ):
            noisy_pair = (y[0] + first_error, y[1] + second_error)
            result = inverse(n, noisy_pair)
            expected_hidden_second = hidden[1] + n*(second_error - first_error)
            assert result == (hidden[0] + first_error, expected_hidden_second)
            if first_error == second_error:
                assert result[1] == hidden[1]
            two_channel_checks += 1

        results.append({
            "n": n,
            "determinant": str(determinant),
            "full_rank": True,
            "measurement_error": str(measurement_error),
            "hidden_error": str(hidden_error),
            "error_amplification": str(hidden_error/measurement_error),
            "condition_inf": str(condition),
        })

    # For every finite candidate uniform Lipschitz constant K, choosing
    # n > K makes the constructed inverse error ratio n > K.
    # These test values illustrate the symbolic identity, not exhaust N.
    assert two_channel_checks == 24
    assert all(row["full_rank"] for row in results)
    assert results[-1]["condition_inf"] == "20002"
    print(dumps({
        "model": "synthetic-rational-two-by-two-inverse",
        "checked": len(results),
        "two_channel_checks": two_channel_checks,
        "all_passed": True,
        "family_symbolic": "det(A_n)=1/n; ||A_n^-1||_inf=2n; cond_inf(A_n)=2(n+1)",
        "boundary": "per-n invertible is not uniformly stable as n grows",
        "not_verified": [
            "Agda kernel", "calibrated sound", "physical instrument",
            "causal intervention", "human response", "Monster same-object"
        ],
        "results": results
    }, indent=2))
    return results


if __name__ == "__main__":
    run()

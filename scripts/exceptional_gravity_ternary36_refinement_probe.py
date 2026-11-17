from decimal import Decimal, getcontext

getcontext().prec = 50

C = Decimal(299792458)
CS133 = Decimal(9192631770)
EDGE_MM = (C / CS133) * Decimal(1000)
PHI = -Decimal(11) / Decimal(54)
D_PHI_DZ = Decimal(5) / Decimal(9)
THEORY_GRADIENT = Decimal("1.09e-19")
CORRECTED_CENTRAL = Decimal("0.98e-19")
CORRECTED_SIGMA = Decimal("0.23e-19")
SYNCHRONOUS_CENTRAL = Decimal("1.28e-19")
SYNCHRONOUS_SIGMA = Decimal("0.27e-19")


def epsilon_from_depth(depth: int) -> Decimal:
    return Decimal(1) / (Decimal(3) ** depth)


def vertical_clock_gradient(epsilon: Decimal) -> Decimal:
    omega = Decimal(1) + epsilon * PHI
    return abs(epsilon * D_PHI_DZ / omega) / EDGE_MM


def epsilon_for_gradient(target: Decimal) -> Decimal:
    y = target * EDGE_MM
    return y / (D_PHI_DZ - y * PHI)


def verify():
    eps36 = epsilon_from_depth(36)
    grad36 = vertical_clock_gradient(eps36)
    nearby = {n: vertical_clock_gradient(epsilon_from_depth(n)) for n in (35, 36, 37)}
    assert abs(grad36 / THEORY_GRADIENT - Decimal(1)) < Decimal("0.05")
    assert abs(grad36 - CORRECTED_CENTRAL) <= CORRECTED_SIGMA
    assert abs(grad36 - SYNCHRONOUS_CENTRAL) <= SYNCHRONOUS_SIGMA
    assert abs(nearby[36] - THEORY_GRADIENT) < abs(nearby[35] - THEORY_GRADIENT)
    assert abs(nearby[36] - THEORY_GRADIENT) < abs(nearby[37] - THEORY_GRADIENT)
    return {
        "candidate_edge_mm": EDGE_MM,
        "epsilon_3_minus_36": eps36,
        "predicted_gradient_per_mm": grad36,
        "theory_gradient_per_mm": THEORY_GRADIENT,
        "theory_ratio": grad36 / THEORY_GRADIENT,
        "corrected_sigma_offset": (grad36 - CORRECTED_CENTRAL) / CORRECTED_SIGMA,
        "synchronous_sigma_offset": (grad36 - SYNCHRONOUS_CENTRAL) / SYNCHRONOUS_SIGMA,
        "epsilon_to_match_theory": epsilon_for_gradient(THEORY_GRADIENT),
        "depth35_gradient": nearby[35],
        "depth37_gradient": nearby[37],
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")

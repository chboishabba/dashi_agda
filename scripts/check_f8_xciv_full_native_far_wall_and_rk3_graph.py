"""F8 XCIV — same-source far wall field and SSPRK3 radial support gate.

Reads ORIGINAL full LVI production receipts (NOT compact transcriptions).
Exact SymPy affine SSPRK3 polynomial and conservative Boolean radial graph
of original stage dependencies. Does not rerun a PDE, bound an amplitude, or
assert physical acceptance. No CI.
"""
import argparse
import json
from decimal import Decimal
from pathlib import Path
import sympy as sp

CASES = (
    ("medium", "ads5_f8_LVI_independent_medium_full.json", 1506),
    ("medium_dt_half", "ads5_f8_LVI_independent_medium-dt-half_full.json", 3011),
)
PULSE = Decimal(".065")


def radial_rk3_structural_reach(dr, dt, far_radius, nr, last_source, max_steps):
    """The actual stage's radial dependency graph, deliberately ignoring
    coefficients and normal-axis cancellation: U' depends on P,M at same r;
    P',M' depend on P,M at same r and U at r-1,r,r+1.
    Nonzero support of the original compact source enters P/M only.
    """
    j = int(far_radius // dr)
    stencil = tuple(range(j - 1, j + 3))
    assert stencil[0] > last_source
    mask = (1 << nr) - 1
    source_mask = (1 << (last_source + 1)) - 1
    u = velocity = 0
    first_u = first_v = None

    def rhs(x, y, src):
        return y, (y | x | (x << 1) | (x >> 1) | src) & mask

    for n in range(1, max_steps + 1):
        src = source_mask if (n - 1) * dt < PULSE else 0
        k_u, k_v = rhs(u, velocity, src)
        u1, v1 = u | k_u, velocity | k_v
        k_u, k_v = rhs(u1, v1, src)
        u2, v2 = u | u1 | k_u, velocity | v1 | k_v
        k_u, k_v = rhs(u2, v2, src)
        u, velocity = u | u2 | k_u, velocity | v2 | k_v
        if first_u is None and any((u >> cell) & 1 for cell in stencil):
            first_u = n
        if first_v is None and any((velocity >> cell) & 1 for cell in stencil):
            first_v = n
        if first_u is not None and first_v is not None:
            break

    assert first_u is not None and first_v is not None
    return dict(stencil=stencil, source_last_cell=last_source,
                minimum_radial_hops=stencil[0] - last_source,
                first_structurally_possible_U_step=first_u,
                first_structurally_possible_velocity_step=first_v,
                first_structurally_possible_U_bulk_time=float(dt * first_u))


def rk3_formal():
    z = sp.symbols("z")
    R = 1 + z + z*z/2 + z*z*z/6
    B = 1 + z/2 + z*z/6
    assert sp.simplify((R - 1)/z - B) == 0
    # Formal frozen linear system: U'=P, P'=A_r U + f.
    # Each radial hop in U from source f in P requires L^(2D+1).
    checks = []
    for n in range(1, 6):
        p = sp.Poly(sp.expand(B * sum(R**k for k in range(n))), z)
        odd = [m for (m,), v in p.terms() if m % 2 and v]
        checks.append((n, (max(odd) - 1)//2))
    assert checks == [(1, 0), (2, 2), (3, 3), (4, 5), (5, 6)]
    return dict(R=str(R), B=str(B), checked_hop_orders=checks)


def audit(root):
    rows = []
    for label, filename, steps in CASES:
        path = root / filename
        if not path.is_file():
            raise FileNotFoundError("MISSING complete original production JSON: " + str(path))
        j = json.loads(path.read_text(), parse_float=Decimal)
        assert j["model"] == "original moving AdS5 a=t Neumann compact TT"
        assert j["original_radial_multipoles"] == [0, 2, 4]
        assert j["normal_order"] == 3 and j["steps"] == steps
        assert j["conservative_source_cell_average"] is True
        assert j["intrinsic_4D_weyl_spatial_operator"] == "full_reconstructed_Delta3"
        assert j["step_radial"] == Decimal(".008") and j["step_bulk"] == Decimal(".012")
        wall = j["far_mode_values"]
        assert len(wall) == 3 and all(x.is_finite() and x != 0 for x in wall)
        e4 = j["far_mode_intrinsic_4D_electric_Weyl"]
        e5 = j["far_mode_projected_5D_electric_Weyl"]
        assert len(e4) == len(e5) == 3
        assert all(x.is_finite() for x in e4 + e5)
        reach = radial_rk3_structural_reach(
            j["step_radial"], j["step_time"], j["far_receiver_grid_r"],
            j["radius_bins"], 5, steps)
        rows.append(dict(label=label, source_file=filename,
            far_wall_modes=[str(x) for x in wall],
            far_E4_modes=[str(x) for x in e4],
            far_E5_modes=[str(x) for x in e5],
            structural_reach=reach))
    a, b = rows
    changes = [float(abs((Decimal(y) - Decimal(x))/Decimal(x)))
               for x, y in zip(a["far_wall_modes"], b["far_wall_modes"])]
    assert max(changes) < 0.01
    assert all(x["structural_reach"]["first_structurally_possible_U_step"] == 218
               for x in rows)
    return dict(
        status="DIAGNOSTIC PASS; PHYSICAL FAR-CAUSAL-NULL FAIL",
        source="original full LVI production JSON, not compact receipt",
        observations=rows, far_wall_relative_changes=changes,
        scope="Nonzero interpolated far field implies nonzero underlying wall node(s). "
              "Boolean reach is only a dependency overapproximation; neither "
              "a quantitative leakage explanation nor continuum support proof.")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--receipt-dir", type=Path,
                   default=Path(__file__).resolve().parents[1] / "Artifacts/ksw668")
    p.add_argument("--structure-only", action="store_true")
    args = p.parse_args()
    result = dict(formal_rk3=rk3_formal())
    if not args.structure_only:
        result["producer_replay"] = audit(args.receipt_dir)
    print(json.dumps(result, indent=2))

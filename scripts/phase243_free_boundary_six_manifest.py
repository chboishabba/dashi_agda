from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Tuple


@dataclass(frozen=True)
class Candidate:
    name: str
    tag: Tuple[int, int, int, int]
    a1: float
    a2: float
    delta_c: float
    mach: float
    alpha: float
    b_rel: float
    kg_rms: float
    div_rms: float
    min_rho: float
    coil_relative_bn_residual: float
    coil_coefficient_norm: float


AOFF = (0, 0, 1, 1)
AALI = (0, 0, 1, 0)
XOFF = (2, 0, 0, 1)


def shortlist() -> tuple[Candidate, ...]:
    # Frozen from scripts/phase243_core54_pareto_coil.py on PR #1096.
    # These are executable-search artifact values, not experimental authority.
    return (
        Candidate("AoffRouteC", AOFF, .04, -.04, 1.0, 0.0, 0.0,
                  .03364394467035214, .24477337100674026,
                  2.528019371855315e-17, .9230199850480754,
                  .08501103263938856, .006359868972726422),
        Candidate("AaliRouteC", AALI, .04, -.04, 1.0, 0.0, 0.0,
                  .03364392998437984, .24477337519330805,
                  2.3015506029962425e-17, .9248245903371273,
                  .08501103263939014, .006359868972726406),
        Candidate("AoffMixed", AOFF, .04, -.04, .75, .25, .1875,
                  .03364394467035214, .24477337100674026,
                  2.528019371855315e-17, .9230199850480754,
                  .08501103263938856, .006359868972726422),
        Candidate("AaliMixed", AALI, .04, -.04, .75, .25, .1875,
                  .03364392998437984, .24477337519330805,
                  2.3015506029962425e-17, .9248245903371273,
                  .08501103263939014, .006359868972726406),
        Candidate("XoffRouteC", XOFF, -.04, -.04, 1.0, 0.0, 0.0,
                  .006899842896416637, .24821283815358552,
                  1.8398150762989732e-17, 1.0,
                  .5285936981051297, .016578637318717317),
        Candidate("XoffMixed", XOFF, -.04, -.04, .75, .25, .1875,
                  .006899842896416637, .24821283815358552,
                  1.8398150762989732e-17, 1.0,
                  .5285936981051297, .016578637318717317),
    )


def validate() -> dict[str, object]:
    xs = shortlist()
    assert len(xs) == 6
    assert len({x.name for x in xs}) == 6
    assert {x.tag for x in xs} == {AOFF, AALI, XOFF}
    assert {x.delta_c for x in xs} == {.75, 1.0}
    for x in xs:
        assert abs((x.mach * x.mach) + x.alpha + x.delta_c - 1.0) < 1e-12
        assert x.coil_relative_bn_residual < 1.0
        assert x.div_rms < 1e-12
    for tag in (AOFF, AALI, XOFF):
        rows = [x for x in xs if x.tag == tag]
        assert len(rows) == 2
        assert {r.delta_c for r in rows} == {.75, 1.0}
    return {
        "candidate_count": len(xs),
        "geometry_phase_identity_count": len({x.tag for x in xs}),
        "abc_allocation_count_per_identity": 2,
        "all_coil_proxy_residuals_below_baseline": all(
            x.coil_relative_bn_residual < 1.0 for x in xs
        ),
        "candidates": [asdict(x) for x in xs],
    }


if __name__ == "__main__":
    print(validate())

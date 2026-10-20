from ternary27_routeC_search import Ternary27RouteC
from ternary27_sparse_support import ranked_support, sparse_scan


def test_ranked_support_excludes_gauge_modes():
    p = Ternary27RouteC(nth=10, nz=12)
    rows = p.continuation(levels=(1.0,), maxiter=30)
    coeff = rows[-1][3]
    order = ranked_support(coeff)
    assert 0 not in order
    assert 9 not in order
    assert 18 not in order


def test_sparse_scan_finds_retained_patch():
    p = Ternary27RouteC(nth=10, nz=12)
    full_objective, full_metrics, full_coeff, rows = sparse_scan(p, max_support=5)
    assert full_objective > 0.0
    assert full_metrics["minimum_minor_radius"] > 0.35
    assert len(rows) == 5
    assert any(row[-1] for row in rows)


if __name__ == "__main__":
    test_ranked_support_excludes_gauge_modes()
    test_sparse_scan_finds_retained_patch()
    print("ok")

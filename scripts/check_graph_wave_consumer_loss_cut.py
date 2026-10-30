#!/usr/bin/env python3
"""Independent exact matrix-graph-wave residual obstruction regression.

Sources: classical matrix/digraph correspondence and C3 orbit averaging;
original DASHI TrialecticWeightedDirectedGraph369Exact and
TrialecticC3WeightedOrbitSymmetrizationExact (PR #1438); wave semantics from
Physics.WaveAlgorithmLift, consumer-indexed collision from
Core.ConsumerIndexedResidualRefinementExact. The finite test neither runs
an analytic pi-phase producer nor establishes twin-prime infinitude.
"""

V = range(3)
def rotate(x): return (x + 1) % 3

def left(s, t): return int((s, t) == (0, 1))
def right(s, t): return int((s, t) == (1, 2))

def orbit(w, s, t):
    return (w(s, t) + w(rotate(s), rotate(t))
            + w(rotate(rotate(s)), rotate(rotate(t))))

def matrix(w):
    return tuple(tuple(w(s, t) for t in V) for s in V)

def incoming(w, vertex, source): return w(source, vertex)
def outgoing(w, vertex, target): return w(vertex, target)

def audit():
    assert matrix(orbit_left) == matrix(orbit_right)
    assert matrix(orbit_left) == ((0, 1, 0), (0, 0, 1), (1, 0, 0))
    assert left(0, 1) == 1 and right(0, 1) == 0
    assert ('pos' if left(0,1) else 'zero') != ('pos' if right(0,1) else 'zero')
    for w in (left,right):
        for s in V:
            for t in V:
                assert outgoing(w,s,t) == w(s,t) == incoming(w,t,s)
                assert w(s,t) == matrix(w)[s][t]
                assert orbit(w,rotate(s),rotate(t)) == orbit(w,s,t)
    # Orbit symmetrization is not a faithful observer for arbitrary
    # directed-edge consumers; exact same coarse image, different weight.
    print("PASS exact nine-entry graph orbit collision: directed A→B 1 vs 0")
    print("PASS source/target hyperfabric restrictions preserve original orientation")
    print("PASS selected finite wave trits: pos vs zero")
    print("BOUNDARY no arithmetic prime-pair estimate / no Pickover pi-phase sign")

def orbit_left(s,t): return orbit(left,s,t)
def orbit_right(s,t): return orbit(right,s,t)

if __name__ == "__main__": audit()

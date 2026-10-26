#!/usr/bin/env python3
"""Severe controls for the pinned Hatcher open-exhaustion compactness lemma.

The REAL new Lean source uses Mathlib IsCompact.elim_directed_cover.
These finite exact controls distinguish the indispensable hypotheses:
  1) Increasing OPEN cover of compact loop/homotopy images: valid.
  2) Increasing but NOT OPEN cover: compact subset needn't be inside
     any member, even though the set union covers it.
  3) OPEN but NOT DIRECTED cover: no single member need contain K.

Historical proof context: Hatcher Algebraic Topology Example 2B.2,
Alexander 1924. Formal proof implementation donor: Mathlib.
No program here computes Hatcher's actual infinite linked horn group.
"""
from fractions import Fraction as F

def stage_closed(n):
    """Finite, closed, NOT open in R, subset of compact K."""
    return frozenset([F(0)] + [F(1,k) for k in range(1,n+1)])

def point_on_limit_set(k):
    """1/k belongs to K = {0} union {1/j | j>=1} for k>=1."""
    assert k>=1
    return F(1,k)

def audit(depth=256):
    # A finite stage never captures all of compact K. For every n
    # the witness 1/(n+1) is in K but absent from F_n.
    # This is a universal rational identity, checked at finite depths.
    for n in range(1,depth+1):
        F_n=stage_closed(n)
        witness=point_on_limit_set(n+1)
        assert stage_closed(n-1)<=F_n
        assert witness not in F_n
        assert witness in stage_closed(n+1)
    # In discrete X={0,1}, every subset is open; the two-set cover
    # is not directed and neither member covers compact K=X.
    compact=frozenset((0,1))
    opens=(frozenset((0,)),frozenset((1,)))
    assert compact==opens[0]|opens[1]
    assert all(not compact<=U for U in opens)
    assert all(not(U<=V or V<=U) for U,V in ((opens[0],opens[1]),))
    # Positive directed example on the same compact discrete X:
    directed=(frozenset(),frozenset((0,)),compact)
    assert all(directed[i]<=directed[i+1] for i in range(len(directed)-1))
    assert compact<=directed[-1]
    return {
      'status':'PASS', 'negative_no_openness':'K convergent sequence covered by closed F_n, no uniform n',
      'negative_no_directedness':'discrete compact {0,1} covered by two opens, neither sufficient',
      'positive_directed_discrete':'eventual full stage',
      'finite_witness_levels':depth,
      'hatcher_group_colimit_machine_checked':False,
      'wild_linked_handlebody_machine_checked':False,
      'proof_owner':'Mathlib IsCompact.elim_directed_cover'
    }

if __name__=='__main__':
    import json
    print(json.dumps(audit(),indent=2))

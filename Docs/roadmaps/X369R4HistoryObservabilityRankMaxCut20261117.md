# X369 R4 original-history rank and future-sufficiency max-cut

**Date:** 17 November 2026. **Status:** locally verified symbolic/finite
algebra; original checkpoint / Agda / hardware proof acceptance not claimed.
**Source owners:** LeechTransformer `models/history_orbit_moe.py`,
`models/trialectic_wave_prior.py`.
**SymPy script:** `scripts/check_x369_r4_circulant_history_sufficiency_sympy.py`.

## Original shared directed head as a C3 circulant

For one triad `x=(a,b,c)`, expert history `h=(A,B,C)` and trained
directed weights `w=(ws,wf,wr)`, the original scalar is

    ws*(aA+bB+cC)+wf*(aB+bC+cA)+wr*(aC+bA+cB)
      = <M_w x,h> = <x,M_w^T h>

with exact circulant matrix

    M_w = [[ws,wr,wf],
           [wf,ws,wr],
           [wr,wf,ws]].

Define `D_w=ws+wf+wr` and the three-point rotating-plane energy

    q(w)=ws²+wf²+wr²-ws*wf-wf*wr-wr*ws
        = 1/2[(ws-wf)²+(wf-wr)²+(wr-ws)²].

Symbolic exact identities:

    det(M_w) = D_w * q(w),

    M_w^T M_w = q(w)*I + (D_w²-q(w))*J/3,

where J is the all-ones 3x3 matrix. Consequently the **squared
singular values** are `D_w²,q(w),q(w)`.

### Complete original-score history observability classification

- **Rank 3** iff `D_w ≠ 0` and `q(w) > 0` (generic real head).
  Across all possible activations x, `h ↦ (x↦score(x,h))`
  is injective; no fixed lower-rank linear history codec
  can preserve this original directed consumer universally.
- **Rank 2** iff `D_w=0` and `w≠0`. The DC history
  direction (1,1,1) is unobservable to the directed score;
  its zero-mean/rotating-plane projection is sufficient for
  that **specific** scalar consumer across all x.
- **Rank 1** iff `ws=wf=wr≠0`; only the DC history
  component is observed by the original directed score.
- **Rank 0** iff all directed weights vanish.

This is an exact **consumer-relative** classification of the
original integer/real polynomial. It does not license a
universal codec for finite-precision scores or for the
full recurrent source model.

### Extension to the q-gated mixed phase branch

Original `q(x)` is invariant under both C3 rotations and C2 sign.
Because the per-triad mixed phase gate depends only on the
sample's collection of q values and its mean, it is unchanged
by individually rotating the input triads. Therefore the
piecewise-C3 map Fq has an explicit inverse: apply the
opposite triadwise rotation using the **same** q gate.
It is an exact bijection of the full activation carrier
and commutes with the diagonal C3 action. Consequently,
allowing arbitrary source activations cannot evade the
generic-rank history observability statement merely by
passing through the mixed-q phase map.

This statement is about the SOURCE geometry, not neural
task semantics or quantified robustness at gate thresholds.
Quantization of Fq still requires the source q-threshold
margin established in the earlier relative-error report.

### Crucial non-descent for FULL R4 future state

The original R4 baseline has a learned **C2 history** term
`v·abs(h)`. At directed-head rank 2 with weight sum zero,
histories `h=(0,0,0)` and `h'=(1,1,1)`
have identical directed score for every x; however
the original C2 history consumer with v=(1,0,0)
separates them (0 versus 1). The source orientation
head, expert FFN and learned history transition
may similarly observe or retain the discarded DC
information. A transition can even preserve it
exactly (identity witness). Hence

    sufficient for directed score
      ≠ sufficient for full R4 routing
      ≠ sufficient for selected expert transition
      ≠ sufficient for future reactivation
      ≠ sufficient for typed semantic consumer.

Admissible history compression must factor through
the JOIN of all relevant consumer fibres and the
future transition; its minimal dimension may be
higher than the directed-score rank.

### Near-low-rank and quantization implication

For `h_⊥=(I-J/3)h`, the original head satisfies

    ||M_w h||² = D_w² ||h_DC||² + q(w)||h_⊥||².

If `|D_w|` or `sqrt(q(w))` is small, removing the
corresponding history component has a **bounded
directed-score discrepancy** even before exact
rank loss. This gives a prospective MDL/approximate
consumer tradeoff, but only after the source
TopK and softmax margins, the C2 baseline path,
expert transition and actual quantization errors
are certified. No measured trained-head singular
values are provided here.

### Source verification and follow-up

The independent local SymPy run for this source
mathematics passed **14 grouped tests** before
the additional C3/q-mask invertibility source
checks were committed. The committed script
includes the extra exact q invariance and
finite inverse/commutation controls; no
GitHub Actions or Agda kernel pass is claimed.

**Next maximum cut:**
1. Accept an actual original checkpoint weight/head
   rank/singular-value receipt (not guessed values).
2. Intersect the directed-score fibres with
   C2 `abs(h)`, orientation chart, FFN input,
   transition and inactive-history consumers.
3. Use the certified pairwise score-difference
   envelopes in the earlier
   `X369R4RelativeErrorMaxCut20261117.md`
   to admit approximate rank reduction against
   TopK/softmax consumer margins.
4. Reopen original authoritative inactive histories
   at reactivation; preserve independently typed
   Sophontic/grokking/trialectic-face evidence.

Research attribution: Leech-LILA original by Anatolii Kornienko.
DASHI reuse-first policy; no ESD modifications.


## Stronger P0 joint-router non-descent witness

For a nonzero zero-sum directed head,
`w_s+w_f+w_r=0`, consider two original
expert histories

    h+ = t*(1,1,1),   h- = -t*(1,1,1),   t>0.

For EVERY source input x, the original
directed score agrees:

    <M_w x,h+> = <M_w x,h-> = 0.

The **full C2 history vector** also agrees
exactly, not merely after scoring:

    abs(h+) = abs(h-) = t*(1,1,1).

Consequently the entire R4 ROUTING logit
contribution (shared unary x + v·abs(h)
+ directed residual + same expert bias)
is identical on these two histories
for all source x, including source
coherent or bijective mixed q-gated phase.
This is an exact non-injective joint
C2+directed routing quotient.

But the original expert FFN,
orientation sign and transition consume
SIGNED histories; the two states are
not definitionally equal and are not
certified equivalent for those consumers
or future traces. This proves the
need to JOIN selected-execution and
transition fibres even after combining
the two R4 router feature families.
The updated SymPy source checks this
adversarial witness, without claiming
the original learned FFN parameters
actually separate the specific pair.

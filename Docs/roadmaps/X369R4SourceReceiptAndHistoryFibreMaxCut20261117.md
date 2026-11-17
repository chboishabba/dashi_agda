# X369 R4 source-receipt and joint-history-fibre maximum cut
**17 November 2026.** Original architecture:
`chboishabba/LeechTransformer` PR #5
(`models/history_orbit_moe.py`, `models/trialectic_wave_prior.py`).
Formal source: DASHI PR #1526. Original Leech-LILA attribution:
Anatolii Kornienko. ESD surfaces untouched.

## 1. Reuse the existing original source evidence owners

Original Leech already implements:
- `scripts/audit_x369_projected_router_score_weld.py`:
  source directed feature → learned projected router head →
  strict top-k score-margin check on supplied frozen tensors.
  Its `atol=2e-4`/`rtol=3e-5` for float32 are comparison
  thresholds in that audit, **NOT a universally certified
  quantiser error bound**. Do not transplant them as such.
- `scripts/run_x369_r4_three_arm_source_maxcut.py`:
  native R1 document provenance and repaired C2 checkpoint
  SHA admission, three matched R4 arms, and fitted residual
  checkpoint delta payloads.
- `models/x369_fair_c3_residual.py`: finite q-gated
  branch and strict fitted-delta source/geometry fingerprints.
  Metadata alone does not authenticate source checkpoint bytes.

No actual fitted R4 snapshot, captured hidden-state matrix
receipt or original quantiser precision certificate was recovered
from accessible source files in this work. The user requested
to continue with SymPy rather than rerun GPU/Agda/CI.

## 2. Exact source-compatible joint history fibre counterexample

For a single original triad with directed weights
`(ws,wf,wr)=(2,-1,-1)`, the source directed head is
rank 2 and annihilates the DC direction. Consider
two expert histories `h+=(1,1,1)` and
`h-=(-1,-1,-1)`:

    T-directed score(x,h+) = T-directed score(x,h-)
        for every activation x,
    abs(h+) = abs(h-) = (1,1,1).

The entire C2-history plus C3-directed *routing*
consumer therefore cannot distinguish these histories
when they belong to the same expert and retain the
same bias. However the **original selected executor**
receives signed h in both
`orientation(cat(x,h))`, `experts[e](cat(sign*x,sign*h))`,
and `transitions[e](cat(sign*h,sign*x,y_c))`.

A source-shaped exact-real witness sets shared
`x=(1,0,0)` and makes the orientation linear
head read **x0 only**, so both sign charts are
strictly +. Choose licensed source-shaped FFN
weights that select the first signed history
coordinate in the first linear layer and emit
its GELU into the first output coordinate.
Then, exactly,

    GELU(+1) - GELU(-1) = 1,

so selected expert outputs differ despite
EVERY routing score remaining equal for these
histories. An allowed transition matrix may also
copy the first old-history coordinate directly.
This is a constructive **existence counterexample
for the architecture**, not a claim that the
actually trained FFN uses those witness weights.

## 3. Exact positive sufficient codec criterion

For a history encoder `E:H→C`, selected
observable `O`, and source state transition
`T`, a genuine source consumer quotient requires

    E(h1)=E(h2) => O(h1)=O(h2),
    E(h1)=E(h2) => E(T(h1))=E(T(h2)).

The second implication is the **lumpability /
transition-fibre stability** condition. It gives
a well-defined reduced transition `Tbar`
satisfying `E∘T=Tbar∘E`; induction then preserves
all finite future encoded states and any consumer
factoring through E.

In a linear history subspace `E=P` this is:
- each observer row belongs to rowspace(P);
- `ker(P)` is invariant under transition T,
  or equivalently `P*T=Tbar*P`.

The new `scripts/check_x369_r4_joint_history_fibres_sympy.py`
uses source-shaped linear witnesses, a 2D retained
projection `P=diag(1,1,0)`, a symbolic block
transition with no discarded→retained connection,
and proves by SymPy that
`P T^n=Tbar^n P` for n=1,…,6.
A violating transition feeds h2 into h0 and
shows identical codes at t0 diverge at t1.

For the **selected FFN first affine layer**,
a fixed source orthant turns v·abs(h) into a
linear row `v*diag(sign(h))`. To preserve all
selected preactivations through a two-coordinate
linear codec, the source actual FFN history
matrix must also factor through that codec.
A source-compatible full-rank 3×3 history
block proves the negative (rank=3).
A restricted source-compatible block whose
third column is zero proves the positive
observer condition (rank=2). The actual
checkpoint rank is not available; no
compression admission for real fitted weights.

Local exact SymPy: **25 checks passed**,
covering source routing collision, chosen
GELU separation, arbitrary-symbolic n-step
transition-quotient identities, violating
future counterexample, and observer rank
positive/negative controls.

## 4. Fail-closed external precision and state handoff

New `scripts/check_x369_r4_source_receipt.py`
accepts a JSON object with schema
`x369_r4_source_relative_v1` and exact
rational-string values.

Required source claims/fields: source branch
`arm=coherent|mixed`, checkpoint SHA256 syntax,
externally checked SHA and exporter flags,
source float-evaluation-error receipt flag,
x, all expert histories, original baseline
C2 history head, original C3 directed head,
all expert biases, original seed-owned
q mask, `top_k`, source selected IDs,
selected orientation weight, per-coordinate
x/h/baseline/direct/biased errors, per-pair
floating evaluation slack, per-triad q-energy
evaluation slack, orientation coefficient and
floating evaluation slack.

It returns a **conditional rational-model**
certificate only after:
1. original mixed q-mask intervals determine
   every branch;
2. each selected/excluded pair and adjacent
   selected pair has strict original score
   margin larger than a **correlated** relative
   perturbation budget;
3. all selected orientation signs have strictly
   separated nonzero intervals.

It also returns the admitted selected
softmax L1 bound from pairwise differences.
It explicitly outputs

    "source_checkpoint_authenticated_by_this_script": false
    "full_recurrent_state_certified": false.

This is important: a self-reported `true`
provenance flag or hexadecimal SHA string is
NOT a cryptographic attestation. The file
must be produced by a separate trusted original
source owner who actually reads/hashes checkpoint
bytes and computes a valid rounding-error
certificate. The standalone adapter does not
and cannot verify that original source
authentication by itself.

**Local fixture gate:** synthetic coherent and
mixed records with source rational values
and complete admitted 1/256-style bounds
returned conditional selected IDs
`(2,3)` and `(3,2)`, respectively, each
with selected softmax L1 budget
`594441/8388608`. Mutating the required
source-export verification flag to false
rejected both records. These are test
fixtures, NOT independently checked
checkpoint receipts.

Usage on a **genuine externally produced**
source receipt:

```bash
python3 scripts/check_x369_r4_source_receipt.py source_receipt.json
```

No actual original checkpoint, source routed
state, matrix singular values or quantizer
calibration was produced in this no-run phase.

## 5. Next high-alpha source obligations

1. Have the original Leech source authority
   export *source-bound* model/hidden-history
   values and error receipts under its existing
   repair/checkpoint SHA gate; do not open F5.
2. Bind its error precision to the actual
   dtype, reduction order, `abs`, q energy
   mean, `torch.topk` and selected-softmax
   kernels. Treat the existing projector
   audit tolerances only as *test criteria*.
3. For each selected expert, obtain the
   original orientation and FFN history
   weight blocks and transition; intersect
   their consumer kernels with directed and
   baseline C2-history fibres.
4. Only compress inactive history when the
   actual transition preserves that quotient
   or the original source owner retains and
   reopens its full history. Check this for
   all reactivations and source revisions.
5. Independently type/check grokking,
   Sophontic argument-response and
   trialectic face consumers.

No Agda kernel, GPU or trained semantic
result is claimed here.

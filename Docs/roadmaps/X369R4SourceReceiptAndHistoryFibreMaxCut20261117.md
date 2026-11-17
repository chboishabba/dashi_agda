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


## 6. Conditional original arithmetic rounding frontier

New executable exact-rational interval owner:
`scripts/check_x369_r4_conditional_roundoff_sympy.py`.

Unlike reusing source audit tolerances as if they
were certified `float32` error margins, this
script supplies an **explicit conditional
floating-operation contract**:

    fl(a op b) = exact(a op b)*(1+δ),
    |δ| <= 2^-24,

for each independently specified addition
and multiplication, with finite normal
results, no under/overflow and no
unverified extra rounding mode. The script
propagates outward rational interval
enclosures through TWO explicitly
disclosed source-equivalent expression
plans: original per-expert directed
correlations followed by learned head,
and shared-head fused K(x) then
expert-history dot. Baseline C2
`v·abs(h)` and expert biases are
retained in both plans. It is NOT
a proof that the actual Torch/ROCm
source kernel takes either operation
order; FMA, TF32, reduction trees,
reassociation and GPU architecture
still require a source execution
semantics receipt.

The original two-triad, E=4 exact
rational source fixtures have the
same certified ordered TopK in both
plans. In this conservative interval
evaluation, however, fusion is
**not uniformly superior in precision**:

| Source R4 arm | Original-plan selected-pair roundoff upper bound | Fused-plan upper bound |
| --- | ---: | ---: |
| Coherent C3 | 5.84126e-6 | 5.96047e-6 |
| Mixed q C3 | 7.39098e-6 | 7.51019e-6 |

The two arms' source logits are,
respectively, (3,4,13,11) and
(5,2,9,17), with original
selected pairs (2,3) and (3,2).
All numbers above are bounds under
the stated **ideal binary32
arithmetic-plan assumptions**, not
hardware results.

Direct local rational interval audit:
**15 grouped checks passed**.
The proof demonstrates a meaningful
resource/precision Pareto distinction:
fused scoring reduces scalar
multiplication/addition sites in
the disclosed E>1 arithmetic plan,
but reassociation may widen a
conservative floating-error envelope.
Physical source runtime, actual
float kernels and optimizer
gradient parity remain OPEN.

For the next original source
checkpoint receipt, keep
`differential_floating_eval`
as an independent pairwise
error term unless the original
kernel's precision and operation
graph are actually certified.
Do not inject ideal-plan bounds
as if they were measured source
error receipts.


## 17 November GELU parity source-donor reuse and recurrent chart max-cut

**Priority owner:** `Docs/roadmaps/X369R4GELUParityChartHistoryMaxCut20261117.md`.
**Executable SymPy:** `scripts/check_x369_r4_gelu_parity_history_sympy.py`;
its source-specific bounds are also welded into
`scripts/check_x369_r4_end_to_end_envelope_sympy.py`.

Recovered and **reused**, not cloned, the early 31 October
`Docs/LeechGELUParityHistoricalSafetySteelman20261031.md`,
`LeechSignedHistoryExpertBidiExact.agda`,
`LeechOddOnlyApproximationObstructionExact.agda` (F02a),
`LeechLayerErrorTransportExact.agda` (F07),
`PhysicalInvolutionParityExact.agda`, and existing
`QuantisedSearchBoundsExact.agda`. The early scalar real
GELU `g(-z)=g(z)-z`, odd half `z/2` and even
`z erf(z/sqrt2)/2` were ALREADY documented;
the new proof-development specialises them to the
ORIGINAL learned signed expert with biases and history.

For the real source FFN
`F(z)=W2 GELU(W1z+b1)+b2`, let
`O_F=(F(z)-F(-z))/2` and
`E_F=(F(z)+F(-z))/2`. Then for
original **nonzero** oriented charts ±,

    y_sigma(z) = sigma F(sigma z)
               = O_F(z) + sigma E_F(z),

and the exact chart jump is
`y_+(z)-y_-(z)=2E_F(z)`.
The source affine signed history transition
has pre-cap chart jump
`H_+-H_- = 2(T_y E_F(z)+b_T)`;
the real radial history cap is nonexpansive.
This does not assert learned `F` is odd and
does not omit original `b1,b2,b_T` biases.

A **new guarded approximate consumer** is available:
with identical selected expert set and admitted q
branch, an orientation sign flip need NOT be rejected
when the consumer only requires a bounded numeric
mixture/history discrepancy. It contributes an
explicit `2||E_F||` selected-output residual and
`2||T_yE_F+b_T||` pre-cap history residual, which
can feed the existing F07 layer-error transport.
To preserve the actual returned `signs` metadata,
strict chart parity remains necessary.
The source's `sigma=0` unique fixed point is
handled separately: its output/history are zero
even with internal learned biases.

**Sharp real GELU Lipschitz constant:** exactly

    Lg = (1+erf(1))/2 + exp(-1)/sqrt(pi)
       = 1.128904145185...,

improving the older loose bound
`1+1/sqrt(2*pi*e)=1.2419707245...`.
The biased FFN even component has centred
Lipschitz coefficient `Lg-1/2` and
a **quadratic curvature** majorant
`||E_F(z)-F(0)|| <=
 ||W2||*||W1 z||²/sqrt(2*pi)`.
This means small preactivations have a small
chart-even residual ONLY if the learned
`F(0)=W2 GELU(b1)+b2` is also small.

**Early F02a quantitative cross-pollination:**
for real Euclidean mirrored output pair `F+,F-`,
an odd student S obeys the exact identity

    (||F+-S||²+||F-+S||²)/2
      = ||E_F||²+||O_F-S||².

The minimum odd-only pair MSE floor is
`||E_F||²`; the exact output chart-jump
squared is `4||E_F||²`. The scalar/finite
Euclidean proof is checked with SymPy
(1,2,3,4 output coordinates), NOT falsely
promoted to an Agda-kernel accepted
inner-product F02b theorem.

**Gate status:** Source math / SymPy parity identities
and real bounds advanced; original fitted
`W1,b1,W2,b2,T_y,b_T` spectral norms, original
float GELU rounding, source chart/softmax precision,
and full future-history/semantic acceptance remain OPEN.
No model timing, GPU, Agda or CI run claimed.

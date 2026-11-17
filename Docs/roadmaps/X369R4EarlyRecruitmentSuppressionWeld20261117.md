

## 17 November strict-topk correction and executable closure route

**Mandatory correction to EARLIER historical paragraphs in this
roadmap:** the previous e3 configuration `s3=10, b3=-13`
produced a **TIE** at the second-step history probe after the
low-load prefix: `(8,3,7,7)`. Because the original source
uses `torch.topk`, expert 2 vs expert 3 could be chosen
for the second selected slot; source deterministic selection
was NOT established for that earlier fixture.
This is an actual logical error in the old history claim,
not a cosmetic numerical refinement.

**Repaired original source-shaped fixture** changes ONLY e3 to
`s3=11, b3=-16`. The corrected four original
reset-state score vectors at loads 0,1,2,3 are:

    (8,3,-11,-16), (8,7,-2,-5),
    (8,11,7,6), (8,15,16,17).

They retain the strict source topk sequence
`(0,1),(0,1),(1,0),(3,2)`, the same selected
scalar responses
`1/(1+e^5),1/(1+e),1/(1+e^-3),0`, and
canonical old `ResponseKink` Nat `(0,2,9,0)`.
The forced pair (0,1) still has the strictly
monotone source response `sigmoid(4t-5)`.

The corrected two original step histories share
probe load 2 and clock index 1:
- prefix load0 -> second-step logits `(8,3,7,6)`;
  unique top2 `(0,2)`, Nat0;
- prefix load3 -> second-step logits
  `(8,11,-11,-16)`; unique top2 `(1,0)`, Nat9.

An independent LOCAL six-case Python source-formula
audit checked all four reset-state and both
same-clock cases with strictly positive
selected-slot and selected/outside gaps:
**6/6 PASS**. The old tied witness must NOT
be promoted by relying on Python's sorting
order or CPU/GPU `torch.topk` tie behaviour.

**Executable implementation advances in original
LeechTransformer PR #5:**
- The existing reset-state checkpoint source producer
  now uses the shared `strict_source_order_margin`
  function to fail closed on source topk ties and
  record the minimum observed original score gaps.
- The same-clock history probe REUSES that same
  source margin helper at both prefix and
  probe steps, instead of duplicating the logic.
- The actual source-native synthetic regression
  now creates the repaired source-valid module
  weights, checks native `step`/
  `execute_selected` parity and source history,
  emits a genuine synthetic state_dict, then
  **runs BOTH original checkpoint and history CLI
  producers via subprocess**, reopens their
  JSON outputs and checks checkpoint SHA256,
  Nat `(0,2,9,0)`, same-clock Nat `(0,9)`,
  strict prefix/probe score margins and explicit
  non-certification of trained-model/float/
  general hysteresis conclusions.
- The previous JSON numeric-string parser fix,
  required original nonpersistent `history_cap`,
  controlled `dtype` and integer scale, and
  same-Nat forced-route comparison remain.

**Still-open acceptance:** these original
GitHub-native Torch scripts have been
source-written/committed but the complete
committed original source bundle has NOT
been run locally in this session because
the original repository checkout was
not accessible in this container.
The independent six-case exact-formula
audit is NOT a substitute for running
the actual source Torch model.
Agda kernel acceptance, real trained
checkpoint/source-history provenance,
independent numeric source error margins,
heldout semantic tests and general
hysteresis remain OPEN.
# X369 R4: early facilitation-before-suppression source weld

Date: 17 November 2026. Formal owner: DASHI PR #1526.
Original Leech-LILA architectural attribution: Anatolii Kornienko.
No ESD edits. SymPy only for numerical/analytic witness checking;
new Agda source is uncompiled unless a separate kernel receipt exists.

## Source audit: correct the early owner

The **canonical** 4-regime qualitative profile lives in
`DASHI/Cognition/ResponseKink.agda`, not in
`DASHI/Cognition/Utterance/AdmissibilityGate.agda`.
The latter exists but concerns literal/symbolic referent admission;
it defines no `RecruitmentSuppressionProfile`, `DriveStage`
or `profile-shape` in the inspected default branch.

`ResponseKink.RecruitmentSuppressionProfile` has strictly
`response(low)<response(prePeak)<response(peak)` and
`response(overload)<response(peak)`, with a canonical
`0→1→2→1` finite ordinal sample. This is an ORDER/SHAPE
contract, not a characterization of standard GELU itself.

Two already-existing consumers matter more than later GELU parity:
- `DASHI/Cognition/AnesthesiaLanguagePhaseDynamics.agda`:
  `canonicalKinkDynamics=marginDynamics 10 4 1 0`
  uses support `10+4t` versus impairment `t³`.
  `marginAt(t)` for `t=0,1,2,3` is exactly
  `+10,+13,+10,-5`. Its separate Schmitt-style phase
  demonstrates history-dependent collapse/recovery and an
  additional stack-rebuilding obligation. Those margin
  samples are **not** the same sequence as the 4-stage
  `RecruitmentSuppressionProfile`.
- `DASHI/Governance/SituatedHPARegimeFlexibilityExact.agda`:
  imports the canonical `ResponseKink` and gives a hypothetical
  ordinal load-response profile. It **explicitly rejects**
  interpreting that profile as an individual's cortisol level,
  deterministic trauma-to-exhaustion process, or clinical finding.
  Its independent `exposureCannotDetermineHPARegime` blocks
  determination of a regime from nominal exposure alone.

Also reused:
`DASHI/Cognition/DASHICognitionDynamicsRegression.agda`
imports the profile and
`DASHI/Cognition/CognitiveSystemAnalyticClosure.agda`
reuses the earlier cubic margin theorem. Later
`LeechGELUParityHistoricalSafetySteelman20261031.md`
is a DISTINCT parity/analytic donor, not the original
facilitation-before-suppression contract.

## Source-facing typed witness (new, no parallel profile)

`DASHI/Cognition/PNF/X369R4EarlyKinkSourceWeldExact.agda`
imports the **existing** `ResponseKink` and defines
`OriginalR4FourRegimeEvidence`, consisting of:
  (a) the declared original-source response observable,
  (b) an actual `RecruitmentSuppressionProfile` over
      the same four states, and
  (c) pointwise equality of that canonical profile response
      to the declared original source observation.

`sameSourceR4RiseAndOverload` transports the existing
profile-shape inequalities to the exact declared source
observable; no new general parity/GELU/kink owner is invented.
No original trained Leech expert/state observation is
supplied here, so this record is NOT asserted to be inhabited
by original R4. The source-written Agda bridge has not been
kernel-accepted in this session.

## Analytic/finite constructive cross-pollination (SymPy)

New exact-rational / SymPy checker:
`scripts/check_x369_r4_early_kink_sympy.py`.
An explicit **candidate**, not a source-R4 implementation, is

    A(t)=16/(16+t³),  t>=0,
    r(t)=(1+4t) A(t).

At the four input loads t=(0,1,2,3):

    r = (1,80/17,6,208/43).

Exact rational comparisons prove

    1 < 80/17 < 6
    208/43 < 6.

This discharges the OLD qualitative 4-stage profile for a
positive rational gain times a decreasing overload
attenuation. It does not prove a learned R4 uses r.

A second, analytic GELU-specific proposed family is

    g(t)=t Φ(t),   a(t)=g(t)16/(16+t³).

At loads 0,1,2,3 its values are approximately

    (0,0.791853878653,1.30299982407,1.11477220685),

and it also satisfies facilitation before overload
suppression. The order is supported by rigorous
rational inequalities, conditional on the standard
normal CDF/tail property. Mills' bound at 2 gives

    1-Φ(2) < φ(2)/2 < 1/8,
    so Φ(2)>7/8.

Therefore a(2)>7/6, while a(1)<=16/17 and
a(3)<=48/43, and a(0)=0. Thus

    a(0)<a(1)<a(2),  a(3)<a(2),

without needing delicate numerical comparisons for
the branch ordering. The committed script checks
the analytic values numerically with SymPy and the
rational margin inequalities. A formal certificate
for the normal-tail bound is still separate from
the finite Agda profile theorem.

Negative control: unattenuated `GELU(t)` is
strictly increasing for t>=0, so cannot satisfy
a descending overload limb on t=0,1,2,3.
The source history `cap_history` merely bounds the
history vector's norm; radial projection is NOT by
itself a theorem that the selected expert's response
declines under increased load. Nor does `topk`
guarantee the shape over an arbitrary parameter
sweep, without actual fixed-source response data.

Local independent reconstruction of the SymPy
candidate: **14 grouped checks passed**.
No actual trained checkpoint, source observed
response trace, Agda kernel or GPU runtime receipt.

## Correct remaining X369 R4 proof gates

1. **Choose a typed original-source response observable.**
   Examples requiring explicit interpretation:
   norm of selected expert contribution, margin to
   unselected experts, activation norm, admitted
   task-condition quality or route entropy. These are
   DISTINCT; none is interchangeable with an endocrine
   response or arbitrary symbolic proxy. Preserve the
   entire source context `(x,H,weights,revision)`.
2. **Define a four-state comparable load family** under
   same checkpoint, expert identity and authoritative
   history revision; determine what is held fixed or
   transitioned through the history dynamics.
3. **Source-bind exact response intervals** with the
   existing R4 quantiser/floating precision and
   q/topk/orientation chart certificates. To prove
   strict four-stage orders with interval responses
   I0,I1,I2,I3 require
   `sup I0<inf I1`, `sup I1<inf I2`,
   `sup I3<inf I2`.
4. **Distinguish mechanism**: a baseline GELU FFN
   alone is not the old whole-system shape.
   Attribute any descending limb to an observed
   attenuation, resource competition, topk change,
   recurrence, cap interaction or feedback, not
   to plain GELU. A mechanism claim needs a controlled
   source ablation; a shape receipt alone is insufficient.
5. **Retain the previous strongest mathematical gates**:
   the correlated relative-score quantizer bound,
   mixed-q and selected orientation/FFN sign-chart
   residual, inactive expert-history authority and
   the prior `LeechLayerErrorTransportExact` F07
   conditional recurrence. The early Kink theorem
   is a different SOURCE CONSUMER and must not be
   inferred from scalar score or GELU parity equality.
6. **Keep semantic, biological and causal types apart**:
   no claim that a four-level ordinal HPA toy curve
   proves a clinical mechanism or that ± neural
   orientation defines moral opposition.

This corrects the attribution and turns the early
Agda contract into a reusable R4 evidence consumer,
rather than replacing it with later parity algebra.


## Source-receipt acceptance surface

`scripts/check_x369_r4_kink_source_receipt.py` is a read-only
exact-rational interval checker for the old original
`ResponseKink` three inequalities. It requires four
strictly ascending source loads, stage IDs, a common
declared checkpoint SHA and original history revision,
one explicitly typed response observable, and
source-state/export/error provenance flags. All three
strict response orders must be separated even after
admitted interval uncertainty. The script refuses
overlapping response intervals, ties, mixed source
revisions, mixed observables, and missing evidence.
It explicitly does **not** hash checkpoint bytes
or certify original source execution.

`scripts/check_x369_r4_kink_source_receipt_selftest.py`
adds **14 synthetic cases**: one accepted rational
envelope and 13 adversarial rejected variants.
These are regression fixtures, not authenticated
original R4 experiments. `selected` in the
old four-stage response profile means a qualitative
coherence regime, not necessarily membership in
the source model's `torch.topk` selected expert IDs.

Source Agda file:
`DASHI/Cognition/PNF/X369R4EarlyKinkSourceWeldExact.agda`,
which imports existing canonical `ResponseKink`
without copying the profile owner. Kernel
acceptance remains unclaimed.


## Nat-response type boundary closed for the constructive fixtures

The original `Kink.RecruitmentSuppressionProfile`
requires `response : Input → Nat`, not a rational or
real response. The continuous candidate inequalities
alone therefore cannot directly instantiate that type.

Updated `scripts/check_x369_r4_early_kink_sympy.py`
checks an explicitly chosen **monotone scalar-to-Nat
observation** and its POST-QUANTISATION margins:

    floor(rational(t))    = (1,4,6,4),
    floor(10*GELU(t)A(t)) = (0,7,13,11),

for original ordered loads t=(0,1,2,3).
Both have strict `low<prePeak<peak`
and `overload<peak`, as the canonical
Agda shape requires.

The same `floor` with scale 1 on the
GELU envelope erases the rise and FAILS
the shape. This is the necessary negative
control: a monotone codec can destroy strict
ordinal inequalities if its precision is too
coarse. A future source-bound Nat consumer
needs separately calibrated strict cell
margins, not just real-valued profile shape.

A stronger rational bound `Phi(2)>15/16`
follows from `phi(2)/2<1/16`;
it yields `GELU(2)*16/24>5/4`,
while the overload response is at most
`48/43`. Therefore under scale-10
floor quantisation, the peak code is
at least 12 while overload code is
at most 11, with strict order guaranteed.
The actual finite evaluation gives
peak code 13 and overload code 11.
The independent local SymPy reconstruction
now passes **19 grouped checks** including
this Nat bridge and the erasure control.

These are finite mathematical witnesses,
not real checkpoint source observations.
The `OriginalR4FourRegimeEvidence`
Agda interface requires a true
`Nat` source response and its same-source
provenance equality before transporting
the old qualitative theorem.


## Receipt tightened to the canonical Nat type

The source adapter now refuses a generic real-valued
response record masquerading as the Agda
`ResponseKink` owner. It explicitly requires
`response_codomain="Nat"`,
`nat_observation_source_verified=true`, and
a nonnegative integer `response_nat`
for every source stage, **enclosed by its
corresponding authenticated error interval**.
A real source observable must be quantised
to Nat by a separately sourced observation
map whose cell margins are checked.

The companion test now contains
**18 synthetic test cases** (one accepted,
17 adversarial rejections), with a
Nat response `(1,4,6,4)`.
New negative cases reject an unverified
Nat projection, an incorrect Real codomain,
a string where the response must be Nat,
or a reported Nat value outside its
declared interval. This is a SOURCE WRITTEN
test suite without a separate full-file
execution receipt; the 19 local SymPy
constructive-shape checks are distinct.

The source checkpoint and provenance flags
are **declarations**, not independent
cryptographic or FP authentication.
Source measurements and a verified projection
are still required to instantiate the
original Agda profile on a trained model.


## 17 November continued max-cut — original coherent R4 top-k replacement produces the early kink

**New executable original-source algebra:**
`scripts/check_x369_r4_topk_kink_sympy.py`.
**Composition with existing R4 quantisation certificate:**
`scripts/check_x369_r4_topk_kink_source_gate_sympy.py`.

This is stronger than the earlier **proposed**
`GELU(t)*16/(16+t³)` attenuation curve:
the new construction uses ONLY actual
`HistoryOrbitMoE` R4 scorer, learned expert
biases, `torch.topk` + selected softmax,
the original signed selected FFN with
a source-licensed constant-output
parameter choice, and source-owned
original history. There is NO new
attenuation gate and no altered R4
algorithm. It proves the architecture
*can* instantiate the original
`ResponseKink` contract; it does
NOT claim a fitted checkpoint does so.

### Source-shaped original numerical fixture

Use the original coherent `c2_c3_residual`
branch, d=6 (two complete original
C3 triads), E=4 experts, k=2.
Fix the SAME initial retained history
for every independent activation-load
counterfactual. Set the baseline C2
router history coefficients to zero,
the shared C3 directed head to
`w=(1,0,0,0,0,0)`, and expert
histories `h_e=(1,0,s_e,0,0,0)`
with slopes `s=(0,4,9,10)`.
Set the source's learned
`expert_bias=(8,3,-11,-13)`.
Set activation `x(t)=(t,0,0,0,0,0)`
for t=0,1,2,3.

The original source coherent C3 phase
rotates the first activation triad
`(t,0,0)` into `(0,0,t)`.
Therefore its ORIGINAL fused directed
residual equals `s_e*t`; the common
unary x terms cancel from relative
logits. Exact source logits are

    L_e(t) = s_e*t + expert_bias_e.

Choose original source-compatible
orientation weights reading `h_e[0]`
and no orientation bias, so every
selected sign score equals 2>0
(no sign tie at any load).
Choose each original FFN's final
linear weights zero and output
bias `y_e=(0,1,0,0)` on one
emitted channel, and the selected
history transition zero. These
are allowed **parameter choices**,
not actual learned Leech weights.
The original R4 code and GELU
remain unchanged: GELU hidden
values simply do not affect the
constant output under W2=0.

| Load t | Original four logits | Strict ordered top2 | Weighted response |
|---|---|---|---|
| 0 | (8,3,-11,-13) | (0,1) | 1/(1+exp(5)) |
| 1 | (8,7,-2,-3) | (0,1) | 1/(1+exp(1)) |
| 2 | (8,11,7,7) | (1,0) | 1/(1+exp(-3)) |
| 3 | (8,15,16,17) | (3,2) | 0 |

The selected/unselected margins
are at least 1 at every stage;
the two ordered selected slots
also have strict gaps (5,1,3,1).
A tie between two unselected
experts at t=2 is irrelevant to
the certified top2 order because
both remain strictly below the
second selected expert.

Use the OLD `ResponseKink`
`Nat` observation scale 10.
Elementary `8/3<e<11/4`
bounds on the exponential prove
the four Nat buckets exactly:

    Nat(floor(10*response))=(0,2,9,0).

This witnesses
`low<prePeak<peak` and
`overload<peak` for the
**ORIGINAL R4 SOURCE ARCHITECTURE**
under the disclosed parameters.

### Matched mechanism ablation / no-go

Keep the SAME inputs, histories,
expert parameters and learned
relative logits, but hold the
selected pair at `(0,1)` and
renormalise their logits through
the SAME source softmax. This is
an explicit counterfactual selected
subset (supported conceptually by
the original `execute_selected`
consumer), not what native routing
would select at overload t=3.
The selected expert-1 weight is
now

    p1(t)=sigmoid(4t-5),

strictly increasing in t because
`p1'(t)=4*p1*(1-p1)>0`.
No overload decline remains.

Consequently **sparse competition /
selected-set replacement is
sufficient** to generate the old
shape in the original R4 model,
even with constant FFNs, no
learned attenuation and zero
transition. This is a genuine
mechanism-specific *architectural
possibility* with a matched control.
It does not establish topk
competition as the mechanism in
the actual trained checkpoint.

### Combined q/topk/orientation/precision and Nat interval gate

The companion
`check_x369_r4_topk_kink_source_gate_sympy.py`
reuses the EXISTING independent
`check_x369_r4_source_receipt.certify`
instead of rebuilding a decision
certificate. At each load it
presents the same hypothetical
checkpoint SHA, original
source-authenticated-state flags,
same expert histories, original
orientation row, and coordinate
precision tolerances 1/65536.
It requires original source-selected
IDs, strictly verified TopK
membership and ordered slots,
and selected orientation margins.

For the coherent branch, the
topk/phase mask is fixed. It
uses the pairwise selected-score
error bound / selected softmax
variation to enclose the
source response with rational
exponential brackets. The
resulting response interval is
required to lie in ONE post-scale-10
`Nat` cell at each load,
not merely have ordered
central values.

The approximate admitted interval
is robust:
- t=0 response ≈0.0067,
  Nat=0;
- t=1 response ≈0.26894,
  Nat=2;
- t=2 response ≈0.95257,
  Nat=9;
- t=3 response exactly 0
  because neither selected
  expert emits a nonzero
  value, Nat=0.

The external checkpoint/export/
float-error attestations in this
fixture are **synthetic declared
premises**, not real SHA verification
or a calibrated Torch binary32
error receipt. The companion
refuses source-incorrect frozen
IDs at overload and attempts to
promote an uncertified mixed-q
tie at t=0. These are necessary
boundary tests, not actual
original model validation.

### High-alpha theorem / what remains

For constant original expert
histories and activation ray
`x(t)=t x0` under fixed
coherent C3 phase, the original
relative logits are affine
`L_e(t)=a_e t+b_e`.
With a FIXED top2 selected pair
and constant emitted expert
outputs, the scalar mixture is
a logistic interpolation of
two constants and so is
monotone in t. A non-monotone
four-stage response of this
restricted class must come from
selected-pair changes or an
explicit change in the emitted
expert output/other admitted
source consumer. Original
mixed-null phase q is stable
on strictly positive rays because
q scales quadratically, but
at zero load a mixed gate is
generically ambiguous under
quantization; the coherent
witness is not silently promoted
to the mixed arm.

Next physical/fitted gate:
export a real checkpoint and
four source response states
with fixed experimental
semantics and authenticated
hidden-history revisions;
compare actual source output
and fixed-route counterfactual
at matched loads, then test
history feedback and cap
interactions separately. If
a real source shows a
non-monotone Nat response,
the existing Agda
`OriginalR4FourRegimeEvidence`
can consume its strictly
certified Nat observation.

**New source construction is not
a measured trained-model result,
a claim that GELU is
overload-decreasing, a clinical
analogy, or an Agda kernel
acceptance.**


### Matched canonical Nat Agda fixture and full receipt composition

The source-written finite constructive witness now has its
own reuse-only Agda source:
`DASHI/Cognition/PNF/X369R4TopKSourceKinkWitnessExact.agda`.
It imports both **original** `ResponseKink` and the
earlier source-transport `X369R4EarlyKinkSourceWeldExact`,
encodes `r4FixtureNatResponse=(0,2,9,0)` over
the ORIGINAL `DriveStage`, supplies explicit Agda
natural-order evidence, and transports that record
through `sameSourceR4RiseAndOverload`.
This proves the **finite shape for the declared
fixture data**, not Torch equivalence;
no Agda kernel acceptance is asserted.

The source-gate script now actually invokes
BOTH existing consumers:
`check_x369_r4_source_receipt.certify` for
strict original coherent topk and orientation,
and `check_x369_r4_kink_source_receipt.certify`
for the same-checkpoint/history, ordinal
four-regime response. Its outputs are
explicitly labelled conditional and synthetic
(checkpoint hash is placeholder `0` repeated).
The analytic response intervals are
projected to a single strict Nat cell BEFORE
the latter receipt is constructed.

The elementary numerical constant `e`
is enclosed analytically by
`8/3<e<87/32<11/4`:
the first four exponential-series terms
sum to `8/3`, and the positive
tail from `1/4!` is bounded by the
geometric sum `5/96`. These rational
bounds, not a floating evaluator's
approximation alone, justify the
reported response cells.

An **independent local reproduction** of
the source relative-logit arithmetic,
coherent selected IDs, pairwise
rational error budgets and source Nat
interval cell tests returned:

| t | Ordered selected | Minimum cross-score gap | Pairwise selected error budget | Admitted response interval | Nat |
|---|---|---:|---:|---|---:|
| 0 | (0,1) | 14 | 0.00015259 | [0.006280,0.007399] | 0 |
| 1 | (0,1) | 9 | 0.00024415 | [0.266606,0.272788] | 2 |
| 2 | (1,0) | 1 | 0.00033570 | [0.949823,0.954206] | 9 |
| 3 | (3,2) | 1 | 0.00019837 | [0,0] | 0 |

These local computations instantiate the
SAME symbolic formulas as the new
committed scripts. The entire committed
files were not run from GitHub as files,
and the synthetic float/source-provenance
premises have NOT been verified against
an actual checkpoint or original Torch
kernel. Device tests and kernel promotion
remain separate.

### The next true original-source gate

The architecture-level **existence** of
an R4 early-kink mechanism through
topk replacement is now settled by a
specific matched source-shaped witness.
The open question is **whether an
actually trained model and a specified
real response observable exhibit it**.
Next use the existing native original
R4 runner/checkpoint hash producer,
source fixed-state load interventions,
matched forced-topk replay and
layer-wise selected-FFN/transition
observations. A static four-point
response shape cannot establish
on-policy hysteresis or physiological
causation; keep those as separate
evidence branches.


## 17 November source-execution max-cut — original Leech producer now implemented

Original repository: `chboishabba/LeechTransformer`, existing PR #5,
branch `experiment/x369-r4-fair-c2c3-residual-20261115`.

**No surrogate router was introduced.** Existing
`models/history_orbit_moe.py` now accepts optional
`select_source_experts(x,history,return_logits=True)`,
returning `(ids,weights,logits)` from the SAME original
route/score computation. Its default
`return_logits=False` preserves the original
2-tuple API and ordinary training/inference semantics.

New original-source consumers:
- `scripts/check_x369_r4_native_topk_kink.py`:
  CPU smoke test of the ACTUAL HistoryOrbitMoE class
  with source-valid synthetic d=6 coherent R4
  weights and histories. Checks source logits,
  native topk slots, signed expert FFN output,
  source `step` versus `execute_selected`
  replay and full selected histories;
  asserts the strict Nat response `0,2,9,0`.
  The *matched* fixed pair [0,1] has
  strictly increasing response and
  no overload limb.
  Optional `--emit-probe-dir` creates a
  genuine native **synthetic** state_dict
  and matching four-load JSON for
  the checkpoint probe.
- `scripts/probe_x369_r4_kink_checkpoint.py`:
  exact original-source same-checkpoint
  CPU probe. Uses weights_only
  `torch.load` and `strict=True` state
  dictionary admission (an explicit
  `--state-prefix` handles module
  embedding), computes real checkpoint
  byte SHA256, source input and history
  byte SHA256, retains original all-E
  inactive histories, and independently
  resets the SAME history for four
  increasing activation loads.
  Evaluates original `select_source_experts`,
  `step`, and `execute_selected`,
  rejects same-source selected/sign/history
  replay mismatch, and computes an
  actual-source-logit/softmax-based
  forced-route selected-only ablation.
  Its response type is explicit
  coordinate or L2 norm; Nat
  projection uses an explicit scale.
  The return JSON separates native
  `nat_kink_observed` from
  `fixed_route_continuous_kink_observed`,
  and **explicitly** marks
  `certified_float_error_intervals=false`,
  `recurrent_hysteresis_certified=false`
  and heldout quality uncertified.
- `docs/x369_r4_native_kink_probe.md`:
  usage instructions and source
  promotion/non-promotion boundaries.

To run from the original Leech
repository root with installed
source dependencies:

```bash
python scripts/check_x369_r4_native_topk_kink.py \
  --emit-probe-dir .leech-r4-kink
python scripts/probe_x369_r4_kink_checkpoint.py \
  --checkpoint .leech-r4-kink/synthetic_history_orbit_moe_state_dict.pt \
  --input .leech-r4-kink/synthetic_original_load_input.json \
  --output .leech-r4-kink/synthetic_probe_result.json
```

**Independent LOCAL exact-rational verification COMPLETED**
in this conversation of the source formula and its
correlated paired-error/response Nat cells,
for each load t=0,1,2,3:
- logits `(8,3,-11,-13)`,
  `(8,7,-2,-3)`, `(8,11,7,7)`,
  `(8,15,16,17)`;
- strict ordered top2 `(0,1)`,
  `(0,1)`, `(1,0)`, `(3,2)`;
- exact Nat `(0,2,9,0)`;
- synthetic pairwise score errors and source
  Nat interval margins remain admitted.

That local rational audit reproduced
the corresponding symbolic mathematics.
**The exact committed original Torch scripts,
the fitted checkpoint and the new Agda
modules have NOT been executed or kernel
accepted** in this chat.

Both TOE entry points now import the
canonical finite R4 kink witness with
the unique `r4FiniteKinkSourceShape`
public projection:
`DASHI/EverythingTOESymmetryResolved369.agda`
and `DASHI/Unified/Everything.agda`.
No change to the core early
`ResponseKink.agda` owner or ESD modules.

**Remaining decisive physical/source gates:**
real owned R4 source checkpoint + actual
history revision, four-load choice with
measured source response, actual counterfactual
replay, independently certified floating
interval/Nat-cell errors, original R1/SLR
development/heldout provenance, and true
on-policy recurrent hysteresis (not a
reset-history comparison). No
clinical/endocrine claims.


## 17 Nov continuation: source-native checkpoint runner repair + original R4 same-clock history gate

Original Leech PR #5 updated, with:
- `models/history_orbit_moe.py`: default original
  `select_source_experts(x,h)` tuple unchanged; explicit
  opt-in `return_logits=True` returns SAME
  calculated original source logits (not a
  separately computed router).
- `scripts/probe_x369_r4_kink_checkpoint.py`:
  original checkpoint-byte-hashed same-reset
  four-load source execution and matched
  source-logit forced selection.
  **Repaired actual runnable blocker:** its
  JSON input uses numeric strings, which
  `torch.tensor(["1","0"],dtype=...)`
  rejects. The original producer now
  recursively parses only finite
  numeric scalar strings/integers/floats
  into the requested exact source tensor
  shape and rejects NaN, Inf, Bool and
  invalid shapes, plus disallows
  implicit dtype or coerced Nat scale.
  Added original repo-root source
  package path handling for
  `python scripts/...py`.
  The forced-route comparator now
  checks its **same Nat projection**
  separately from continuous shape;
  the result explicitly marks that a
  fitted causal mechanism is NOT
  certified.
- `scripts/check_x369_r4_native_topk_kink.py`:
  synthetic native model/FFN/topk test
  now verifies default API and opt-in
  logits agree, emits source state_dict,
  reloads the exact bytes with
  `strict=True`, replays source step
  and selected-only execution, and
  rejects malformed JSON arrays.
- `scripts/probe_x369_r4_history_path_dependence.py`:
  NEW same-checkpoint, same initial
  full history, same second-step load
  and clock, different one-step
  *prefix interventions* followed by
  the original source `step`.
  Unlike a four-load RESET curve,
  this tests a genuinely updated
  ORIGINAL recurrent history state.
  It records full-history hashes and
  selected scores/IDs/weights/signs.

**Exact independent history-path source mathematics:**
the previous source-legal d=6,
E=4 synthetic parameter fixture
has original coherent routing

    L_e(t)=b_e+s_e*t,
    b=(8,3,-11,-13),
    s=(0,4,9,10).

After a prefix load 0, original
topk selects (0,1) and ZERO source
transitions replace their histories
with zero; at the common second-step
load t=2 the logits are
`(8,3,7,7)`, selected (0,2),
output Nat 0.
After a prefix load 3, topk
selects (3,2), whose histories
are replaced with zero; at the
SAME second-step t=2 and same
clock index 1 the logits are
`(8,11,-11,-13)`, selected (1,0),
output Nat 9.
An independent exact-source-formula
local run checked **4/4** finite
history-path facts. This is a
counterexample to inferring a
same-load source response from the
load scalar ALONE when the active
retained histories may differ.

**Existing mathematical reuse:**
new `DASHI/Cognition/PNF/X369R4HistoryLoadNonFactorabilityExact.agda`
imports `DASHI.Core.IntersectionalNonFactorability`
(not a duplicate quotient constructor).
It defines a two-prefix same-load
finite witness and exposes the
already-proved generic
`witnessRulesOutEveryFlatFactorisation`
and recharting no-recovery laws:
the declared Nat response 0 vs 9
does not factor through the common
second-step load. This source-written
Agda result is exposed from BOTH
`DASHI/EverythingTOESymmetryResolved369.agda`
and `DASHI/Unified/Everything.agda`.

**Local verification performed this round:**
- exact rational/symbolic source
  four-load scores, selected experts,
  native-response Nat 0,2,9,0,
  frozen-route monotonic response:
  **17 independent source-formula checks PASS**;
- original PyTorch numeric-string
  deserialization defect reproduced
  with installed CPU Torch; corrected
  parsing function independently
  reproduced and passed **7 CPU checks**;
- exact same-clock path dependence:
  **4 independent source-formula checks PASS**.

**Still open:** executing exact GitHub
native Torch fixture/probe scripts,
kernel-checking new Agda/TOE imports,
same-source actual R4 checkpoint/history
provenance, independent true
source floating-error bounds across
Nat observation thresholds,
experimentally selected four-load
family, heldout generalisation,
and genuine on-policy recurrent
hysteresis. The current same-clock
two-prefix inequality is
history-dependence, not proof of a
hysteresis loop or biological
allostatic mechanism.

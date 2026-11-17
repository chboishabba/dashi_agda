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

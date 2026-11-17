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

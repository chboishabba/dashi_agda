# X369 R4 relative-error maximum cut — 17 November 2026

**State:** SymPy proof development; no source checkpoint, Torch/ROCm,
hardware-float or Agda kernel acceptance. Source modules inspected:
`LeechTransformer/models/history_orbit_moe.py` (original R4 branch)
and `models/trialectic_wave_prior.py`.

## 1. What changed

The earlier independent full-logit error envelope is safe but often
unnecessarily pessimistic: each expert logit includes the SAME unary
`x` term and the SAME `nn.Linear` bias. In exact real arithmetic,
those terms cancel from both selected TopK comparisons and softmax.
The correct decision quantity is the **relative expert logit**:

    d_ij = [v·(|h_i|-|h_j|)]
         + [<K_w phase(x),h_i-h_j>]
         + bias_i-bias_j.

Source C2-history and directed C3 score owners remain distinct.
The new symbolic auditor is
`scripts/check_x369_r4_relative_certificate_sympy.py`.
The shared offset is retained for absolute logit observers; the
reduction is only claimed for ranking/selected-softmax consumers.

For any calibrated pairwise error interval `delta(d_ij) ∈ [l_ij,u_ij]`,
an admitted original ordering i>j survives when

    d_ij + l_ij > 0.

This permits correlated quantiser errors (e.g. common rounding terms)
to cancel **before** constructing independent coordinate budgets.
When only independent expert envelopes `B_i,B_j` are available,
the conservative sufficient test is `d_ij > B_i+B_j`.
Strict membership tests every selected/unselected pair.
Strict ordered slots also compare each adjacent selected pair.
No tie-policy parity is claimed on source `torch.topk` ties.

## 2. Tighter softmax and mixture bound

For the selected, ID-aligned perturbation vector `delta`, define

    osc(delta) = max_i(delta_i) - min_i(delta_i).

Since softmax is invariant under common shifts, subtract the midpoint
of this range and apply the softmax Jacobian (infinity→L1 operator
norm ≤ 1). This gives the sharp-to-first-order general envelope

    ||softmax(s+delta)-softmax(s)||_1 <= osc(delta)/2.

The previous bound `<= ||delta||_infinity` follows immediately but
can be arbitrarily looser for almost-common perturbations.
A purely interval-derived bound is

    osc(delta) <= max_i upper(delta_i) - min_j lower(delta_j).

Correlated pairwise-error certificates can improve on even this.
Given `||y_e||<=M` and `||y'_e-y_e||<=Y`,
the source one-step output mixture satisfies

    ||o'-o|| <= (M/2)*osc(delta) + Y

under the admitted same-selected-ID conditions. This is an
exact-real inequality; Torch softmax rounding and accumulation need
an independent precision budget.

## 3. Source q-gate threshold correlation

Actual mixed-null branch:
`flip_j = [q_j > (1/m)Σ_k q_k]`, XOR fixed base mask.
If `|delta q_j|<=Q_j`, the **sharper** deviation bound is

    |delta(q_j-mean(q))|
        <= ((m-1)/m)*Q_j + (1/m)*Σ_(k != j) Q_k.

This exploits the fact that q_j contributes to the mean.
The old bound `Q_j+mean(Q)` unnecessarily double-counted Q_j.

For each triad let `I_j=[d_j-R_j,d_j+R_j]`,
`d_j=q_j-mean(q)`. The source's strict comparison is certified
TRUE if `I_j.lo>0` and FALSE if `I_j.hi<=0`.
If neither holds, **the q branch is unverified**; one must not
apply a fixed-phase quantizer score bound. At an exact threshold tie
with nonzero error, reject or separately prove the unchanged branch.
For m=2, the new radius is `(Q0+Q1)/2` instead of
`(3Q0+Q1)/2` for the first triad.

## 4. R4 rational source witnesses

Two original triads, E=4, topk=2, with original source values
from the preceding end-to-end envelope.

| Branch | Original scores | Certified ordered top2 |
|---|---|---|
| Coherent C3 | (3,4,13,11) | (2,3) |
| Mixed q-gated C3 | (5,2,9,17) | (3,2) |

Input, history, baseline-history coefficients, directed residual
head coefficients each use separately admitted rational absolute
error 1/256, and expert bias error 1/256. Per-expert score
budgets are exactly:

    (594441,824201,824201,824201)/8388608.

The new symbolic audit retains the original strict top2 guards and
adds the correlated mean-q interval logic, exact relative offset
cancellation, a negative-control q threshold tie, selected
orientation sign margins, the source GELU differentiation, and
a five-step nonautonomous state-discrepancy identity.

The *full-length local development script* is independently executed
in this chat: 20 grouped checks passed. The trimmed
repository script includes the same core formulas and fixtures;
a separate execution receipt of that exact committed version
has not been obtained. No cloud CI run is asserted.

## 5. What is and is not enough for future recurrence

The source selected-history transition computes `h'_e` before
using the selected softmax weight, so a pure weight perturbation
with the same activation, selected set, orientation and model
does not change the selected expert's immediate history.
The emitted mixture changes, however, and can change downstream
activations, routing and eventually that expert's future history.
Inactive histories must remain available at their authoritative
source; selected-only transmission is not global-state compression.

To certify a future trace, inductively require at **each** time:
1. source q-mask accepted (mixed arm);
2. selected-vs-unselected and within-selected relative score
   intervals have strict ordering (or source-identical tie receipts);
3. selected orientation sign chart remains nonzero and stable,
   including the first-nonzero fallback if a zero score is admitted;
4. independently sourced float precision/quantizer evaluation error
   budgets, GELU/FFN/transition operator norms and cap evaluation
   bounds;
5. selected-execution source revision plus all inactive histories
   retained/reopened at original authority.

Only then a conditional `D_{t+1}<=L_t D_t+eta_t` can be propagated;
its exact n-step expansion is

    D_n <= D_0 * Π_(k=0)^(n-1) L_k
           + Σ_(j=0)^(n-1) eta_j Π_(k=j+1)^(n-1) L_k.

This is a **guarded induction schema**, not an observed original
Leech execution. Also, `nn.GELU` is the source FFN activation;
a conservative real derivative bound is
`1+1/sqrt(2*pi*e)`, but source checkpoint norms remain unmeasured.

## Next max-cut

The next decisive original-source weld is a pairwise correlated
quantization receipt `(i,j)↦[l_ij,u_ij]`, with precision provenance
and a declared score-evaluation rounding budget. This can be
reused for TopK ordering, softmax oscillation, output mixture and
recursive margins. Semantic consumers still have independent
grokking/Sophontic/trialectic-face non-descent gates.

Attribution: original Leech-LILA Anatolii Kornienko; DASHI
mathematical formalisation follows the pre-existing original-source
owner graph. No ESD surfaces changed.


## Round 3: directly certified pairwise R4 errors

New independently tested SymPy owner:
`scripts/check_x369_r4_pairwise_sympy.py`.
For a fixed certified coherent/mixed phase,
write `H=h_i-h_j`, `Delta H=Delta h_i-Delta h_j`,
`u=K_w phase(x)`, and `Delta u` its shared fused-coefficient
error. Exact polynomial:

    Delta(<u,H>) = <Delta u,H> + <u,Delta H>
                    + <Delta u,Delta H>.

For `|Delta u_l|<=U_l` and independent history
errors, a sufficient pairwise directed envelope is

    B_ij^directed = Σ_l [
      U_l |h_i,l-h_j,l|
      + (|u_l|+U_l)*(eps_hi,l+eps_hj,l) ].

For the shared C2 head `v_l`, put
`A_l=|h_i,l|-|h_j,l|`. The absolute value's
1-Lipschitz law gives

    B_ij^C2 = Σ_l [
      |v_l|*(eps_hi,l+eps_hj,l)
      + eps_v,l*(|A_l|+eps_hi,l+eps_hj,l) ].

Add the bias-difference error, and *separately*
the differential source floating-evaluation
error. The total strict decision condition is

    source_score_i-source_score_j > B_ij.

To preserve the ordered TopK source output,
apply this to all selected/unselected pairs
and all adjacent ordered selected pairs.
Original `torch.topk` equality/tie policy,
q-mask branch and orientation sign have
independent admissions.

This is strictly more informative than adding
two isolated full-logit error budgets: shared
x/w perturbations multiply `h_i-h_j`,
not `h_i` and `h_j` independently. Independent
history-quantizer errors remain bounded
separately unless shared representation
provenance establishes their correlation.

**Direct local SymPy execution: 20 grouped checks PASS.**
Source rational coherent fixture has ordered
top2 `(2,3)` and error tolerance 1/256
for every declared input/head/history channel
and expert bias. Every selected/outside
strict pair, selected internal gap,
all six perturbed pair intervals and the
mean-q correlation algebra pass.

Measured *symbolic bound tightening*
for selected pair (2,3):

    independent B2+B3 = 1648402/8388608 ≈ 0.196505
    pairwise B23        = 1185801/8388608 ≈ 0.141358

i.e. **28.1%** less conservative. For selected
(2) against outside (0), the bound changes
from `1418642/8388608` (≈0.169115)
to `956041/8388608` (≈0.113969),
**32.6%** less conservative.

These numbers are exact RATIONAL FIXTURE
envelopes, not a physical quantiser,
trained model or device uncertainty
measurement. No Agda/CI/GPU acceptance
is implied.

**Next maximum cut:** extend this pairwise
relative-error object to source **all-triad**
tensor scores and the COMPLETE baseline C2
h-half plus expert bias under independently
declared per-coordinate precision conventions,
then instantiate the same relative envelope
for softmax oscillation and a guarded
selected-history trace. Do not require
a false exact reconstruction of original
directed activations, and retain independent
semantic/face consumer evidence.

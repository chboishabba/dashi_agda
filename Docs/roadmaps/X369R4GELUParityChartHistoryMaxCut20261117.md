# X369 R4 GELU parity, chart residual and recurrent error — donor weld

**Date:** 17 November 2026. **Owner:** DASHI PR #1526; source original
Leech-LILA by Anatolii Kornienko. **Runtime/precision:** source R4
`LeechTransformer/models/history_orbit_moe.py` and
`models/trialectic_wave_prior.py`, no fitted checkpoint or GPU/Agda run.
**SymPy implementation:**
`scripts/check_x369_r4_gelu_parity_history_sympy.py`.
Existing end-to-end consumer revised in
`scripts/check_x369_r4_end_to_end_envelope_sympy.py`.

## 1. Precise older Agda owners, reuse before construction

Read and retain these ORIGINAL donors:

- `Docs/LeechGELUParityHistoricalSafetySteelman20261031.md`
  (31 October): analytically states the scalar
  `GELU(-t)=GELU(t)-t`, odd linear `t/2`, even nonlinear
  `t erf(t/sqrt(2))/2`. It explicitly distinguishes the
  real normal-CDF identity, abstract involution, and PyTorch
  precision. This is not an Agda-kernel accepted normal-CDF proof.
- `DASHI/Reasoning/LeechSignedHistoryExpertBidiExact.agda`:
  `invertHistory` acts on **both** activation and history;
  `conjugateIntertwinesInverse` owns the finite two-chart
  commuting square. Do not invent another sign carrier.
- `DASHI/Reasoning/LeechOddOnlyApproximationObstructionExact.agda`:
  F02a `historyOddCannotMatchNonOddPair` proves that an odd-only
  student cannot fit both mirrors when the original target
  violates oddness. F02a does NOT prove a quantitative norm bound.
- `DASHI/Reasoning/LeechLayerErrorTransportExact.agda`:
  F07 `traceErrorBound` is a conditional finite
  teacher/student discrepancy majorant using actual supplied
  `lipBound` witnesses. No original trained Lipschitz
  constants are claimed.
- `DASHI/Physics/YangMills/PhysicalInvolutionParityExact.agda`:
  already owns the generic `Involution`, `OddUnder`,
  `EvenUnder` and pair-cancellation interface.
- `DASHI/Cognition/ResponseKink.agda` is a qualitative
  recruitment/suppression surface, NOT a numerical GELU
  nonmonotonicity or derivative owner.
- `DASHI/Visualisation/QuantisedSearchBoundsExact.agda`
  distinguishes preactivation versus activation quantisation,
  clipped-fibre collisions and strict ranking margins.
  Retain this distinction on the FFN nonlinear path.

No new competing generic Agda GELU definition was introduced.
This continuation is a **source-specific analytical/consumer weld**,
with exact SymPy development and the existing Agda owners as its
formal antecedents. A real CDF/erf proof in Agda remains separately
open rather than being smuggled in by an axiom or a numeric test.

## 2. Recover exact GELU parity on reals

For `g(t)=t Phi(t)` and `Phi(-t)=1-Phi(t)`,

    g(-t)=g(t)-t,
    O_g(t)=(g(t)-g(-t))/2=t/2,
    E_g(t)=(g(t)+g(-t))/2=t erf(t/sqrt(2))/2.

Thus `g=O_g+E_g`, with linear odd part and nonlinear even
part. GELU is NOT an odd gate. The source learned FFN has
biases, so this scalar decomposition is NOT a theorem that the
whole source expert is an odd linear map plus only this same
componentwise E_g on original z.

## 3. Source-exact sign-oriented FFN with *learned biases*

For one selected original R4 expert, let
`z=concat(x,h_e)` and

    F_e(z)=W2_e GELU(W1_e z+b1_e)+b2_e.
    y_(e,sigma)(z)=sigma F_e(sigma z), sigma=±1.

Define its parity RELATIVE TO THE FULL SIGNED INPUT:

    O_e(z)=(F_e(z)-F_e(-z))/2
    E_e(z)=(F_e(z)+F_e(-z))/2.

The source y has the EXACT factorisation

    y_(e,sigma)(z)=O_e(z)+sigma E_e(z),
    y_(e,+)(z)-y_(e,-)(z)=2 E_e(z).

For b1=0,

    O_e(z)=(W2 W1 z)/2,
    E_e(z)=W2 E_g(W1 z)+b2.

With nonzero b1, use the full **biased** F_e mirror average.
In particular

    E_e(0)=F_e(0)=W2 GELU(b1)+b2.

Thus changing chart can cause an order-one output jump even
at arbitrarily small nonzero z if F_e(0) is not small. DO NOT
drop learned biases. The source `nn.GELU()` default uses exact
Gaussian GELU as its mathematical target, but hardware evaluation
and rounding remain independent source receipts.

### Special zero-sign chart

In the original *non-raw* R4 route, if the concatenated
activation and expert history are identically zero,
the source's orientation score and first-nonzero fallback
give `sigma=0`, not ±1. Then `y=0` and updated h=0
even with FFN and transition biases. The ± two-chart formula
must not be applied at this unique fixed point. The original
`raw` route has a different >=0 tie rule and is not the
R4 geometry studied here.

## 4. Reuse F02a to close a REAL finite-vector F02b identity

For a historical state z and mirrored state Iz, write
`F_+=F(z)`, `F_-=F(Iz)`,
`O=(F_+-F_-)/2`, `E=(F_++F_-)/2`.
An odd-only student has outputs `S(z)` and `-S(z)`.
For a real Euclidean output vector,

    (||F_+-S||²+||F_-+S||²)/2
      = ||E||² + ||O-S||²
      >= ||E||².

This proves the **scalar/finite-dimensional real algebraic F02b
MSE floor** given Euclidean geometry and the involution.
The same source orientation chart has

    ||y_+-y_-||² = 4||E||².

Therefore the chart jump equals twice the square root of the
minimal odd-only pair MSE floor (when S=O on that pair).
A model needing an even channel to fit its targets can also
be intrinsically sensitive to a sign chart reversal unless it
retains that even residual. This is a mathematical capacity/
robustness trade-off, NOT a fitted Leech observation.

SymPy verifies the vector parallelogram identity in dimensions
1,2,3,4; general finite n follows by coordinate summation.
The old **Agda F02a remains the kernel owner** of the
qualitative no-go. No claim that its quantitative F02b
real theorem has been proved in the Agda kernel.

## 5. Sharp GELU FFN Lipschitz constant and even curvature

The source mathematical gate has

    g'(t)=Phi(t)+t phi(t),
    g''(t)=(2-t²)phi(t).

The extrema of g' occur at `t=±sqrt(2)`, and
the limits at ±infinity are 0 and 1.
The exact GLOBAL scalar Lipschitz constant is

    L_g = Phi(sqrt(2))+sqrt(2) phi(sqrt(2))
        = (1+erf(1))/2 + exp(-1)/sqrt(pi)
        ≈ 1.1289041451851547.

This replaces the older **loose** majorant
`1+1/sqrt(2*pi*e)≈1.2419707245` used
in the earlier R4 conditional recurrence.
The source FFN admitted Lipschitz factor is

    L_F = ||W2||_2 * L_g * ||W1||_2

when the true learned weights/spectral norms are supplied.

The even projection has scalar Lipschitz constant
`L_E=L_g-1/2≈0.6289041451851547`, and the second
derivative satisfies

    sup_t |g''(t)| = sqrt(2/pi).

With `u=W1 z`, the FULL biased FFN even component
has the global real upper bound

    ||E_F(z)||_2 <= ||F(0)||_2
      + ||W2||_2 * min(
          (L_g-1/2)*||u||_2,
          ||u||_2²/sqrt(2*pi)
        ).

The quadratic bound follows from the centred second-difference
formula and the global g'' bound, with
`||u ⊙ u||_2 <= ||u||_2²`. When b1=b2=0, the
chart-sensitive even component is O(||W1 z||²) near zero.
When biases are nonzero, do NOT infer that quadratic
term bounds the total even chart jump by itself.

SymPy checks the exact derivative/curvature identities, the
sharp extremum, even-channel derivative, a series leading
quadratic term (with a nonzero fourth-order correction),
and finite biased curvature/residual controls. This
is NOT a numerical GELU implementation tolerance.

## 6. Signed history transition: exact chart residual

The original `HistoryOrbitMoE.step` computes

    y_c=F_e(sigma z),
    h_c=T_h(sigma h)+T_x(sigma x)+T_y y_c+b_T,
    y_sigma=sigma y_c,
    h'_sigma=cap_history(sigma h_c).

For sigma=±1, before the history cap,

    H_sigma = T_h h + T_x x + T_y y_sigma + sigma b_T,

hence at the SAME x,h,

    H_+-H_- = 2 (T_y E_F(z)+b_T).

Under exact Euclidean radial cap with the same positive radius,
`||cap(H_+)-cap(H_-)||_2 <= ||H_+-H_-||_2`.
The actual source `cap_history` uses a float64 vector norm
and casts to the original dtype; that requires separate
numeric evaluation slack. The low-rank source transition
is still affine (composition of two linear layers); replace
T with its composite map and full final bias, not an
unjustified per-layer fixed matrix.

For DIFFERENT states z and z' and charts sigma,sigma'∈±1,

    ||y_sigma(z)-y_sigma'(z')||
      <= L_F ||z-z'|| +
         2 I[sigma≠sigma'] ||E_F(z')|| +
         eta_FFN.

The corresponding pre-cap history bound is

    Delta H <= ||T_h|| Delta h + ||T_x|| Delta x
       + ||T_y|| Delta y
       + 2 I[sigma≠sigma'] ||b_T||
       + eta_transition.

This is the correct **chart-relaxed** alternative to the
previous strict orientation-sign margin condition. It is only
an approximate numeric output/history consumer certificate;
if the receiver observes the `signs` metadata, exact sign
parity still requires strict margin or the exact tie/fallback
contract. Different TopK sets or mixed q-gate changes remain
separate discontinuities. The sigma=0 fixed point requires
its separate identity. Training `train_sign=True` has a
straight-through tanh surrogate gradient and is not covered
by this inference/forward certificate.

### F07 layer-error transport cross-pollination

For a source-admitted selected set, q gate, FFN matrices,
transition and precision budgets, the older
`LeechLayerErrorTransportExact.traceErrorBound` is the
right **compositional target**. Its `ErrorLayer.lipBound`
is UNIVERSAL on its chosen `State` carrier, however.
A locally bounded chart flip does NOT on its own satisfy
that premise. To reuse F07 soundly, either restrict
the state carrier to a proved chart/route-admissible
domain with a genuine Lipschitz witness, or introduce
a distinct guarded one-step error interface with
an explicit chart-jump residual `eta_chart`.
The latter can be summed as an additive per-step
majorant only after proving its replacement
one-step transport law; it cannot be silently
inserted as a global Lipschitz constant.

The approximate numeric output/history consumer may
tolerate chart changes even though the actual source
`signs` metadata differ. Per-step q/topk contracts,
full inactive histories and source FP receipts remain
independent.

## 7. Strong next Pareto/max-cut

1. Read the actual fitted R4 FFN `W1,b1,W2,b2`, orientation
   and transition blocks under the original checkpoint
   hash gate. Calculate `F_e(0)`, spectral norms
   `||W1||_2,||W2||_2,||T_y||_2`, and `b_T`.
   These are missing, not guessed.
2. For selected expert histories compute both an ordinary
   strict orientation margin and a **chart-even residual**
   bound. Choose the more useful consumer admission:
   exact sign metadata or approximate output/history.
3. Combine the chart residual with the existing
   correlated pairwise score errors, q-gate admission,
   softmax oscillation and inactive-history reopening.
4. Feed the resulting per-layer `lipBound` and
   source-only residual terms into the existing F07
   `teacherPathMajorant` formal receiver.
5. Preserve F02a/F02b parity non-fitting and independently
   typed grokking/Sophontic/trialectic face consumers.
   Do not reinterpret ± sign as moral opposition.
6. Do not claim an actual PyTorch parity, trained model
   improvement or hardware precision theorem without
   same-source checkpoint evidence.

**Attribution:** Leech-LILA by Anatolii Kornienko.
Original early GELU/parity formalisation is DASHI-owned;
the analytic normal-CDF formula traces to the GELU
literature. No ESD surfaces edited.


## 8. Adversarial source-chart fixture — margin failure need not mean output failure

The committed SymPy source now includes a constructive
orientation error condition that FAILS strict sign preservation
but passes a quantitative numerical consumer:

    same nonzero source z=1/100,
    original orientation coefficient +1/4096,
    perturbed coefficient -1/4096.

The original selected sign changes from + to -.
For a bias-free scalar source-shaped expert F(z)=GELU(z),
the exact output chart jump is

    |g(z)+g(-z)| = z erf(z/sqrt(2))
                 ≈ 0.0000797871262926,

and the **global quadratic** analytic upper bound is

    2 z²/sqrt(2 pi) ≈ 0.0000797884560803.

With an identity output-to-history transition path
and zero transition bias, the same residual controls the
source history jump before the cap. Thus the strict
orientation sign gate is necessary for exact `signs`
metadata and strict routing-chart equality, but can
be relaxed for a numeric output/history-error
consumer whose budget admits this parity residual.

The **negative control** sets the learned FFN output
bias to +1 with otherwise trivial FFN: a ± chart flip
then changes the output by exactly 2 even as
the preactivation approaches zero. Small source
state alone is not sufficient. The actual trained
FFN biases and norms remain missing.

The original expert's `sign=0` joint fixed point
still requires a separate source branch, and sign
flips in a quantized model require unchanged
expert IDs plus appropriate source q-gate bounds
before any single-expert residual is composable
with mixture/recurrence.


### F07 guarded recurrence: implemented as a distinct source contract

The SymPy script now symbolically checks, for every
finite horizon from 1 to 6, an explicit
guarded-error recurrence with chart-jump slack:

    D_(t+1) <= L_t D_t + eta_base,t + flip_t * J_chart,t,

where `flip_t` indicates the source's two nonzero
orientation charts disagree and `J_chart,t`
is admitted from the **actual** biased FFN
even component and transition residual.
For `D_0` and an arbitrary horizon N,
the exact upper-envelope expression is

    D_N <= D_0 * product_(k<N) L_k
         + sum_(j<N) (eta_base,j+flip_j J_chart,j)
                       * product_(j<k<N) L_k.

This is a source-compatible proof-development
RECURRENCE, not a new Agda F07 theorem:
the old F07 `lipBound` requires a genuine
global Lipschitz witness on its chosen carrier.
One cannot replace that premise with
pointwise chart-jump error without a new
guarded one-step law (or an explicitly
restricted carrier). The independently
checked finite algebra supplies the
right receiving formula but the fitted
source's layer-by-layer guard and
numerical Lipschitz/evaluation receipts
remain necessary.

The old even/odd F02a and F07 modules
remain the original Agda owners. The
finite-dimensional Euclidean F02b and
source-specific chart residual are new
SymPy exact-real bridges, not purported
Agda kernel promotions.


## 9. Source matrix lift — no diagonal/bias-free shortcut

The most recent SymPy source adds a finite arbitrary-symbolic
matrix check matching the original R4 selected expert's
layer structure rather than only its scalar GELU gate.
For `d=2`, hidden width 3, arbitrary learned
`W2:2x3`, full output bias `b2`, independent symbolic
`GELU(W1 z+b1)` and `GELU(-W1 z+b1)` hidden vectors,
the exact `y_σ=O_F+σE_F` identity and
`y_+-y_-=2E_F` hold coordinatewise.

For arbitrary affine transition matrices
`T_h,T_x,T_y` and transition bias `b_T`,
the source pre-cap history chart jump
`H_+-H_-=2(T_y E_F+b_T)` also holds
coordinatewise. The real Euclidean F02b
odd-only pair MSE floor survives arbitrary
learned `W2` mixing. These are matrix
algebra / finite Euclidean checks:
they do NOT identify actual fitted
weights or prove PyTorch float identity.
An independent local SymPy recreation
passed all five matrix/transition/MSE
checks. No Golden Agda/kernel receipt
is asserted.


## 17 November: corrected *early* GELU/kink prior-art attribution

The actual **facilitation-before-suppression** owner is
`DASHI/Cognition/ResponseKink.agda`, whose
`RecruitmentSuppressionProfile` and `profile-shape`
check a four-level rise–rise–overload-decline shape.
The pasted attribution to
`DASHI/Cognition/Utterance/AdmissibilityGate.agda`
is incorrect on the inspected default branch:
that module governs literal vs symbolic
utterance admission, not this profile.

The original cognitive computation owner
`DASHI/Cognition/AnesthesiaLanguagePhaseDynamics.agda`
has the distinct exact cubic margin
`10+4t-t³`, giving margins
`(+10,+13,+10,-5)` and hysteresis/stack
rebuilding. The separate HPA owner
`DASHI/Governance/SituatedHPARegimeFlexibilityExact.agda`
**reuses the canonical ResponseKink** as a
hypothetical ordinal stress-response
profile and explicitly prohibits inferring
an actual clinical condition or deterministic
high-load adrenal-exhaustion claim.

New source-written reuse bridge:
`DASHI/Cognition/PNF/X369R4EarlyKinkSourceWeldExact.agda`.
The bridge needs an explicit equality between
an actual original R4 observable and the
existing canonical profile's response,
before transporting the profile inequalities.
No verified R4 response/source record is
supplied, and no kernel run is asserted.

Exact SymPy candidate:
`scripts/check_x369_r4_early_kink_sympy.py`;
independent local execution: **14 grouped checks
passed**. A rational load-attenuated candidate
has profile values `(1,80/17,6,208/43)`;
a separate standard GELU-times-cubic-attenuation
example has values approximately
`(0,0.791853879,1.302999824,1.114772207)`.
Neither is claimed to be implemented or
fitted by the original R4. Unattenuated
positive-input GELU is an explicit negative
control: its increasing response cannot
establish the overload decline. A radial
history cap gives saturation, not necessarily
suppression of a selected expert's output.

The source-facing *conditional* evidence
checker `scripts/check_x369_r4_kink_source_receipt.py`
accepts only four source-provenance-bound
ordered loads and strict response intervals
for the SAME observable, checkpoint and
history revision. Companion
`scripts/check_x369_r4_kink_source_receipt_selftest.py`
adds 14 synthetic positive/negative fixtures.
Claims of source authentication or fitted
overload mechanism remain OPEN.

**Next actual maximum cut:** define and
measure an R4 original response observable
(e.g. selected contribution norm, fixed-expert
quality, router margin) as a function of
controlled increasing load with fixed
source checkpoint/history provenance.
Discharge the three original order
comparisons with response interval bounds,
then distinguish source mechanism by
independently tested attenuation,
topk competition, signed FFN dynamics,
history cap or hysteresis. Do not
derive shape from the earlier GELU
parity or correlated logit equivalence.

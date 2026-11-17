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
`LeechLayerErrorTransportExact.traceErrorBound` can use a
pointwise source discrepancy term that INCLUDES the
bounded chart-even jump. It need not reject every
orientation sign flip outright. However F07 is still a
generic conditional majorant; the actual PyTorch
network requires these per-layer numerical premises,
and the sign metadata is not automatically identical.

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

# Eighth maximum cut — nonlinear, mutually coupled, passive-memory **generator** with a finite-flight electrical port

**Date:** 15 November 2026. **Owner:** `chboishabba/dashi_agda`, continuation of open PR #1519. **Selected apparatus:** independently narrated @madscience369 V2 reel. **Status:** exact rational finite-model theorems and source-independent numerical controls; NOT an original V2 reconstruction, continuum spatial Maxwell theorem, globally certified hybrid-rotor orbit, or Agda-kernel proof.

## What changed, materially

The seventh-cut result (`v2_exact_multirate_periodic_port.py`) treated a **linear scalar flux/memory boundary** and a periodic, locally clocked reluctance. It proved a finite-packet line energy identity and rational period-map contraction. The sixth cut constructed a **nonlinear** multi-coil motor endpoint, but only checked numerical energy residuals; it did not prove uniqueness of the implicit nonlinear port solver or exact nonlinear periodic stability of the *combined* line/motor state.

This eighth cut builds a distinct **nonlinear, multiwinding, reciprocal-magnetic-coupling, first-order passive-memory** boundary and proves a conditional, locally attracting, explicitly manufactured nonzero *generator-polarity* cycle of the **entire coupled waveguide + machine system**. The waveguide remains a finite-speed queue; the rotor-parameter waveform is a prescribed four-step *clock*, not measured smooth rotation.

**Attribution:** Reluctance, Faraday/Maxwell, scattering passivity, discrete gradients and the Banach/implicit-function mathematics are established mathematical/physical methods; the synthetic model and receipts are our implementation. Donald Smith/Filsinger contributes a *separately sourced* retarded-control energy accounting analogy, not evidence that V2 has the same circuit. The 3–12 winding comparison is a mathematical control family, not an asserted Tesla 369 optimum.

## 1. Nonlinear magnetic energy and strict wellposedness

Let `m≥2` be windings; each has a positive-delay forward/backward waveguide, and each local winding has flux `λ_j` and relaxing memory coordinate `z_j`. Let `A_k` be a **symmetric inverse-inductance matrix**, held fixed over a clock interval, with diagonal dominance lower bound `ell`; let `b>0`, `h>0`, `μ>0`, coupling `g`, and assume `ell > g²/h`. Define

\[
U_{A_k}(\lambda,z)=\tfrac12\lambda^TA_k\lambda
 +\tfrac b4\sum_j\lambda_j^4-g\lambda^Tz+\tfrac h2z^Tz.
\]

The terminal current and passive memory force are its gradients

\[
i=\partial_\lambda U=A_k\lambda+b\lambda^{\circ3}-gz,
\qquad q=\partial_z U=hz-g\lambda.
\]

Its Hessian `[[A_k+3b diag(λ²), −gI], [−gI, hI]]` is uniformly SPD under `ell > g²/h`. In this flux-coordinate form increasing current costs increasingly steep energy; the differential inductance is positive but can decline with flux. This is an *illustrative reversible saturation law* and a dissipative single-rate memory. It does not model arbitrary Preisach hysteresis or identify an actual material B–H curve.

For each interval, define the **average-vector-field discrete gradient**, exactly

\[
\bar i=\tfrac12 A_k(\lambda+\lambda')+
\tfrac b4(\lambda^{\circ3}+\lambda^{\circ2}\!\circ\lambda'+
\lambda\circ\lambda'^{\circ2}+\lambda'^{\circ3})-\tfrac g2(z+z'),
\]
\[
\bar q=\tfrac h2(z+z')-\tfrac g2(\lambda+\lambda').
\]

These polynomials obey the exact identity, for **every** pair of states (not only simulated trajectories):

\[
U(\lambda',z')-U(\lambda,z)=
\bar i\cdot(\lambda'-\lambda)+\bar q\cdot(z'-z).
\]

The dynamically coupled implicit step is

\[
\lambda'-\lambda=\Delta t[2a-(Z+R)\bar i],\qquad
z'-z=-\Delta t\mu\bar q.
\]

Here `a` is the *actually arrived* wave, not an instantaneous remote controller read. Under the SPD hypothesis and `Z+R>0, μ>0`, the implicit-step operator `y' + Δt D \int_0^1 \nabla U(y+t(y'−y))dt` with `D=diag((Z+R)I, μ I)` is strictly monotone and coercive in the `D^{-1}` inner product. Indeed its Jacobian is `I+Δt D∫_0^1 t Hess(U)(...)dt`; pairing with `D^{-1}` makes its symmetric quadratic form strictly positive. Consequently **every fixed initial state and arrived wave admits exactly one nonlinear implicit endpoint**. Numeric root convergence is a separate implementation check, not the proof of existence.

This is the new `v2NonlinearMutualMemoryAVFImplicitExistenceUnique` subgate.

## 2. Exact signed energy of the actual coupled causal boundary

Every winding has `n≥1` flight cells, per-cell attenuation `0<s≤1`, characteristic impedance `Z>0`, front speed `0<v≤c`, launch wave `u`, incident `a=s f_last`, returned source wave `s b_first`, and reflection `r=a−Z i_bar`. Every cell has positive flight duration `Δt`, and distance `vΔt`; a physical remote response cannot arrive before `n` positive flight ticks or return before `2n`.

Define the finite line inventory

\[
E_{line}=\frac{\Delta t}{Z}\sum_j\sum_{r=0}^{n-1}
(f_{jr}^2+b_{jr}^2).
\]

At every solved nonlinear electrical step, the exact wave scattering identity is

\[
\frac{\Delta t}{Z}(a^2-r^2)
=\Delta t(a+r)\bar i=\Delta t\,v_{terminal}\bar i.
\]

The AVF identity, memory dissipation and wave packets then establish, **for every admissible state**,

\[
\boxed{\Delta(E_{line}+U_{A_k})
=W_{source}-D_{line}-D_{Cu}-D_{memory}.}
\]

All dissipation terms are explicitly nonnegative. The source and motor-terminal terms are **signed**: negative source work means energy exported back through that port. An *independently driven* clock change `A_k→A_{k+1}` at fixed `(λ,z)` adds

\[
W_{rotor/actuator}=U_{A_{k+1}}(\lambda,z)-U_{A_k}(\lambda,z)
=\tfrac12\lambda^T(A_{k+1}-A_k)\lambda.
\]

It is not unmetered gain. These identities pass exact Fraction arithmetic and a symbolic polynomial test using an arbitrary reciprocal multiwinding matrix.

## 3. Nonzero generator-polarity periodic orbit and certified **local** attraction

For an explicit four-clock sequence, prescribe **nonzero rational flux states** `λ_k` and derive a unique periodic passive memory `z_k` by the linear memory recurrence. Invert the exact implicit flux law to calculate the *arrived* waves needed for that orbit. The periodic source launch schedule is then selected **ahead of time** with `n` flight ticks of causal lead. Backward reflected waves are computed from the same signed port. Thus the sequence solves the **actual nonlinear coupled line/motor recurrence**, not a merely desired current waveform, and both packet and magnetic states close exactly after four clock events.

For each clock step, differentiate the **implicit nonlinear recurrence** exactly using rational arithmetic. The product is the full period Jacobian `DP(x*)`, incorporating both directions of line transport, cross-winding mutual coupling, memory, nonlinear quartic terms and the source being held fixed during perturbations. For the selected three-winding example,

\[
\boxed{\|DP(x_*)\|_\infty=0.9572862540872351\ldots<1.}
\]

Because the actual nonlinear period map is `C¹` locally (by the implicit-function theorem) and this norm bound is **an exact rational inequality**, it is a contraction on a sufficiently small neighbourhood of the fixed point. This establishes a *locally unique, locally exponentially attracting periodic orbit*. It does **not** establish a uniform global attractor for arbitrarily large perturbations or arbitrary hybrid switching.

Exact rational local contractions also pass for the constructed 2-, 4-, 6-, 9- and 12-winding examples; the tests cover 3–12 winding periodic energy accounts with 1–3 flight cells. No optimum 369 count is inferred, and these designs do not hold manufacturing mass and magnetic geometry fixed.

The three-winding **generator-polarity** witness has `s=999/1000`, `Z=1/2`, `R=1/100`, `b=1/16`, `g=1/4`, `h=1`, `μ=1`, and a selected clock sequence. All values except the speed-of-light constant are hypothetical:

| Signed one-cycle energy | Model units (J if the abstract parameters are interpreted as SI) |
|---|---:|
| Rotor/parameter work **into** field | +0.027500000000 |
| Source work **into** system | −0.002756208295 (net electrical export) |
| Loss in propagation line | 0.006780434870 |
| Copper heat | 0.017155664527 |
| Passive magnetic-memory heat | 0.000807692308 |
| Whole-cycle stored-energy change | **0 exactly** |

Thus *electrical export + all losses equals the separately supplied rotor/actuator work exactly*. The source terminal power is not counted twice as independent mechanical energy. This is evidence of a physically coherent *possibility within the constructed mathematical model*, not of any original hardware measurement.

## 4. Retardation, smooth rotor and physical time-scale limitations

The mathematical witness uses `Δt=1/4 s` and `v=2c/3`, so a **one-cell cable would be about 49,965,410 metres long**. This is intentionally an abstract exactly solvable network, not a claim about the V2's cable! For a hypothetical 0.5 m line at 0.7c, one-way delay is roughly 2.38 ns. A physical 2354 RPM revolution spans ~10.7 million such intervals.

The prior exact affine multirate reduction accelerates *linear held-parameter* intervals by logarithmic composition; it does **not** apply unchanged to the nonlinear boundary here. An arbitrary instantaneous real switching edge is not Lipschitz, and no remote observation can be forecast before its causal arrival. It would be false to describe this exact orbit as a subnanosecond, smooth-rotor real-device solver.

One new **conditional** error control, `v2SmoothClockedRotorParameterWorkErrorBound`, addresses the parameter-work part of this gap. Suppose `A(t)` is absolutely continuous, `||λ(t)||≤B`, `||dλ/dt||≤D`, each clock partition width is `h`, and `TV(A)=∫||dA/dt||dt` (matrix operator norm). The difference between the true continuous parameter work `1/2∫ λᵀ A_dot λ dt` and the *right-endpoint* clocked-jump surrogate is bounded by

\[
\boxed{|W_{smooth}-W_{clock}|\le BDh\,TV(A).}
\]

The proof is `|(λᵀ A_dot λ)-(λ_kᵀ A_dot λ_k)| ≤ 2BDh ||A_dot||` (under `||λ||≤B` at both points), integrated with the `1/2` coefficient. The tests check this bound with independent smooth two-winding waveforms. The required `B,D,TV(A)` are external assumptions; **this is not a validated nonlinear flow bound** and does not apply across unbounded edges.

## 5. Exact P0–P4 ledger integration

New closed **restricted subgates**:

- `v2NonlinearMutualMemoryAVFAllStateSignedEnergyExact` — exact polynomial AVF plus packet boundary work for arbitrary admissible states, with independent signed source, copper, memory and line terms.
- `v2NonlinearMutualMemoryAVFImplicitExistenceUnique` — analytic strong-monotonicity / coercivity proof under the SPD material domain.
- `v2NonlinearCausalMultiwindingManufacturedGeneratorCycle` — explicit rational nonzero periodic state, all packet and magnetic endpoints matched, generated-source polarity with mechanical work and all losses paid.
- `v2NonlinearCoupledMotorLinePeriodicLocalAttractor` — exact rational period Jacobian and strict one-period infinity-norm bound; **local** and restricted to clocked parameters.
- `v2SmoothClockedRotorParameterWorkErrorBound` — conditional smooth-parameter work approximation bound.

Strict gate status remains **unchanged**:

- **P0:** `v2PulsedNonlinearCoenergyIdentity`, `v2PulseWindowClosedFormAndHighCurrentCounterexample`, `v2ReversibleClampRecoveryImprovesUsefulWorkConditional`, `reluctancePermeancePulseAgda29KernelAcceptance`: full kernel/real analysis still OPEN.
- **P1:** `v2PulseControllerFiniteSlewAndBusVoltageEnvelope`, `v2NonlinearMutualSaturationHysteresisAndCoenergyWeld`, `v2JointPhaseCountPulseConverterParetoCertified`, `originalV2ContinuousVoltageCurrentThermalBound`: source-specific transistor, rate-independent material and validated hybrid envelopes still OPEN.
- **P2:** `generalPolyphaseConstrainedGlobalOptimality`: full physically constrained global optimisation OPEN. The exact local periodic generator is **not** its general global optimum theorem.
- **P3/P4:** source V2 topology, material maps, actual shaft torque, scope channels, complete signed metrology and cyclic storage closure, original load interventions: all PHYSICAL OPEN. The reel cannot close them.
- **Causal stronger gates:** `v2DistributedLineMaxwellPassivityAndWavefrontBound`, `v2LumpedQuasistaticErrorAndControllerLatencyBound`, `v2SubNanosecondCableMultiRatePassiveCouplingCertificate`, `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` (global arbitrary nonlinear rotating hybrid scope) remain OPEN.

**Acceptance:** `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 python -m pytest -q tests/test_v2_nonlinear_exact_causal_boundary.py tests/test_v2_exact_multirate_periodic_port.py tests/test_v2_waveguide_motor_port_maxcut.py`. The exact rational/SymPy/source-independent tests are stronger than a sampled numerically balanced trajectory, but do not constitute Agda kernel acceptance. Original hardware evidence remains unavailable.

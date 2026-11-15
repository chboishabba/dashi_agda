# Seventh maximum cut — exact finite-flight multirate waveguide ↔ lag-memory reluctance boundary

**2026-11-15 · owner `dashi_agda` PR #1516.** The original V2 reel by @madscience369 and the separately attributed Donald Smith/Filsinger work are not a source for any winding/cable parameters in this construction. This is a *strictly delimited finite-dimensional mathematical theorem* and its reproducible tests. It does **not** prove original-machine anomalous power, a smooth Maxwell PDE, semiconductor PWM, real nonlinear saturation, arbitrary rate-independent hysteresis, or Agda kernel admission.

## Why this cut was necessary

The earlier producer `v2_waveguide_motor_port_maxcut.py` dynamically couples the actual signed incident/reflected wave port to a nonlinear mutual-flux/magnetic-memory step, with an exact-to-roundoff energy ledger. But one propagation cell is one motor solver timestep, implying kilometer-scale or larger illustrative lines if the timestep is slow; the physical 0.5 m at 0.7c crosses in only 2.38260068 ns. Brute stepping ~10.7 million ticks for one 2354 RPM revolution obscures the multirate structure. Prior analytic periodic-state proofs concerned the winding subsystem, not the complete waveguide + motor + memory state.

## Exact *rational* model and proof

For a finite passive transmission line with `n ≥ 1` forward and backward packet cells, `dt>0`, `Z>0`, `0 ≤ s ≤ 1`, front speed `0 < v ≤ c`, source launch `u_k`, and incoming `a_k=s f_{n-1,k}`:

\[
 f'=(u_k,s f_0,\dots,s f_{n-2}),\qquad
 b'=(s b_1,\dots,s b_{n-1},r_k),
 \quad r_k=a_k-Z\bar i_k.
\]

The terminal voltage is `v_k=a_k+r_k`, the terminal work `dt v_k ī_k`, and the signed source work is `dt (u_k² - (s b_{0,k})²)/Z`. The packet stored energy is `dt/Z Σ(f_j²+b_j²)`, with nonnegative attenuation loss `dt (1−s²)/Z Σ(f_j²+b_j²)`. No source response can reach the motor before `n` flight ticks or return before `2n`.

The *restricted linear magnetic-memory* coenergy and Legendre energy, at locally prescribed positive inductance `L`, are

\[
 W'(i,z;L)=\tfrac12Li^2+giz-\tfrac12hz^2,\quad
 \lambda=Li+gz,\quad
 U_L(\lambda,z)=\tfrac{(\lambda-gz)^2}{2L}+\tfrac h2z^2.
\]

A midpoint/discrete-gradient step satisfies

\[
 \frac{\lambda'-\lambda}{dt}=2a-(Z+R)\bar i,\qquad
 \frac{z'-z}{dt}=\mu(g\bar i-h\bar z),\qquad
 \bar i=\frac{\bar\lambda-g\bar z}{L}.
\]

For `R>0, μ≥0, h>0`, copper work `dt R ī²` and magnetic-memory dissipation `dt μ(g ī−h z̄)²` are nonnegative. By exact midpoint quadratic identity, for every initial packet/magnetic state and signed source input,

\[
 \boxed{E'_{line}+U'_L-E_{line}-U_L
 =W_{source}-D_{line}-D_{Cu}-D_{memory}.}
\]

The implementation proves this not merely on selected traces: it constructs the rational quadratic forms `H,Q_source,Q_line,Q_copper,Q_memory` and checks **coefficient by coefficient**

\[
 M^T H M-H=Q_{source}-Q_{line}-Q_{copper}-Q_{memory}
\]

for the entire one-step affine map `y' = M y` on augmented `(packet state, λ,z,source launch)`. It also checks the signed motor terminal power identity. `Fraction` computations are exact, not floating point approximations.

## Lossless exact supersteps and all-work receipts

For constant local `L` and held source launch during a block of length `K`, define affine transition `M_K` and five quadratic integrated-work matrices `Q^q_K` for `q∈{source, motor_port, line_loss, copper, memory}`. For consecutive blocks `A` then `B`:

\[
 M_{AB}=M_BM_A,\quad Q^q_{AB}=Q^q_A+M_A^TQ^q_BM_A.
\]

This is an exact algebraic semigroup. Binary composition computes states **and separately signed energy flows** for `K` microscopic ticks in `O(log K)` small-matrix products without time-stepping each fine flight tick. Tests compare exact rational supersteps against independent per-tick application at many lengths and source signs. Critical restriction: blocks may not silently cross a rotor-parameter change, switch-event or source-waveform change; each event must split the block. This is not yet an error-controlled approximation to a smooth time-varying rotor.

The floating-point version applies the *same* block formulas after converting the exact one-step coefficients. It separately checks the post-run balance, but numerical rounding is **not** interval-certified. With an illustrative 0.5 m / 0.7c one-cell cable, positive attenuation, and constant local inductance and source launch, ~10.7 million microscopic ticks are grouped logarithmically. The final cumulative signed-work residual is recorded; **this is a held-parameter interval**, not one resolved mechanical revolution.

## Actual coupled-system periodic-orbit and mechanical-energy theorem — restricted scope

Choose an *explicitly periodic sequence* of locally held inductances `L_j>0` and source waves `u_j`; each phase holds both fixed for `K` positive-flight ticks. A local change `L_j→L_{j+1}` keeps `(λ,z)` continuous and contributes signed external parameter/rotor work

\[
 W_{mech,j}=U_{L_{j+1}}(\lambda_{end},z_{end})-U_{L_j}(\lambda_{end},z_{end}).
\]

This term must **not** be smuggled in as free magnetic energy. The computed affine period map is `x↦P x+b`. For the exact illustrative rational values `(n=2,dt=1/4,Z=2,s=1/2,R=1,g=1/4,h=1,μ=1)`, four clocked blocks with `L=(1,5/4,1,3/4)`, `u=(1,0,−1,0)`, `K=2` are used **only as a mathematical witness**. These abstract times would correspond to an implausibly long physical cable at `2c/3`; they are not V2 geometry.

The *rational* matrix calculation establishes `||P^16||_∞<1`, which proves the 16th period iterate is a contraction on all state space. By Banach's fixed-point theorem, `P` itself has one unique attracting fixed point (it commutes with its iterate); the solution `(I−P)x*=b` is solved exactly with rational Gaussian elimination. The source, line and memory states return exactly after the period; there is no depletion-based efficiency illusion. A full-cycle telescoping proof then gives

\[
 \boxed{W_{source}+W_{mech}=D_{line}+D_{Cu}+D_{memory},\quad\Delta E_{total}=0}
\]

in exact fractions. Depending on the chosen pulse and phase, the signed local parameter work can be positive or negative; it is never omitted. A sample nonzero positive-work instance is recorded in the receipt.

This discharges the **restricted discrete waveguide ↔ linear-memory clocked-reluctance periodic-state subgate**. It does **not** imply a periodic orbit for the previous nonlinear saturation/mutual-coupling model, for a continuous rotor with hybrid semiconductor switch edges, or for a spatial Maxwell PDE.

## Original 16 strict P0–P4 gates and exact follow-on leaves

No original strict gate is fully closed by this round; the completed *model-level* leaves are:

- `v2FinitePacketMotorMemoryQuadraticEnergyAllStates`: exact rational coefficient identity for all finite states and signed inputs.
- `v2CausalBlockSemigroupAllSignedWorkExact`: exact block-power and five-Gramian work composition, no acausal delay reduction when the input is held.
- `v2ClockedReluctanceCoupledLineMemoryPeriodicBanach`: exact finite-dimensional period map with strict rational contraction and matched state/energy endpoints.
- `v2LocalRotorParameterWorkNoFreeGain`: rotor/actuator parameter work kept as a signed port in the full cycle.
- `v2ShortCableHeldParameterTenMillionTickReduction`: floating accelerated illustration with a measured numerical residual, **not** a rounding-verified certificate for a smooth machine.

Still required for strict closure:

1. `v2SubNanosecondCableMultiRatePassiveCouplingCertificate` — validate accelerated **nonlinear and hybrid** multirate coupling across events with interval flow enclosures and source-specific geometry; the current fast proof is only linear, event-delimited.
2. `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` — nonlinear saturating, mutually coupled, memory-bearing **rotating** motor, causal line and actual hybrid controller together; current theorem only linear scalar magnetic memory and clocked L.
3. `v2DistributedLineMaxwellPassivityAndWavefrontBound` and `v2LumpedQuasistaticErrorAndControllerLatencyBound` — spatial, dispersive PDE field-to-motor result and controlled lumped-model error, not a finite packet assertion.
4. `reluctancePermeancePulseAgda29KernelAcceptance` plus the P0 calculus/real trigonometry proof suite — pinned local kernel acceptance still unavailable, despite exact Python Fraction proofs.
5. Full original V2 P3/P4: selected schematic, cable/probe timing, measured nonlinear flux/torque, all signed power ports, storage endpoint closure and randomised load tests; none is available from the reel.

**Acceptance command:** `OPENBLAS_NUM_THREADS=1 python -m pytest -q tests/test_v2_exact_multirate_periodic_port.py` in this package. The exact model and tests are independent of the old SLSQP/PWM aggregate runner. All proof assumptions are recorded; no claim of physical anomalous energy is made.
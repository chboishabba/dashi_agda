# Fifth maximum cut — dissipative magnetic memory, retarded control, periodic-state closure

**Date:** 15 November 2026. **Owner:** existing \`chboishabba/dashi_agda\` PR #1516, continuing merged #1511. **Provenance:** original @madscience369 V2 reel remains a *distinct* uncharacterised physical device. Donald Smith/Filsinger source-qualified finite-flight and modulated-Hamiltonian mathematics is a donor; no claim of identical apparatus or natural energy source. Reluctance/coenergy, Faraday and Maxwell theory retain original scientific provenance.

## Result and exact scope

This round closes a previously open **restricted mathematical subgate**: a nonlinear **reversible saturating, mutually coupled** reluctance model with a **dissipative internal magnetic-memory state** admits an explicitly manufactured bounded-voltage periodic trajectory and an exponential **retarded-feedback history-contraction certificate** under a quantitative small-gain condition. The internal state is first-order *relaxation* (\`z' = μ(gi-hz)\`), which can display rate-dependent hysteresis-like lag. This is **not** a constitutive theorem for arbitrary rate-independent ferromagnetic hysteresis/Preisach operators, not a solved Maxwell field/motor boundary, not a transistor-level switching/diode guarantee, and not a measurement of the original V2.

The source \`scripts/v2_retarded_memory_periodic_maxcut.py\` produces a 3–12 phase test family, an exact two-winding SymPy constitutive identity, continuous analytic voltage envelope, positive dissipative terms, a constructed periodic memory waveform, two causal method-of-steps controls, and an exact symbolic/rational signed-port composition. The regression owner is \`tests/test_v2_retarded_memory_periodic_maxcut.py\`. Machine receipt: \`Artifacts/v2_retarded_memory_periodic_maxcut_20261115.json\`.

## 1. Constitutive contract and energetic sign convention

For winding currents \`i in R^m\`, rotor angle \`θ=ωt\`, and magnetic-memory state \`z in R^m\` define

\[
W'(i,\theta,z)=\tfrac12 i^T L(\theta)i+b I_s^2\sum_j\log\cosh(i_j/I_s)
       +g\,i^Tz-\tfrac12h\,z^Tz,
\]
\[
\lambda=\nabla_iW'=L(\theta)i+b I_s\tanh(i/I_s)+gz,
\quad f_z=\nabla_zW'=gi-hz, \quad \tau_e=\partial_\theta W'.
\]

\`L(θ)\` is a symmetric phase-shifted reluctance/mutual matrix, with eigenvalues bounded so that the smooth monotone map \`Fθ(i)=λ−gz\` has \`ell I <= ∂Fθ/∂i <= Lambda I\` uniformly. Parameters \`b>=0, Is>0, R>0, μ>0, h>g²/ell\`, and \`g>=0\` are **assumptions**, not source-calibrated material constants.

The passive memory and actual lumped winding equations are

\[
\dot z=\mu f_z,\quad
\dot\lambda=v_{\rm base}(t)+K i(t-\tau)-R i(t),\quad
\tau=d/v_{\rm front}+\tau_{\rm controller},\quad 0<v_{\rm front}\le c.
\]

The active delayed controller \`K i(t−τ)\` is a **separately metered electrical port**. The magnetic energy is the Legendre expression

\[U=i\cdot\lambda-W'=\tfrac12i^TLi
 +b I_s\sum_j i_j\tanh(i_j/I_s)-b I_s^2\sum_j\log\cosh(i_j/I_s)+\tfrac12h\|z\|^2.\]

Exact differentiation yields

\[
\boxed{i\cdot v=R\|i\|^2+\dot U+\tau_e\omega+\mu\|g i-hz\|^2.}
\]

Thus \`P_shaft,extraction=-τω\`, and over a matched complete cycle \`P_export=P_shaft,extraction−P_Cu−P_memory\` in the ideal terminal-port convention. No separate pump, delayed controller or internal reactive circulation is an unmetered energy source. The symbolic 2-winding identity simplifies to zero exactly (SymPy) and has pointwise numerical residual below \`6e-15 W\` in the selected examples.

## 2. Delayed flux + memory proof

Consider any two histories under the **same** periodic \`vbase(t)\` and rotor motion. Let \`x=||Δλ||\`, \`y=||Δz||\`. Strong monotonicity and upper Hessian bounds of \`Fθ\` give

\[
D^+x\le-\frac R\Lambda x+\frac{Rg}{\ell}y+\frac{|K|}{\ell}(x(t-\tau)+g y(t-\tau)),
\]
\[
D^+y\le\frac{\mu g}{\ell}x-\mu\left(h-\frac{g^2}{\ell}\right)y.
\]

For any \`ρ>0\` choose \`M(t)=max(x(t),ρ y(t))\`, and define

\[
a=\min\left\{\frac R\Lambda-\frac{Rg}{\ell\rho},\quad
              \mu\left(h-\frac{g^2}{\ell}\right)-\frac{\rho\mu g}{\ell}\right\},\qquad
b_d=\frac{|K|}{\ell}\left(1+\frac g\rho\right).
\]

If **\`a>b_d>=0\`**, the comparison inequality \`D+M(t)<=−a M(t)+b_d sup_[t−τ,t] M\` holds at every upper-Dini differentiability point (including ties). Halanay's comparison gives

\[\boxed{M(t)\le M_{[-\tau,0]}e^{-\eta t},\qquad
  \eta+b_d e^{\eta\tau}=a,\quad \eta>0.}\]

The positive \`ρ\` used in the source solves \`ρ² c+(a0−d0)ρ−b0=0\` to balance both instantaneous margins, with \`a0=R/Λ, b0=Rg/ell, c=μg/ell, d0=μ(h−g²/ell)\`. A failed inequality is **uncertified** rather than proved unstable. For any specified bounded periodic base waveform the forward dynamics are well-defined in this model. We construct a periodic orbit explicitly below; contraction proves that it is **unique and attracting**, including for different valid history segments. For a genuine history Poincaré contraction, choose enough periods so their total exceeds the finite delay \`τ\`.

For the illustrative params, \`ell=0.0256 H, Lambda=0.0584 H, R=1 Ω, g=h=0.003\`, \`μ=12000\`, gain \`K=0.04 Ω\`, \`ρ≈0.0157234\`, \`a≈9.6702 s^-1\`, \`b_d≈1.8606 s^-1\`, \`τ≈100.002383 μs\`, and the certified history-decay exponent \`η≈7.8081 s^-1\`. These numbers are invented source-independent physical parameters, not inferred V2 material values.

## 3. Explicit periodic state and continuous drive voltage

At phases \`ϕ_j=hθ−2πj/m\`, choose positive periodic currents

\[i_j^*(t)=(I_0+I_1\sin\phi_j)/\sqrt m,\quad I_0\ge|I_1|>0.\]

Set \`Ω=hω\`, \`γ=μh\`, \`δ=atan2(Ω,γ)\`, and

\[
z_j^*(t)=\frac{g I_0}{h\sqrt m}
  +\frac{\mu g I_1}{\sqrt m\sqrt{\gamma^2+\Omega^2}}\sin(\phi_j-\delta).
\]

This **exactly solves** \`z'=μ(gi−hz)\` and returns to the same z state each rotor period. Differentiate the constituted flux to obtain \`vterminal*(t)=R i*(t)+dλ*(t)/dt\`. Set \`vbase*(t)=vterminal*(t)−K i*(t−τ)\`. The prescribed *known-periodic* base waveform and purely delayed feedback then realize the exact periodic solution; the base waveform is not a clairvoyant remote observation. All current/voltage signals are smooth *averaged* controller targets, not instantaneous current steps or verified semiconductor PWM.

An all-time conservative voltage envelope is

\[
|v_{terminal,j}|\le R i_{max}+\Lambda \dot i_{max}+|A|\Omega i_{max}
  +2\mu g^2 i_{max},\quad
|v_{base,j}|\le|v_{terminal,j}|+|K|i_{max},
\]
where \`i_max=(I0+|I1|)/sqrt(m)\` and \`di_max=|I1|Ω/sqrt(m)\`. In the illustrative 3–12 phase construction this envelope is below a **hypothetical** 320 V bus (e.g. 32.00 V at 3 phases), while the exact periodic cycle has mean shaft extraction ≈3.54975 W, copper loss 1.180 W, magnetic-memory dissipation ≈0.01941 W, and ideal terminal export ≈2.35033 W. **These are not V2 output measurements.** Internal storage endpoints coincide *by construction*; numerical quadrature checks the exact algebra rather than defining the result.

## 4. Independent retarded numerical controls and lightfront honesty

A method-of-steps RK4 diagnostic integrates the independent \`(λ,z)\` state and reconstructs current by a positive-definite constitutive inverse. Every feedback sample is read from time \`t−τ\` or from the fixed initial history, never from an unavailable future sample. The integration step is shorter than the total feedback delay. Two-cycle examples for 3 and 6 phases satisfy the analytic weighted-envelope bound. This is a numerical control; RK4 and interpolated history are NOT a validated interval enclosure or proof of the theorem.

The 0.5 m / 0.7c cable flight contributes ≈2.3826 ns; the constructed controller adds 100 μs latency. These are separate causal contributions and cannot be replaced by the older 142 μs motor solver step. No influence crosses the cable earlier than its lightfront. The sinusoidal feedforward waveform may be scheduled ahead because its future profile is known; unexpected sensing or switching edges cannot be pre-observed.

## 5. New *conditional* 1D telegrapher ↔ motor port composition

Take the established passive telegrapher line equation at each spatial point, integrate over the finite cable, and orient line current towards the motor. It has

\[\dot E_{line}=P_{source}-P_{terminal}-D_{line}.\]

The nonlinear motor/lag equation has

\[\dot U_{motor}=P_{terminal}+P_{shaft,extraction}-P_{Cu}-P_{memory}.\]

**Only if** the physical line endpoint and motor winding terminals are the same signed electrical port can their inner \`Pterminal\` cancel, yielding

\[\boxed{\frac d{dt}(E_{line}+U_{motor})
  =P_{source}+P_{shaft,extraction}-D_{line}-P_{Cu}-P_{memory}.}\]

This composition is proven algebraically, including exact Fraction arithmetic for a negative *signed* motor-port example. The prior finite packet simulation with a passive resistor load does **not** implement a generating motor boundary, and this algebraic composition is **not** a theorem of existence or uniqueness for the jointly coupled 1D wave/motor evolution. That is a separate strict Maxwell-to-machine boundary/retarded wellposedness gate. It would be wrong to equate passive load absorption with negative signed generator-port energy without constructing the active bidirectional boundary conditions.

## 6. Acceptance, status and next maximum cut

New model-level exact declaration names for the canonical ledger:

- \`v2RetardedSaturatingMemoryHalanayPeriodicContraction\` — conditional analytic proof CLOSED for specified smooth positive-incremental-inductance + passive single-rate z and small delay gain; Agda real-analysis theorem OPEN.
- \`v2RetardedMemoryManufacturedPeriodicStateAndVoltageBound\` — explicit periodic current/z with continuous conservative voltage bound CLOSED in constructed averaged-control class; actual V2 and real switching OPEN.
- \`v2RetardedMemoryCoenergySignedWorkIdentity\` — exact 2-winding SymPy symbolic identity and numerical 3–12-phase pointwise energy checks CLOSED in mathematical model; Agda calculus and actual power boundary OPEN.
- \`v2DistributedLineToMemoryMotorSameSignedPortConservation\` — conditional symbolic/Fraction algebraic composition CLOSED; dynamically coupled boundary PDE and apparatus port matching OPEN.
- \`v2RetardedMemoryHistoryIntegrationAndHighGainNegativeControl\` — causal RK4 and failed high-gain proof checks CLOSED at regression level, NOT a validated interval flow.

Existing original **16 distinct strict P0–P4 gates remain OPEN**, and there is no original V2 hardware evidence this round. Especially: Maxwell-to-nonlinear magnetic material field solution, arbitrary rate-independent hysteresis, transistor-level gate/recovery loss, globally calibrated phase-optimum, pinned Agda kernel and complete source-selected original device port receipt are OPEN. Do not infer physical efficiency or natural energy from the independent Smith/Filsinger donors.

Reproduction after integration:

\`\`\`bash
bash scripts/check_madscience369_reluctance_maxcut.sh
python scripts/v2_retarded_memory_periodic_maxcut.py > Artifacts/v2_retarded_memory_periodic_maxcut_20261115.json
RUN_AGDA=1 bash scripts/check_madscience369_reluctance_maxcut.sh  # only with pinned compiler
\`\`\`

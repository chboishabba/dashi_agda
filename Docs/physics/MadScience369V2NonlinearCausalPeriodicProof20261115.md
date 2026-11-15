# Nonlinear periodic reluctance and retarded controller: fourth maximum cut

**Status 2026-11-15:** source-independent conditional mathematical theorem for a smooth quasistatic *reversible* saturating multi-coil machine. NOT original @madscience369 V2 hardware, 3D Maxwell, measured efficiency, transistor PWM, hysteresis, or kernel-checked Agda. Original Don Smith/Filsinger retarded-flight models are donors only.

## Reversible nonlinear coupled periodic theorem

For m>=3 equal shifted phases, symmetric cyclic mutual L(theta), diagonal L0+A cos(h theta−2 pi j/m), neighbor M, and L0>|A|+2|M|, define coenergy

    W'(i,theta) = i^T L(theta) i / 2 + b Is² sum_j log cosh(i_j/Is)
    psi = grad_i W' = L i + b Is tanh(i/Is).

Assume b,Is,R>0. Uniform incremental Hessian bounds follow by diagonal dominance:

    ell I <= dpsi/di <= Lambda I
    ell = L0−|A|−2|M| > 0
    Lambda = L0+|A|+2|M|+b.

Consider flux-state dynamics psi_dot = v(t)−R i(psi,theta(t)).
For two solutions under the same drive/rotor, the mean Hessian along their current segment has spectrum in [ell,Lambda]. Hence delta_i · delta_psi >= ||delta_psi||²/Lambda and

    ||delta_psi(t)|| <= exp(−Rt/Lambda) ||delta_psi(0)||.

Periodic rotor geometry and voltage give a strict one-cycle Poincare contraction, therefore a **unique globally attracting periodic flux/current state**, by Banach fixed-point theorem. This closes v2CoupledSaturatingFluxPeriodicPoincareContraction *in this precise reversible model only*.

An explicit cycle-periodic nonnegative target current is i_j*=(I0+I1 sin(h omega t−2pi j/m))/sqrt(m), I0>=I1>0. It solves the actual winding equation if the smooth averaged voltage is

    v* = R i* + H(i*,theta) i*_dot + omega L_theta(theta)i*.

The **all-time** voltage bound is R imax + Lambda dmax + |A| h omega imax, where imax=(I0+I1)/sqrt(m) and dmax=h omega I1/sqrt(m). All magnetic state/storage endpoints close exactly. Instantaneous power is v·i=R||i||² + d/dt(i·psi−W') + omega partial_theta W'. In this constructed motor, mean shaft extraction A h omega I0 I1/2 and copper R(I0²+I1²/2) do not depend on phase count at fixed aggregate current normalisation. This closes v2CoupledSaturatingFluxPeriodVoltageEnvelopeAndEnergyClosure only for the smooth constructed class; real PWM/thermal/Maxwell remain open.

## Strict causal delay and nonlinear response

For prescribed smooth v(t), a matched pure delay tau with vector command Lipschitz Mv produces

    ||delta_psi(t)|| <= (Mv*tau/k)*(1−exp(−k t)),  k=R/Lambda,

for identical initial flux and rotor history; add exp(−kt)||delta_psi(0)|| for different initial states, and bound current difference by ||delta_psi||/ell. This is v2DelayedNonlinearFluxResponseGronwallBound, NOT the full Maxwell-to-lumped near-field error theorem. A sudden 100V edge remains different before remote arrival for all tau>0: v2UnexpectedSwitchEdgeRejectSmoothDelayBound.

## Retarded *active* feedback (source port explicitly metered)

For active voltage feedback K i(t−tau), consider

    psi_dot = vbase(t) − R i(psi(t),theta(t)) + K i(psi(t−tau),theta(t−tau)).

For two trajectories with equal base drive, e=||delta_psi|| satisfies the Halanay incremental estimate D+e <= −a e + bdelay e(t−tau), with a=R/Lambda, bdelay=|K|/ell. Under the **sufficient** small-gain condition bdelay<a, histories converge exponentially at positive eta uniquely satisfying

    eta + bdelay exp(eta tau) = a.

For periodic base drive/rotor, the periodic delayed-input -> periodic stable-response operator is a contraction of factor <=bdelay/a<1, hence has one attracting periodic history. This closes v2RetardedNonlinearFluxFeedbackSmallGainExponentialStability at the stated model scope. If the sufficient inequality fails, the model is **uncertified**, not proven unstable.

The feedback is an external source. Its **signed work** is (K i(t−tau))·i(t), and base-plus-feedback equals total terminal work: v2RetardedActiveFeedbackPeriodicOrbitAndSignedWork. Known periodic feed-forward timing does not predict unexpected changes or transmit remote information ahead of the field front. tau includes physical flight >=distance/c and nonnegative controller latency.

Illustrative test: ell=.0256 H, Lambda=.0584 H, R=1 ohm, K=.25 ohm, tau=.0001000023826s; eta=7.35048 per second. Base-drive mean −2.66453W, external-feedback source +0.29478W, total terminal −2.36975W (2.36975W ideal net export). These are synthetic model values, not V2 measurements.

## Acceptance and remaining exact gates

Full producer and all 53 new adversarial tests are committed to this PR. Their Git blob hashes match the independently tested local files exactly. The complete independently verified ZIP v2_nonlinear_causal_maxcut_round4_20261115.zip also contains detailed local numerical receipts and the expanded proof. Complete local Python acceptance: 216/216 PASS, including preceding 163 tests. The local default wrapper passes; full historic SLSQP producer replay remains opt-in; pinned Agda/Nix unavailable and no Agda kernel PASS is asserted.

All **16 original strict P0–P4 gates remain OPEN** at their original strong levels: real/kernel calculus acceptance, hysteretic nonlinear passive memory, real hybrid switch/thermal limitations, full distributed Maxwell-to-motor error, global physical optimiser, original V2 netlist/flux/torque, complete signed shaft/controller/load/storage experiments and causal probe calibration.
# Sixth maximum cut: dynamically coupled causal line ↔ nonlinear reluctance-memory generator

Date: 15 November 2026. Owner: DASHI motor PR #1516 continuation. This closes **a restricted discrete-time, spatially delayed, bidirectional signed-port subgate**; it does not identify the original @madscience369 V2 winding/cable arrangement, source of electrical input, or demonstrate any anomalous source. Separate Don Smith/Filsinger time-indexed propagation and nonlinear-pump work is a *mathematical donor*, not identical physical hardware. Historic Maxwell, transmission-line theory and magnetic co-energy have their independent physical provenance.

## 1. Why this is a substantive new cut

Earlier the line energy law and the motor energy law were joined algebraically **if** they shared the same terminal. The previous finite packet simulator used a passive resistor termination, whereas the motor's model had a separate imposed terminal voltage. That did not implement a dynamically connected generator boundary.

This work solves **one implicit motor-boundary problem at the same electrical port as the reflected wave**. The waveguide has a strict propagation queue. Each winding's current determines the outgoing reflected wave; the incident wave determines the boundary voltage. Source-side feedback observes only the already-returned wave, never an instantaneous remote machine state.

## 2. Exact discrete traveling-wave law

For each phase take characteristic impedance `Z>0`, step `dt>0`, `N>=1` flight cells and a passive per-cell amplitude factor `0<=s<=1`. The guide's physical model distance is `d=N dt vfront`, with `0<vfront<=c`. Let forward/back wave arrays be `f_0..f_(N-1)`, `b_0..b_(N-1)`. At a tick:

- Source's locally received return: `c=s b_0`; source injects wave `u` (which may depend on `c`).
- Motor's arrived incident wave: `a=s f_(N-1)`.
- The motor's implicit signed current `i_bar` sets reflection `r=a-Z i_bar` and terminal voltage `v=a+r=2a-Z i_bar`.
- Shift `f'=(u,s f_0,...,s f_(N-2))`, `b'=(s b_1,...,s b_(N-1),r)`.

Per-phase sums are taken with Euclidean squares. Define finite in-transit energy

\[E_L=\frac{dt}{Z}(\|f\|^2+\|b\|^2).\]

Then the **identities of this explicitly defined packet model** are

\[
\begin{aligned}
W_S&=\frac{dt}{Z}(\|u\|^2-\|c\|^2),\\
W_T&=dt\,v\cdot\bar i=\frac{dt}{Z}(\|a\|^2-\|r\|^2),\\
D_L&=\frac{dt}{Z}(1-s^2)(\|f\|^2+\|b\|^2)\ge0,\\
\boxed{E_L'-E_L&=W_S-W_T-D_L.}
\end{aligned}
\]

A separate **exact `fractions.Fraction` check** covers negative signed terminal work, both directions and nonzero attenuation. These discrete identities are mathematically exact; floating-point motor simulations have independently checked energy residuals. The packet scheme is a passive idealised transmission-line network, not a proof of the full dispersive Maxwell initial-boundary problem or a physically measured original cable.

## 3. Reversible saturation and dissipative memory at the same wave port

Let `L(θ)` be a symmetric positive-definite multi-winding inductance matrix (the selected toy has equally spaced diagonal reluctance harmonics and nearest-neighbour mutual inductance). Use co-energy

\[
W'(i,\theta,z)=\frac12i^TL(\theta)i
+bI_s^2\sum_j\log\cosh(i_j/I_s)
+g i^Tz-\frac12h z^Tz.
\]

The constitutive law, magnetic energy, memory gradient and torque are

\[
\begin{aligned}
\lambda &= L(\theta)i+bI_s\tanh(i/I_s)+gz,\\
U &=i\cdot\lambda-W'=\frac12i^TLi+bI_s^2\sum_j\left(q_j\tanh q_j-\log\cosh q_j\right)+\frac12h\|z\|^2,\\
\nabla_\lambda U&=i,\quad\nabla_z U=hz-gi,\quad\partial_\theta U=-\tau_e.
\end{aligned}
\]

`L` has positive Gershgorin margin and `b,h>=0`, making the reversible stored energy nonnegative; `g` cancels in the Legendre-transform storage expression, but changes the flux/current and memory dynamics. This is a **single-rate dissipative magnetic-memory model**, NOT general rate-independent hysteresis.

To avoid assuming infinitely fast coil current, solve an implicit discrete-gradient step `y=(λ,z)` at **fixed rotor angle** with

\[
\begin{aligned}
\frac{\lambda'-\lambda}{dt}&=2a-(Z+R)\bar i,\\
\frac{z'-z}{dt}&=-\mu\bar u_z,\\
\bar\nabla U\cdot(y'-y)&=U(y')-U(y),
\qquad \bar i=(\bar\nabla U)_\lambda,\quad\bar u_z=(\bar\nabla U)_z.
\end{aligned}
\]

Therefore the **exact discrete identity conditional on solving these equations** is

\[U_{\mathrm{elec}}'-U=W_T-dt R\|\bar i\|^2-dt\mu\|\bar u_z\|^2.\]

Advancing the prescribed rotor angle while holding `(λ',z')` fixed increases magnetic energy by the separately metered mechanical work

\[W_{\mathrm{shaft}}=U(\lambda',z',\theta')-U(\lambda',z',\theta).\]

The total composed balance is

\[
\boxed{\Delta(E_L+U)=W_S+W_{\mathrm{shaft}}-D_L-D_{Cu}-D_{memory}.}
\]

It is critical to **not double-count** rotor work, magnetic energy returned from storage or source-feedback work. Negative `W_T` is permitted (generator sends power to the line), as is negative `W_S` (source bus receives wave energy). If both source and shaft work vanish, the combined stored energy is nonincreasing.

The numerical implementation uses the Gonzalez discrete gradient and an implicit nonlinear root solve. A successful residual tolerance is **not** a mathematically certified existence/uniqueness proof for arbitrary nonlinear parameters, and floating-point consistency is not Agda kernel acceptance.

## 4. Causality and the formerly hidden multirate obstacle

A source perturbation at tick 0 first alters the motor **after `N` ticks** and can first return to source **after `2N` ticks**. Tests compare a pulsed run with a quiet run and confirm *no earlier difference*. The model rejects nonpositive delay and front speed above `c`.

**The illustrative default is intentionally a long cable:** `dt=20 μs`, `N=3`, `front=0.7c` gives `d=12.59 km`. That long cable is not an invented property of V2. A 0.5 m cable at `0.7c` has about **2.3826 ns** one-way flight, and the same solver can verify several extremely short steps, but an entire ~2354 RPM motor revolution at that resolution would require over **10 million time steps**. Physically faithful small-cable motor studies therefore need a **multi-rate passive interface, causal delay/interpolation certificate, or an appropriate distributed model reduction**, not a fake microsecond-scale cable delay.

## 5. Acceptance and remaining exact lemmas

Implemented/tests in `scripts/v2_waveguide_motor_port_maxcut.py`, `tests/test_v2_waveguide_motor_port_maxcut.py`, `Artifacts/v2_waveguide_motor_dynamic_port_20261115.json`. Run `bash scripts/check_v2_waveguide_motor_port_maxcut.sh`.

| Target declaration | Current conclusion | Strong parent still OPEN |
|---|---|---|
| `v2DynamicBidirectionalWaveguideMemoryMotorSignedPort` | **Closed at defined discrete-network/successful-step scope:** the wave reflection and nonlinear memory update share the same terminal voltage-current pair | `v2DistributedLineMaxwellPassivityAndWavefrontBound` full continuum Maxwell/physical geometries |
| `v2LossyWaveguideMotorDiscreteTotalEnergyBalance` | **Exact algebraic finite-step identity**, plus exact Fraction and numerical regression, source and shaft work separated | P0 real calculus in Agda; continuum port Hamiltonian weld and original V2 power receipts |
| `v2CausalSourceMotorReturnRoundTripNonanticipation` | Causal numerical traces after `N`/`2N` steps with no early influence | Actual cable geometry/dielectric and P3 probe timing |
| `v2DiscreteGradientNonlinearMemoryHeatNonnegative` | Analytic nonnegative loss, numerical nonlinear root residual tests over m=3..12 | Validated all-time nonlinear hybrid flow and material-state hysteresis |
| `v2SubNanosecondCableMultiRatePassiveCouplingCertificate` | **OPEN:** only short-time 0.5m examples tested | Rigorous cross-rate coupling over a motor cycle, including PWM switching edges |
| `v2DynamicCoupledMotorLinePeriodicOrbitGlobalAttractor` | **OPEN:** former periodic proofs treat motor and line separately | Full joint waveguide+nonlinear memory+active switched-controller Poincaré/stability theorem |
| `reluctancePermeancePulseAgda29KernelAcceptance` | **OPEN:** compiler absent in this runtime | Agda typecheck and real-analysis formalisation |
| `originalV2*` P3/P4 | **ALL OPEN** | Actual winding, pulse netlist, material maps, shaft/thermal/all-source metrology, storage repeatability |

This result is an intentionally **restricted** dynamic boundary weld. It does not assert physical over-unity, environmental work, Don Smith hardware identity, universal 369 optimality, or an original V2 source observation.

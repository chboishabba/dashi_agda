# Magnetic-priority A×B×E×F: finite-voltage nonlinear current-tracking weld

**Scope:** exact current-error algebra and a conservative all-angle continuous-voltage feasibility condition for the existing *hypothetical* two-winding saturated co-energy and passive-memory model. Neither the original @madscience369 V2 geometry nor a real PWM inverter has been identified or measured. Converter recovery is fixed, not an optimisation variable.

## Exact same-machine dynamical port weld

With magnetic co-energy
\(W'(\theta,i,z)=\tfrac12 i^T L(\theta)i-\tfrac\beta4\sum i_j^4 + \sum k_j(i_jz_j-z_j^2/2)\),
flux and incremental inductance are
\(\lambda=L(\theta)i-\beta i^3+kz\),
\(H=\partial_i\lambda=L(\theta)-3\beta\operatorname{diag}(i_j^2)\).
The real winding law is \(v=Ri+\dot\lambda\), and the passive lag state obeys \(\tau\dot z=i-z\). For any differentiable angular reference \(r(\theta)\), bounded speed \(\omega\), and positive feedback gain \(g\), impose

\[
 v=Ri+\partial_\theta\lambda\,\omega+k\dot z
   +H\big(r_\theta\omega+g(r-i)\big).
\]

Whenever **(i)** \(H\) is positive definite and **(ii)** the actuator actually supplies this unsaturated voltage, the error \(e=i-r\) obeys **exactly** \(\dot e=-g e\), hence \(e(t)=e(0)e^{-gt}\). This remains true with a varying rotor speed, so current-tracking dynamics need not be postulated as an ideal current source. It is a conditional continuous-voltage theorem, **not** PWM tracking or a closed-loop rotor stability theorem.

For the supplied hypothetical source parameters, an all-angle Weyl bound proves positive incremental inductance throughout the admitted 0.025 A error tube, and the existing all-angle feedforward voltage bound plus rigorously bounded perturbations establishes conservative voltage feasibility. The tube is **assumed**, not established as an invariant set of the fully coupled motor/controller; however the linear error solution preserves the current tube under unsaturated voltage. For variable speed, the memory-lag error relative to the nominal-speed angular profile obeys \(\tau\dot{\delta z}=e-\delta z-\tau z_{\mathrm{ref},\theta}\delta\omega\). Hence the sufficient invariant lag bound is \(z_{\mathrm{tube}}\ge e_{\mathrm{tube}}+\max_j\tau_j\|z_{\mathrm{ref},\theta,j}\|_\infty\Delta\omega\). The stated 0.026 A lag tube passes this check for both illustrative controllers; 0.025 A does not. The speed envelope is externally required.

## Local numerical acceptance

- Matched nominal hypothetical output: 20 W bus in both memory-aware and copper-only reference controls (unchanged converter boundary).
- Nominal constant-speed tracking: sufficient voltage bounds 288.83 V (aware), 275.96 V (copper-only) including ±1 RPM speed allowance; current bound less than 7 A.
- With \(g=2500\,s^{-1}\), \(|e(0)|_\infty\le0.025\) A, \(|\delta z(0)|_\infty\le0.026\) A, ±1 RPM speed envelope: **299.68 V** (aware) and **286.76 V** (copper-only) conservative sufficient voltage bounds, versus invented 320 V limit.
- Nonlinear incremental inductance sufficient lower bound: above 0.038 H (both controls).
- Independent ODE numerical test confirms exponential current-error decay with prescribed rotor speed and no voltage clipping. Additional adversarial tests reject reduced voltage headroom, excessive current error, invalid gain; model voltage limits are conditional, not hardware measurements.
- **74/74 available magnetic-priority regressions passed locally**: 28 nonlinear memory, 19 mutual-winding, 11 finite-inertia, 16 current tracking/fully coupled integration. These are not 74 independent physical gates.

## The critical remaining Ω barrier

The previously committed numerical **30-turn** rotor simulation with *imposed* magnetic current found a near-periodic motor response. Its speed ripple is less than 1 RPM and its storage-rate discrepancy is small. The current controller above is proven *conditionally* on a speed tube, but **the coupled electromechanical speed tube has not been proved invariant under actual controller voltages** and no rigorous Poincaré fixed-point/existence-and-stability result has been established for the full coupled rotor+memory+current dynamics. Thus neither a complete periodic orbit nor a real switching actuator may be marked closed.

Recommended next proof producer: a rigorously bounded return-map enclosure for the full \((\theta,\omega,i,z)\) dynamics with saturation guards, motor torque limit and voltage clipping. If that cannot be certified, provide an explicit failing counterexample instead of further optimistic performance estimates. Following that, physical hardware characterization must identify magnetic L(θ,i,z), core/hysteresis/eddy loss, motor torque/efficiency map, actual bus, switching and actual stored-energy endpoints. The 16 original P0–P4 strong gates remain OPEN. Attribution: constructed comparison is not original V2 hardware and must not be mixed with Smith/Filsinger designs.

## Additional full coupled numerical cross-check (not a proof of stationarity)

The same continuous-voltage controller is now integrated inside the finite-inertia rotor ODE, with evolving actual currents, passive magnetic lag, voltage clipping, torque limit, speed and every signed energy account. In the **12-turn** synthetic test the memory-aware case requires about 30.4512 W motor shaft supply versus 32.7033 W for the naive copper-only case; both export approximately 20.000 W at the same fixed bus conversion boundary. Current error is below \(10^{-6}\) A over the last turn, voltage remains below 152 V (aware) and 118 V (naive), and neither branch clips voltage or motor torque. Numerical ledger errors are about \(10^{-6}\) J. This makes the prior forced-current numerical result more realistic, but **does not prove a stationary operating point**: the last-cycle rotor storage rate is about +0.024 W (12 turns), so the previously mentioned exact 30-turn convergence does not automatically carry over. Full coupled model periodicity, switched PWM and physical load-dependent motor calibration stay OPEN.

Updated local acceptance **74/74** magnetic-priority tests, comprising 28 passive-memory, 19 mutual geometry, 11 previous finite-inertia and 16 new exact-tracking/full-coupled tests. Original V2 16 strict gates remain OPEN.

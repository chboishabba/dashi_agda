# J29–J32 single-cut numerical reconfirmation: full six-event hybrid period, 9×9 tangent and sampled Banach margin

**24 November 2026 | PR #1537 | original Smith/Filsinger-attributed synthetic nine-state source-only circuit | NOT an exact-periodic-orbit theorem or real hardware demonstration.** This is one integrated full-period audit, not J29B/J29C standalone event promotions. The unchanged original J25 equations and exact rational J23 initial decimal seed are independently transcribed and integrated, including both actual spark transitions, physical max-positive-part U/V diode currents, finite loss, nonlinear HF capacitor and both signed forcing quadratures. Controller driver OFF, synthetic incident wave ON. No GitHub Actions, Agda kernel, original J18 native-byte executable, apparatus metering or naturally supplied field.

## One completed numerical end-to-end test; precise numerical/rigorous separation

The locally executed independent Python/SciPy DOP853 nine-state hybrid integrator at `tau=20*pi/11` returns the physical spark mode ON and the following **numerical** ordered events. Reference locations are the original J24 source numerical centres, not artificially supplied switches:

| # | Event | New computed model time | J24 centre (approx) |
|---:|---|---:|---:|
| 1 | V diode ON | 3.389367008894 | 3.389367008882 |
| 2 | spark ON→OFF | 3.491292721190 | 3.491292721185 |
| 3 | spark OFF→ON | 3.515340479143 | 3.515340479137 |
| 4 | U diode ON | 4.275489023275 | 4.275489023213 |
| 5 | V diode OFF | 4.323837945006 | 4.323837947628 |
| 6 | U diode OFF | 4.928751407316 | 4.928751406857 |

Across the six event states, the maximum numerical component discrepancy from J24's original centres is about **1.7683e-8**, below its original radius **1e-4**. The largest event-time difference is about **2.6225e-9** dimensionless model time. The source-seed full-`tau` return defect is **9.2553e-12** in the 9-state infinity norm under the independent hybrid-state integration; a tighter joint tangent integration reports **1.9174e-12**. A second DOP853 integration from J28B's exact rational **75-step centre** at `t=4.26534095` independently reproduces U ON, V OFF and U OFF. **These checks confirm a numerical candidate, not the validated inclusion of the exact solution, not J24 6/6 boxes and not a mathematical fixed point.**

The reproducible local three-script campaign and exact JSON samples/9×9 matrix are in the conversation-side download bundle **Filsinger_full_six_event_numerical_audit_20261124.zip**, SHA256 `34e4892b62672b84e93aff4124f10bf74fd754e736d9af1601c363370280e18b`, and its original J28B checkpoint Git blob `74c1a94b30c44a772016c93b39558bc446359832`. Locally executed scripts' Git-hash bytes (when placed at repository `scripts/` paths) are: six-event `69aa771ed0af9fb0b33d4109cbf7d9cc1dd44557`, nine-by-nine tangent `481cc5b693e7244d582a136aa06d828fb41d46b7`, nonzero-ball probe `06cb58ae1141ead5867ba5e8dbc7246cbfa18edb`. They are independent local tools, **not source-owner byte-execution**. [Machine-level summary](../../Artifacts/smith-filsinger/j29_j32_full_period_numerical_6event_monodromy_ball_audit_20261124.json) records the strict claim firewall.

## Five-setting independent numerical convergence control

The full six-event integrator was independently replayed five times at progressively tighter tolerances and smaller maximum step lengths. **All five runs retained exactly V ON → spark OFF → spark ON → U ON → V OFF → U OFF**, with the terminal spark ON. These are not outward error estimates:

| DOP853 relative tolerance | Maximum step | Terminal defect infinity norm |
|---:|---:|---:|
| 2e-10 | 0.0200 | 1.68245e-9 |
| 2e-11 | 0.0100 | 2.01440e-10 |
| 3e-12 | 0.0060 | 2.88702e-12 |
| 6e-13 | 0.0030 | 6.31717e-12 |
| 2e-13 | 0.0015 | 1.87472e-12 |

The last three values fluctuate on the ~1e-12–1e-11 numerical-solver floor, so they **must not be extrapolated to a theorem** about the exact residual. The six event labels and approximate times remain stable through the refinement. The five-run receipt is appended to the [single machine summary](../../Artifacts/smith-filsinger/j29_j32_full_period_numerical_6event_monodromy_ball_audit_20261124.json). The untouched local step-state traces are in the conversation-side source bundle.

## Independently reproduced nine-by-nine hybrid monodromy

Solve the full `9+81` ODE, with the original signed J25/J28B Jacobian of the physically active U/V positive-part sectors. A diode current is zero at its kink, so state and vector field are continuous and the diode saltation is exactly identity, although the Jacobian changes. Apply **both real spark saltations** to the tangent:

```
S_spark = I + (f_after - f_before) e_bank^T / f_before,bank
det S_spark = f_after,bank / f_before,bank.
```

The resulting numerical finite-model return derivative `M=DP_tau(x0)` has:

| Computed numerical diagnostic | Result |
|---|---:|
| spectral radius `rho(M)` | **0.888103794154** |
| `sigma_min(I-M)` | **0.119506176076** |
| `cond_2(I-M)` | **11.30763505534** |
| `||(I-M)^(-1)||_inf` | **11.731499449908** |
| Original J24 independently reported inverse norm | **11.731499450011** |
| spark OFF determinant | **-2.26790644522** |
| spark ON determinant | **-0.857393123999** |

The inverse norm agrees with the previously committed J24 original donor to **~1.04e-10**, a strong independent source-equation cross-check. Nine coordinate directions with symmetric `epsilon=1e-4` provide 18 perturbed trajectories, **each with all six expected event labels**, and a relative Jacobian/FD difference `2.51294e-6`. Separate `3e-4` and `3e-5` finite differences show truncation/ODE noise limits; they are not exact error certificates. A numerical Newton correction has norm `2.0451e-12`; the corrected defect at a different solver configuration is `1.3549e-11` and must **not** be marketed as a monotone reduction.

## Full proof-ball probe and remaining exact mathematical lemmas

On the pre-existing J24 proposed sup-norm initial-state ball of radius `r=1e-7`, the separate independent tangent calculation tested all **18 coordinate directions** `x0 ± r e_j` (no interpolation over the continuum):

| Quantity | Independent numerical observation | Required rigorous promotion |
|---|---:|---|
| Maximum sampled `||DP(x)-DP(x0)||_inf` | **5.69309e-7** | Provable upper bound `<0.001` on *every* point in ball |
| Maximum sampled `||I-C(I-DP(x))||_inf` | **8.54400e-7** | Rigorous whole-ball `q<1` |
| `||C(P(x0)-x0)||_inf` | **2.04506e-12** | Rigorous centred defect plus return-mode proof |
| J24 original conditional centre defect budget | **8.42406e-9**, unvalidated | Outward rational interval original ODE result |

These values show a **credible numerical margin for a computer-assisted proof**, not the proof. Neither 18 sampled states nor singular values at a sampled centre guarantee the entire nonzero state ball, continuous parameter family, or exact return defect.

The source-grounded **maximum cut** remains all of the following as *one end-to-end certificate*:
1. **Physical/interval flow**, retaining the original J28B/J29A validated stage-75 checkpoint, with no skipped transitions; validate V OFF, U OFF, and the final U/V-inactive smooth interval through irrational `tau`, and all original J24 9/9 state-box inclusions. Preserve exact source forcing phase and both real spark saltations.
2. **Nonzero-ball derivative and defect**, original J24 rational preconditioner, full `DP_tau(B)` over `r=1e-7` and certified `||P_tau(x0)-x0||`; do not accept sampled numerics as inequalities.
3. **Banach/Krawczyk**, prove the full self-map with strict rational inequalities and uniform six-event itinerary on B. Only this would establish a unique nominal exact periodic fixed point and 11-fold transport to source `T=20*pi`. Five-parameter uniform result requires its own interval family.
4. **Physical source/receiver**, independently remain open. The original 0/4 pin edges and 0/24 measured energy roles cannot be inferred from synthetic oscillation; finite-positive coil/load loss excludes exact 100% efficiency in this topology.

**Authoritative current certified mathematical status stays 4/6 original event crossings and 3/6 original J24 state boxes**; the new independent numerical results are a fast falsification/feasibility diagnostic, not a replacement for the original exact interval producer. No small-step PR split or new theorem headline is warranted.

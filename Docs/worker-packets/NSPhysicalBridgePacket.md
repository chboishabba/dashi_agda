# NS Physical Bridge Packet

Date: 2026-06-03

Worker: W1 NS physical bridge data/proof

Status: NO-GO for Sprint 40 promotion.  The available artifacts define useful
shell diagnostics and a falsification surface, but they do not provide a
formal proof of

```text
Q_K <= C * R_K^+ * concentration_K^theta
```

and they do not provide all physical bridge observables on actual 3D
Navier-Stokes data.

## Sources Inspected

- `Docs/ClaySprintFortyCalculationHarvest.md`
- `Docs/ClaySprintThirtyNineConcentrationSourceBudget.md`
- `Docs/ClaySprintThirtyEightSourceDecayPhysicalBridgeAudit.md`
- `Docs/ClaySprintTwentyNineAnalyticResidueHarness.md`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_theta_full_sweep.csv`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/manifest.json`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/checks.json`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/shell_enstrophy.csv`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/ev5_trace.csv`
- `Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/theta_profile.csv`
- `../dashiCFD/scripts/ns_theta_full_sweep.py`
- `../dashiCFD/scripts/ns_ev5_shell_enstrophy.py`
- `../dashiCFD/README.md`

## Definitions

Use the following as the formalization target, with `epsilon > 0` fixed only
as a numerical audit guard and removed or bounded explicitly in any proof.

### Shell Projection Convention

For a periodic grid vorticity field `omega`, the current CFD adapter uses a
dyadic Fourier shell projection:

```text
j(xi) = floor(log2 |xi|) for |xi| >= 1
j(0) = 0
P_j omega = Fourier modes with shell index j
E_j = sum_{xi: j(xi)=j} |fft2(omega)(xi)|^2 / N^4
```

The normalization guard compares:

```text
0.5 * sum_j E_j
```

against the truth enstrophy.  In the inspected run this guard passed with
`max_abs_error = 5.867323848995909e-10` and
`max_rel_error = 1.9607476147427937e-09`.

This is a 2D diagnostic projection over snapshots, not a 3D Littlewood-Paley
theorem.  A formal 3D version should replace the grid `fft2` projection by a
fixed smooth dyadic projector `P_K` on the physical domain, with cutoff fixed
during differentiation.

### Q_K

Physical bridge target:

```text
T_K = | integral (P_K S(u) omega) dot omega_K dx |
D_K = nu * 2^(2K) * ||omega_K||_2^2
Q_K = T_K / (2^(K/2) * D_K + epsilon)
```

Here `S(u) = (grad u + grad u^T) / 2`, `omega_K = P_K omega`, and `T_K`
is the physical vortex-stretching contribution seen at shell `K`.  Existing
Sprint 38/39 docs use this normalized stretching convention.  The inspected
CFD artifacts do not compute `T_K`, so they cannot directly evaluate `Q_K`.

### R_K^+

`R_K^+` is the positive/expansive source residue at shell `K`, inherited from
the Sprint 30-39 residue program:

```text
R_K^+ = B_K^+ / (P_K_count + epsilon)
```

where `B_K^+` is the count or weight of expansive/unbalanced positive
transitions and `P_K_count` is the admissible transition count or mass at
scale `K`.  This is a combinatorial/source observable.  The inspected CFD
artifacts do not compute `B_K^+`, `P_K_count`, or a physical pullback from
vorticity dynamics to this residue.

### concentration_K

Use the Sprint 39 aligned concentration gate:

```text
concentration_K = alignedConcentration(K)
alignedConcentration(K) <= C_conc * 2^(beta_K * K)
beta_K = log2(alignedConcentration(K)) / K
```

The intended diagnostic bridge ratio is:

```text
adjusted_C_K =
  Q_K / (R_K^+ * concentration_K^theta_bridge + epsilon)
```

The source budget condition recorded in Sprint 39 is:

```text
gamma_K + eta_K * log2(p) - theta_bridge * beta_K > 1/2
```

The inspected CFD artifacts do not compute `alignedConcentration(K)`,
`beta_K`, `gamma_K`, or `eta_K`.

### theta

There are two overloaded theta symbols.  They must remain separate.

`theta_bridge` is the exponent in the requested bridge:

```text
Q_K <= C * R_K^+ * concentration_K^theta_bridge
```

It is a parameter in the concentration-aware physical bridge.  It is not
estimated by the current CFD artifacts.

`theta_NS(k,t)` is the runtime tail-flux diagnostic in the CFD scripts:

```text
E_tail(k,t) = sum_{j >= k} E_j(t)
Diss_tail(k,t) = 2 * nu * sum_{j >= k} 2^(2j) * E_j(t)
dE_tail/dt = Flux_tail - Diss_tail
theta_NS(k,t) = |Flux_tail(k,t)| / Diss_tail(k,t)
Theta = sup_k sup_t theta_NS(k,t)
```

`theta_NS < 1` is explicitly marked by the scripts as evidence-only, not as a
BKM/Serrin equivalence, not as an NS theorem, and not as Clay evidence.

## Numerical Findings

### EV5 Truth Trace

Artifact:
`Docs/Images/clay-analytic-sprint/sprint40_calc/ns_ev5_cpu/`.

Run metadata:

```text
source_truth = ../dashiCFD/outputs/truth_ns_ev5_cpu_2026-06-01T014101.npz
grid_size = 128
snapshots = 11
dt = 0.01
nu = 0.0001
K_star = floor(3/4 * log2(1/nu)) = 9
finite shell rows = j = 0..6
```

The theta profile is unavailable:

```text
reason = no shell cutoffs at or above K_star in finite theta vector
theta_profile.csv rows = header only
promotion_status = diagnostic_unavailable_no_ns_theorem
```

EV5 diagnostics:

```text
v7_decreasing = true
v2_bounded = true
ev5_admissible = true
lane7_first = lane7_last = 0
mean_shell_max = 2.5219064786911067
q_increases = 1
two_phase_ok = false
evaluation_status = falsified
```

Interpretation: this trace is a useful projection sanity check and a useful
falsification of the old scalar `Q_log` diagnostic.  It is not data for the
requested physical bridge because `Q_K`, `R_K^+`, `concentration_K`, and even
the high-shell `theta_NS(k,t)` vector at `k >= K_star` are unavailable.

### Synthetic Theta Sweep

Artifact:
`Docs/Images/clay-analytic-sprint/sprint40_calc/ns_theta_full_sweep.csv`.

The sweep has `1600` rows over five synthetic shell-energy regimes, five
viscosities, and cutoffs `1..64`.  Promotion is disabled in every row.

Global counters:

```text
theta_k > 1 rows = 196 / 1600
barrier_pass rows = 0 / 1600
combined_ratio >= 1 rows = 1600 / 1600
```

Worst observed diagnostic row:

```text
trace = rough
nu = 0.0001
k = 1
theta_k = 1.1028037662310666
K_star = 4
K_kolmogorov = 9
edge_leakage_ratio = 0.21212388628489248
combined_ratio = 1.314927652515959
barrier_pass = false
```

Trace maxima:

```text
rough max theta_k range = 1.0408363316717624 .. 1.1028037662310666
inviscid max theta_k range = 1.029003777196406 .. 1.0510226018402122
kolmogorov max theta_k range = 1.0001249718247474 .. 1.013046459604463
near-critical max theta_k = 1.0
smooth max theta_k = 1.0
```

The danger shell is always `k = 1` for the global maxima.  This localizes the
observed hazard to low shells in the synthetic traces; it does not prove a
uniform high-shell margin.

## Proof Sketch Status

The bridge cannot currently be formalized from the available packet.  A proof
would need at least the following lemmas, none of which are established by the
inspected artifacts:

1. A fixed-shell physical identity connecting `T_K` to the dyadic tail flux
   with commutator errors controlled uniformly in `K`.
2. A projection theorem transferring the combinatorial/source residue
   `R_K^+` to physical vortex-stretching alignment for actual NS trajectories.
3. A concentration theorem bounding aligned shell mass by
   `concentration_K^theta_bridge` with explicit `beta_K`.
4. A high-shell budget proving
   `gamma_K + eta_K * log2(p) - theta_bridge * beta_K > 1/2` uniformly.
5. A 3D continuum limit argument replacing the current 2D grid diagnostics.

Without these lemmas, the requested inequality remains a conditional target.
The current numerical data instead supports a no-go/falsification posture:
the available EV5 trace has no high-shell theta vector, and the synthetic
sweep contains above-boundary tail-flux ratios plus no passing combined-ratio
rows.

## Formalization Payload

Safe Agda-facing statement:

```text
record NSPhysicalBridgeAssumptions : Set where
  field
    Q_K : Nat -> Real
    R_K_plus : Nat -> Real
    concentration_K : Nat -> Real
    theta_bridge : Real
    C : Real
    nonnegative_Q : forall K -> 0 <= Q_K K
    nonnegative_R : forall K -> 0 <= R_K_plus K
    concentration_ge_one : forall K -> 1 <= concentration_K K
    bridge_bound :
      forall K -> Q_K K <= C * R_K_plus K * concentration_K K ^ theta_bridge
```

Current receipt should not assert `bridge_bound`; it should record it as an
open assumption or failed promotion gate.

Recommended next executable diagnostic:

```text
For each shell K and transition t:
  compute T_K from P_K S(u) omega dot omega_K
  compute D_K = nu * 2^(2K) * ||omega_K||_2^2
  compute Q_K = T_K / (2^(K/2) * D_K + epsilon)
  compute or import R_K^+
  compute alignedConcentration_K
  emit adjusted_C_K = Q_K / (R_K^+ * alignedConcentration_K^theta_bridge + epsilon)
```

Pass criterion: `sup_K adjusted_C_K < infinity` on a real trace family with
an analytic proof of the observables.  Fail criterion: `adjusted_C_K` grows
with `K`, or any required observable is unavailable.

Implemented follow-up:

```text
script: scripts/ns_diagnostic_harness.py
output: Docs/Images/clay-analytic-sprint/sprint40_bridge_budget/
report: Docs/ClaySprintFortyBridgeBudgetEstimatorRun.md
```

The implemented bridge-budget table emits `Q_K_proxy`, `R_plus_K_proxy`,
`aligned_concentration_K`, `theta_NS_K`, `budget_hat_K`, and
`adjusted_bridge_ratio`.  On the two real N32 tail2 dashiCFD traces, the run
remains fail-closed: the inputs are 2D scalar vorticity, so literal 3D
`omega dot grad(u) omega` and physical `Q_K` are unavailable.  The traces also
only have three nonzero shells `[2,3,4]` at or above `K_star = 2`, below the
five-shell high-shell fit gate.

## Packet Verdict

FAIL / NO-GO.

The packet supplies definitions and numerical diagnostics, but not a proof
and not a successful numerical bridge.  The Sprint 40 bridge should remain
open with promotion blocked.

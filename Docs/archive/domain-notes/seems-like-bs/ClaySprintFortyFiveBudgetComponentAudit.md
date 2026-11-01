# Clay Sprint 45 Budget Component Audit

Date: 2026-06-04

Sprint 45 consumes the Sprint 39 budget algebra and the Sprint 44 residue
semantics audit.  The diagnostic state is now sharper:

```text
strict DASHI red does not control observed physical stretching
pressure-relaxed strict red does not rescue the strict classifier
stretch-sign / strain physical residues keep the bridge numerically plausible
budget_K > 1/2 still fails
```

The target inequality remains:

```text
budget_K = gamma_K + eta_K * log_2(p) - theta * beta_K > 1/2
gap_K    = 1/2 - budget_K
```

## Output Contract

Sprint 45 adds:

```text
ns_budget_component_audit.csv
```

The table emits one row per `(time,K,theta,residue_key,p)`:

```text
source_K
gamma_fit
eta_fit
eta_log2p_fit
beta_fit
budget_if_gamma_only
budget_if_eta_only
budget_if_independent_gamma_eta
budget_gap_gamma_only
budget_gap_eta_only
budget_gap_independent_gamma_eta
double_count_warning
budget_status
promotion_status
```

`source_K` is the selected residue observable, for example
`Rplus_stretchSign`.  When `gamma` and `eta` are inferred from that same
observable, the harness records:

```text
same_observable_gamma_eta = 1
independent_gamma_eta = 0
```

and the combined `gamma + eta*log2(p)` budget is only a counterfactual.  It
cannot promote without an independent BT/ultrametric observable.

## Recorded Runs

Artifact root:

```text
Docs/Images/clay-analytic-sprint/
```

Command form:

```bash
python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz \
  --budget-component-audit \
  --residue-key Rplus_stretchSign \
  --out-dir Docs/Images/clay-analytic-sprint/sprint45_budget_components_N64_seed0
```

Current summaries:

| run | residue | gamma range | beta range | inf gamma-only budget | worst gamma gap | status |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| N32 seed0 | `Rplus_stretchSign` | `0 .. 0` | `0.01191 .. 0.02572` | `-0.02572` | `0.52572` | `FAIL_BUDGET_BELOW_HALF` |
| N64 seed0 | `Rplus_stretchSign` | `0 .. 0` | `0 .. 0.000995` | `-0.000995` | `0.500995` | `FAIL_BUDGET_BELOW_HALF` |
| N64 seed1 | `Rplus_stretchSign` | `0 .. 0` | `0 .. 0.001777` | `-0.001777` | `0.501777` | `FAIL_BUDGET_BELOW_HALF` |

For every tested prime `p = 2,3,5,7,11,71`, `eta_log2p_fit = 0` because eta
is converted from the same source slope as gamma.  There is no measured
independent ultrametric decay in these runs.

## Interpretation

The audit localizes the Sprint 44 budget failure:

```text
concentration is not the main blocker
gamma is zero on the selected physical residue observable
eta is zero unless supplied by an independent BT lane
the route is half a derivative short
```

The next proof-relevant target is therefore not another blind residue
definition sweep.  It is an independent source-depletion mechanism:

```text
IndependentDASHISourceDecayComponents :
  gamma + eta*log2(p) > 1/2
```

with a no-double-counting guard:

```text
NoDoubleCountingGammaEta :
  SameObservable gamma eta ->
  not (validBudget = gamma + eta*log2(p) - theta*beta)
```

## Boundary

This is a diagnostic audit only.  It does not prove independent DASHI source
decay, actual ternary lineage, stretch absorption, no finite-time blowup, or
Clay Navier-Stokes regularity.  All promotion flags remain false.

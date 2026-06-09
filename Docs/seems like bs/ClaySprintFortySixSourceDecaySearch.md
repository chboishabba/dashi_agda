# Clay Sprint 46 Source Decay Search

Date: 2026-06-04

Sprint 46 consumes the Sprint 44/45 state:

```text
strict symbolic red: falsified
pressure-relaxed strict red: falsified
physical stretch-sign / strain residue: bridge-plausible
measured gamma: 0
measured eta: 0
budget: about 0, not > 1/2
Clay promotion: false
```

The question is now narrow:

```text
Is there an independently measurable DASHI source-decay component,
or is the current source-budget route falsified under 3D diagnostics?
```

## Output Contract

Sprint 46 adds:

```text
ns_source_decay_search.csv
ns_source_decay_summary.json
```

The CSV emits:

```text
K
Rplus
rho_K
angular_coherence
angular_sigma_fit
pressure_survival
pressure_sigma_fit
candidate_budget
bt_eta_status
double_count_warning
route_status
```

The governance rule is conservative:

```text
used_in_budget = 0
```

for every raw candidate.  A candidate exponent can guide the next proof search,
but it cannot receive Clay-facing budget credit without an independent
observable proof.  BT eta is recorded as unavailable unless real BT lane labels
exist.

## Candidates

Red persistence:

```text
rho_K = Rplus_(K+1)/(Rplus_K + epsilon)
pass requires rho_K < 1/sqrt(2)
```

Angular coherence:

```text
angular_coherence_K ~ 2^(-sigma K)
```

Pressure survival:

```text
pressure_survival_K = 1 - PressureDecorrelationScore_K
pressure_survival_K ~ 2^(-sigma_p K)
```

BT lane decay:

```text
eta_unavailable_no_BT_lane_observable
```

## Recorded Runs

Artifact root:

```text
Docs/Images/clay-analytic-sprint/
```

Command form:

```bash
python scripts/ns_diagnostic_harness.py \
  --truth ../dashiCFD/outputs/truth3d/ns3d_N64_seed0.npz \
  --source-decay-search \
  --residue-key Rplus_stretchSign \
  --out-dir Docs/Images/clay-analytic-sprint/sprint46_source_decay_N64_seed0
```

Current summaries:

| run | rho pass rows | sup rho | angular sigma max | pressure sigma max | candidate budget sup | route status |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| N32 seed0 | `0 / 588` | `1.12873` | `0` | `0` | `-0.01191` | `SOURCE_BUDGET_ROUTE_FALSIFIED_UNDER_CURRENT_DIAGNOSTICS` |
| N64 seed0 | `13 / 728` | `1.12889` | `0.00794` | `0.04726` | `0.04726` | `POSITIVE_BUT_SUBHALF_DECAY_DIAGNOSTIC` |
| N64 seed1 | `13 / 728` | `1.07239` | `0` | `0.03289` | `0.03205` | `POSITIVE_BUT_SUBHALF_DECAY_DIAGNOSTIC` |

## Interpretation

The N32 validation run finds no independent source decay:

```text
angular_sigma_fit = 0
pressure_sigma_fit = 0
rho_K does not pass the 1/sqrt(2) persistence gate
BT eta is unavailable
```

The N64 runs show a weak pressure-survival diagnostic:

```text
N64 seed0: pressure_sigma_fit max = 0.04726
N64 seed1: pressure_sigma_fit max = 0.03289
```

That is positive, but far below the half-derivative target.  Angular decay is
zero or tiny, rho mostly fails the persistence threshold, and BT eta remains
unavailable.

So Sprint 46 does not produce a budget-creditable independent source component:

```text
no candidate sigma > 1/2
no BT lane observable
no used_in_budget credit
no Clay promotion
```

The current source-budget closure route therefore remains non-closing under
the present 3D diagnostics.  The only lead is a subcritical pressure-survival
decay that would need an independent proof role and additional independent
components before it could matter.

## Boundary

This is a diagnostic audit only.  It does not prove independent DASHI source
decay, actual ternary lineage, stretch absorption, no finite-time blowup, or
Clay Navier-Stokes regularity.  All promotion flags remain false.

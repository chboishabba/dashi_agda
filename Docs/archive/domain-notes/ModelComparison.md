# Surrogate Model Comparison

The reduced photonuclear prototype now supports two model families on the same
Dashi-derived observable interface:

- GBW-style response:
  [`scripts/prototype_gbw.py`](../scripts/prototype_gbw.py)
- IPsat-style response:
  [`scripts/prototype_ipsat.py`](../scripts/prototype_ipsat.py)

Both consume the same extracted observables:

- `delta_defect`
- `promoted_d0`
- `g_star`
- `q_s`
- `photon_energy`

## Purpose

This comparison layer is not a physics fit. Its role is narrower:

- hold the Dashi explanatory variables fixed
- vary only the reduced response model
- inspect which explanatory conclusions are stable across model assumptions

## CLI

```bash
python scripts/compare_surrogate_models.py \
  --state scripts/examples/near_miss_state.json
```

The output reports:

- the shared Dashi observables
- GBW-style response
- IPsat-style response
- the yield/residual gap between the two surrogates
- a shared explanation scorecard for each surrogate

## Interpretation

If both surrogates produce compatible qualitative explanations from the same
Dashi observables, that supports the claim that the explanatory content is not
an artifact of a single placeholder model family. If they diverge strongly, the
next task is not to declare a winner, but to identify which observable or model
assumption is driving the divergence.

The scorecard is intentionally non-fitting. It combines:

- normalized residual
- MDL burden
- surrogate confidence penalty

Lower explanation cost means the surrogate explains the Dashi-derived
observables more efficiently under its own internal criteria. It does not mean
the model is physically correct.

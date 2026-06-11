# GBW-style response layer

## Scope
This note defines the minimal surrogate response layer that consumes the Dashi observables (`Y_D0`, `g⋆`, defect intensity) and produces a GBW-inspired charm-yield proxy. It is intentionally symbolic: the goal is to expose the few numbers a future runner will plug into GBW-type formulas without claiming any calibrated fit.

## Interface assumptions
- `Y_D0 := O_D0(Dx, χ_D0) + η` is the promoted near-miss observable from [Docs/CharmPhotoproduction.md](./CharmPhotoproduction.md).
- `g⋆` is Dashi’s MDL-inferred latent parameter (interpreted as a saturation-scale surrogate).
- `D_defect := |Δx|` is the defect-channel intensity (projected halo energy) defined in [Docs/PhotonBridge.md](./PhotonBridge.md).
- `ω_photon` is the equivalent-photon energy extracted from the bridge; it sets the light-cone momentum fraction `x ≃ ω_photon/√s`.

Any runner must provide these inputs; the GBW-style layer only reads them.

## GBW-inspired response
The reduced GBW surrogate uses the following placeholder expressions:

1. Saturation scale proxy:

```
Q_s^2(x;λ,x₀) := (x/x₀)^(-λ) × T_A
```

`T_A` is an optional thickness scaling (set to 1 for a first prototype), while `λ` and `x₀` are symbolic parameters.

2. Dipole cross-section surrogate:

```
σ_dipole(r, x) := σ₀ × (1 - exp(-r^2 Q_s^2(x)/4))
```

Replace the dipole size `r` with a defect-channel length scale derived from `D_defect`, e.g. `r ≃ 1/√D_defect`.

3. Charm-yield proxy:

```
Y_model := N_D0 × [1 - exp(-Y_D0(g⋆)/σ_dipole)]
```

`N_D0` is a normalization placeholder (default `1`). `Y_D0(g⋆)` is the Dashi prediction at the inferred `g⋆`.

The layer outputs `Y_model` plus the residual `ΔY := Y_D0 - Y_model`, which drives later MDL decisions.

## Parameter bookkeeping
- `λ`, `x₀`, `σ₀`, and `T_A` remain symbolic placeholders. Document their intended meaning and note that they will be tuned when a data-fitting lane is added.
- The mapping from `g⋆` to `Q_s^2` is defined by a user-provided translator `q_from_g(g⋆, x_ref)`, which currently can be `q_from_g(g, x) := g`.
- The `x_ref` value is read from `ω_photon` via `x_ref := ω_photon / √s`.

## Summary
This note supplies the minimal GBW-style response interface:
- reads `Y_D0`, `g⋆`, defect intensity, and photon energy,
- computes a symbolic `Q_s^2` and dipole cross-section,
- emits the surrogate `Y_model` and residual `ΔY`.

It is intentionally agnostic about fits: the numeric parameters stay placeholders, and the module only defines what a future runner must feed into this surrogate and what it returns. Subsequent lanes will hook this response into the saturation/numerical stack and eventually to CMS data.

## Companion model

The prototype also supports a second surrogate family through
[`scripts/prototype_ipsat.py`](../scripts/prototype_ipsat.py). That layer is
not meant to settle which saturation picture is correct. It exists so the
prototype can compare how much of the explanation is stable across model
assumptions versus how much is model-dependent.

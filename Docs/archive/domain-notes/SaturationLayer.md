# Gluon saturation layer

## Purpose
With the equivalent-photon bridge and charm observables in place, the next numerical layer is about how those observables map to saturation-scale models. Dashi supplies `Y_D0` (the promoted near-miss observable) and the MDL inverse problem that infers a latent parameter `g⋆`. This note introduces a minimal set of gluon-density/saturation models and describes how `g⋆` and `Y_D0` are mapped into their variables, along with the agreement/deviation/new-structure criteria we would track.

## Candidate saturation models
- **GBW (Golec-Biernat–Wusthoff)**: saturation scale `Q_s^2(x) = (x/x_0)^−λ` with `λ` and `x_0` as tunable parameters plus nuclear thickness scaling. The Dashi latent `g` is interpreted as the `Q_s^2` value selected by the MDL inverse problem.
- **IPsat**: includes DGLAP-evolved gluon density `xg(x, μ^2)` together with an eikonalized dipole cross-section. Here `g⋆` maps to `xg(x, μ^2)`, and the projected observable `Y_D0` constrains both the nuclear thickness profile and the impact-parameter weighting.
- **rcBK / JIMWLK**: nonlinear evolution equations produce a scale-dependent unintegrated gluon distribution `φ(x, k_T^2)`. The Dashi inference gives a coarse-grained estimate of the saturation scale `Q_s^2` at fixed `x` and `k_T`, with `Y_D0` measuring how the near-miss observable responds to changes in the nonlinear kernel parameters.

Each model shares a saturation scale `Q_s^2` or related density variable, which is the common target for Dashi’s `g⋆`. No numeric fits are performed; instead we lay out what would be compared against a future fit.

## Observable → model mapping
- Dashi axis: `Y_D0 := O_D0(Dx, χD0) + η` and `g⋆ = argmin_g [−log p(Y_D0 | g) + λ L(g)]`.
- Model axis: variables such as `Q_s^2(x)` (GBW), `xg(x, μ^2)` (IPsat), or `φ(x, k_T^2)` (rcBK).
- Mapping rule: treat `g⋆` as a light-weight proxy for the saturation scale—e.g., `g⋆ ≃ Q_s^2(x_ref)` when the near-miss photon energy maps to `x_ref`. When the model has additional structure (impact parameter, transverse momentum), Dashi observables must be lifted to these coordinates via the `Dγ` and `χD0` response functions defined in [Docs/PhotonBridge.md](/home/c/Documents/code/dashi_agda/Docs/PhotonBridge.md) and [Docs/CharmPhotoproduction.md](/home/c/Documents/code/dashi_agda/Docs/CharmPhotoproduction.md).

## Agreement/deviation/new-structure criteria
- **Agreement**: the MDL-inferred `g⋆` lies within the model uncertainty band for `Q_s^2` (or equivalent variable) at the projected `x`. Equivalently, the Dashi prediction `Y_D0(g⋆)` matches the model-predicted `Y_model(Q_s^2)` to within `O(λ)` in log-likelihood.
- **Deviation**: the residual `ΔY = Y_D0(g⋆) − Y_model(Q_s^2)` cannot be absorbed by the MDL penalty `λ L(g)` without raising the description length by a significant fraction. In that case the polynomial tail of the MDL cost signals a new structure.
- **New structure**: a systematic trend in `ΔY` across photon energies or nuclear sizes indicates that the current model lacks a scale or channel. This motivates adding either a higher-twist correction, a new `x`-dependence in `χD0`, or a modification of the saturation kernel. Dashi formally registers that as a change in the residual distribution `η`, not a change in the core projection `P x`.

## Summary
This numerical layer is strictly a mapping from Dashi observables to saturation-scale variables plus a set of comparison criteria. It never claims to derive the QED flux, perturbative cross-sections, or detector systematics. Instead it says: **if** you commit to a particular saturation model (GBW, IPsat, rcBK, etc.), then `g⋆` provides the coarse-grained saturation scale, and `Y_D0` gives you a trustworthy residual whose deviations flag when the model needs extension. With this layer in place, the next step is to attach the actual CMS data or targeted fits while leaving Dashi’s core measurement geometry untouched.

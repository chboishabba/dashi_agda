## Dashi Numeric Observable Interface for Photonuclear Prototype

This note names the minimal state-derived observables that feed the surrogate GBW-style response layer. Each variable is defined on the Dashi defect/Δ channel and exposes only the information needed for the reduced collider proxy. External physics elements (equivalent-photon flux, γ+A→D0+X cross-section, dataset-specific rates) are explicitly left outside this interface.

1. **Defect-channel intensity (`I_defect`)** — the norm or energy of the residual vector `Δx := x_{t+1}-x_t` after projecting into the coarse shell. This abstracts the near-miss photon halo: a larger `I_defect` indicates a stronger photon field available for interaction. Computed purely from the Dashi state geometry, no Standard Model inputs are required.

2. **Promoted observable (`Y_promote`)** — a scalar proxy for the `D0` yield extracted from the defect channel. For now it is defined as a weighted sum of the `ShiftConeCompatible` coordinates (e.g., the tau component and aligned spatial moments) with MDL-based selection weights. The goal is to produce a low-entropy signal analogous to the measured charm meson yield.

3. **Density proxy (`g_star`)** — the inferred gluon-density variable, computed by minimizing the Dashi MDL functional over equivalence classes that share the same projected observable. One practical instantiation is `g_star := argmin_g [L(current_state)+λ·(Y_promote - f_model(g))^2]` where `f_model` will later be provided by the saturation layer. For the interface, simply expose `g_star` as the current best guess of the latent density.

4. **Saturation-scale proxy (`Q_s`)** — an optional parameter representing the effective transverse momentum scale at which nonlinear gluon recombination becomes important. Derived from `g_star` via `Q_s := (g_star)^α` with a tunable exponent `α`, this stays symbolic until the model layer provides a concrete mapping. Treating it as part of the interface keeps the bridge flexible.

Each of these variables is computed in the numerical prototype without calling
heavy physics libraries: they rely exclusively on the existing Dashi
projection/MDL stack. The current prototype examples should be emitted from the
canonical `1+3` shift path and its admissible perturbations, so the numerical
surface stays tethered to
`DASHI/Geometry/ShiftLorentzEmergenceInstance.agda::canonicalShiftStateWitness`
and `ShiftInBasin` rather than to freehand fixtures. External physics enters
only in the next layer (`Docs/SaturationLayer.md`), which will interpret
`g_star` and `Q_s` via a GBW-like response, and in later stages when real data
is compared.

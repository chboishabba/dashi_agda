## Charm photoproduction observable map

### Objective
Build on the equivalent-photon bridge: gamma + A → D0 + X is the promoted observable that Dashi already recognizes as living on a defect / near-miss channel. This note states what Dashi supplies (measurement geometry, projected observable, inverse problem) and what must be supplied by external QCD physics (hard scattering and charm cross-sections).

### Dashi side
- **Measurement geometry**: the near-miss channel lives in the projection defect `D x = x − P x`. The equivalent-photon map turns that defect into an effective photon probe `Dγ`, which is the carrier of the promoted observable.
- **Promoted observable**: define
  ```
  O_D0(Dx, χD0) := ⟨Dγ(Dx), χD0⟩
  ```
  where `Dγ` is the defect-to-photon map (from [Docs/PhotonBridge.md](/home/c/Documents/code/dashi_agda/Docs/PhotonBridge.md)) and `χD0` abstracts the detector response to charm quark fragmentation. This keeps the observable in the low-entropy allowable channel.
- **Inverse problem**: inference minimizes description length:
  ```
  g⋆ = argmin_g [−log p(Y_D0 | g) + λ L(g)]
  ```
  where `Y_D0 := O_D0(Dx, χD0) + η` and `g` parametrizes the gluon-density observable that drives `χD0`.

### QCD side
- The hard process `γ + A → D0 + X` remains a perturbative QCD calculation. The Dashi note only uses it to justify the choice of `χD0` and the likelihood `p(Y_D0 | g)`. It does not attempt to derive the matrix element, only to acknowledge that it supplies:
  * the equivalent-photon flux that weights the photon probe
  * the charm photoproduction cross-section that relates photon energy to D0 yield
  * the branching fractions that tell us when a produced charm quark becomes a measurable D0 meson

### Separation of roles
- Dashi: defect geometry (`D x`), promoted observable (`O_D0`), inverse-problem inference (`g⋆`). This is entirely structural and independent of the specific field-theory parameters.
- QCD/experiment: flux, matrix elements, saturation models, detector acceptance. These populate `χD0` and `p(Y_D0 | g)` but are not derived from Dashi.

### Next steps
With this observable map noted, the next lanes can attach explicit flux models (step 2) and saturation numerics (step 3) while keeping the Dashi core unchanged.

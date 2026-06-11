## Equivalent-photon bridge

### Intention
Dashi already understands that the observable content of a system is the projection-invariant part of the state plus the low-entropy residual deltas that survive contraction and MDL descent. The equivalent-photon result in collider physics is the same structural idea: the useful signal is not the head-on collision (the high-entropy event) but the defect / halo interaction between a photon cloud and a nucleus.

### Object-level map
- Let `x` denote the full collider state. Dashi decomposes it as `x = P x + D x`, where `P x` is the coarse projected part and `D x` is the defect or near-miss channel. The measurement geometry identifies `D x` as the meaningful observable direction.
- In the equivalent-photon language, the near-miss photonuclear event is the projectile `P`.
  creation from the defect field `D`, while the direct collision is the coarse `P x` part.

### Observable map
- Define an observable `O_photon` on the defect channel:
  ```
  O_photon(Dx, χn) := ⟨Dx, χn⟩
  ```
  where `χn` is a target response of the nucleus (gluon density) and `Dx = x − P x`. This bilinear form is the Dashi-side equivalent of “a photon scraping the target”.
- The promoted measurable quantity is then
  ```
  Y_photon := O_photon(Dx, χn) + η
  ```
  with noise `η` capturing the rest of the collision background. This is structurally identical to the Dashi measurement `Y = P(x) + η` except we explicitly restrict to the defect channel `D x`.

### Inference
- Dashi enforces MDL descent `L(T x) ≤ L(x)` and contraction `d(T x, T y) < d(x, y)`, which ensures `D x` stays concentrated in the boundary channel even as the bulk state changes.
- The equivalent-photon inference is:
  ```
  g⋆ = argmin_g [−log p(Y_photon | g) + λ L(g)]
  ```
  where `g` parametrizes the gluon-density observable that enters `χn`. This is just the Dashi inverse-problem pattern: find the minimum-MDL latent that best explains the promoted observable on the defect channel.

### Scope
- This note does not derive the QED equivalent-photon flux, perturbative QCD cross-sections, gluon saturation numerics, or reproduce the specific CMS measurement. Those remain outside Dashi’s current formalism.
- Instead, it identifies the bridge:
  - Dashi defect channel ↔ photon halo
  - clean promoted probe ↔ `D0` meson yield
  - MDL inverse problem ↔ inferring gluon density from the photon observable

With this bridge in place, one can later layer on the physical flux models, cross-sections, and experimental pipeline without changing Dashi’s core measurement-theoretic statements.

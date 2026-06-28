# NS Triad K_N Cross-Shell Signed Domination

> **Status:** Proof target fixed. This is the live Gate 1 theorem surface.
> No promotion claim made.

---

## Definition

On the seam block \(C = \{\text{shells } N-1, N\}\), write

\[
S_C = L_{\mathrm{good}} - L_{\mathrm{bad}}
\]

with \(S_C \mathbf{1}_C = 0\) and the live coercivity question posed on
\(\mathbf{1}_C^\perp\).

Define the signed domination ratio

\[
\rho_N
=
\sup_{x \perp \mathbf{1}_C}
\frac{x^\top L_{\mathrm{bad}} x}
     {x^\top L_{\mathrm{good}} x}.
\]

---

## Observed

- \(\rho_6 \approx 0.6076\)
- \(\rho_8 \approx 0.6257\)
- \(\rho_{10} \approx 0.6144\) via projected CPU matrix-free generalized eigensolve
- \(\rho_{12} \approx 0.6577\) via projected CPU matrix-free generalized eigensolve
- \(\rho_{14} \approx 0.5956\) via projected CPU matrix-free generalized eigensolve
- \(\rho_{16} \approx 0.5812\) via projected CPU matrix-free generalized eigensolve
- \(S_C\) is PSD with nullity one at \(N=6,8,10,12,14,16\) in the current audits
- \(S_C \mathbf{1}_C = 0\) is proved analytically and machine-zero numerically
- All currently tested domination ratios remain below \(2/3\), with the present worst case at \(N=12\)
- The current worst generalized eigenvectors are concentrated on the seam shells \(N-1\) and \(N\), carry negligible axis mass, and are led by non-axis modes such as \((-1,0,N-1)\); \(N=16\) follows the same pattern
- The focused \(N=12\) symmetry audit reproduces a tight ratio below \(2/3\) and shows the extremizer is overwhelmingly non-axis, with about \(86\%\) of its mass on the `0-zero` coordinate-permutation sector and leading orbit classes \((1,7,12)\) and \((0,1,11)\)
- In that same \(N=12\) audit, the shell-only restricted components sit near \(0.575\), while the mixed seam block \(11 \leftrightarrow 12\) still rises to about \(0.702\); this supports a full mixed-shell cancellation theorem rather than per-source or per-shell domination
- The comparative \(N=10,12,14,16\) sector/frame audit shows that the full ratio is already essentially the non-axis ratio at every tested shell, while the `0-zero` restricted component stays much milder (about \(0.50\text{–}0.58\)); the dangerous local piece is still the mixed seam, peaking at \(N=12\)
- Across those same shells, the orbit family \((0,1,N-1)\) persists, but the competing high-mass non-axis family is empirically \((1,7,N)\), not a clean \((1,N-5,N)\) law; this makes \(N=12\) look like the tightest finite resonance rather than evidence for that simpler orbit formula
- The new angular/frame diagnostics do show some pair-mass near dot products \(-1/2\), \(0\), and \(+1/2\), but not a sharp collapse to a single equilateral signature; the observed top-mode frame remains anisotropic, so the safe proof target is still a full mixed-shell compensation theorem, not an incompressibility-only or single-orbit frame shortcut
- A first restricted-sector localization test at \(N=12\), using only the non-axis orbit layer \((0,1,11)\cup(1,7,12)\), fails decisively as a proof sector: the restricted ratio jumps to about \(7.03\) and its overlap with the full extremizer is only about \(0.057\). So those leading orbits are anatomical clues, not a closed theorem sector by themselves
- A first halo-growth audit at \(N=12\) shows why that seed fails structurally: radius \(0\) is the same unstable two-orbit core, but radius \(1\) under Schur-support adjacency already jumps to a sector of dimension \(6352\) with \(\rho_{\mathrm{sector}}/\rho_{\mathrm{full}} \approx 1.001\) and projected overlap about \(0.997\). So the compensating halo is real, but it is not a tiny local ornament around the seed; at the current support threshold it is essentially the full non-axis seam
- A first coarse-quotient audit at \(N=12\), compressing the full non-axis seam to class-indicator coordinates, also fails to preserve the dangerous direction. The basic `shell-zero-orbit` quotient uses \(167\) classes but only reaches \(\rho_{\mathrm{quotient}} \approx 0.433\), with \(\rho_{\mathrm{quotient}}/\rho_{\mathrm{full}} \approx 0.657\) and lifted overlap only about \(0.071\)
- A richer `shell-zero-orbit-parity` quotient still does not localize the proof mechanism: even with \(334\) classes it only reaches \(\rho_{\mathrm{quotient}} \approx 0.507\), with \(\rho_{\mathrm{quotient}}/\rho_{\mathrm{full}} \approx 0.769\) and overlap about \(0.122\). So the live compensation mechanism is not captured by this first class-indicator quotient either
- Ordinary Laplacian reduction is dead: positive off-diagonals occur in the dense sign audit
- The “balanced signed graph” framing is demoted: it is not the active theorem route

---

## Target Theorem

\[
\boxed{
\exists \rho_* < 1 \text{ such that } \rho_N \le \rho_* \text{ uniformly in } N.
}
\]

Equivalently, for every \(x \perp \mathbf{1}_C\),

\[
x^\top S_C x
=
x^\top L_{\mathrm{good}} x - x^\top L_{\mathrm{bad}} x
\ge
(1-\rho_*) x^\top L_{\mathrm{good}} x
\ge 0.
\]

This is now the single live Gate 1 proof obligation.

The highest-alpha next cut is therefore not “prove the two leading orbits.” It is to enlarge the restricted sector until it carries the compensating good mass that the full Schur form forces in the dangerous mixed-shell direction.

The new halo-growth result sharpens that further: the first support-neighbourhood is already nearly everything. The new coarse-quotient result sharpens it again from the other side: a naive class-indicator compression throws away too much of the dangerous direction. So the next reduction should not be “one more hand-picked orbit family,” but it also should not be the first coarse quotient basis tried here. It needs a more faithful global compensation closure, likely a shell-pair or representation-sector compression that preserves the full non-axis seam coupling.

A direct row-pairing audit at `N=12` rules out the simplest rowwise proof bridge while preserving the stronger global `Q` picture. For `Q = 2L_good - 3L_bad`, the projected bottom eigenvalue is still positive (`lambda_min(Q|1_C^⊥) ≈ 1.11e-4`), but the naive row ratios are badly above one (`max_i 3 bad_i / 2 good_i ≈ 1.614`, mean `≈ 1.461`, with `6172/6364` rows above `1`). The extremizer-weighted row ratio is also above one (`≈ 1.489`). So the implication “rowwise pairing closes Gate 1” is dead in its naive form: `Q` remains PSD on `1_C^⊥`, but not because rows are individually dominated. The compensation mechanism is therefore genuinely quadratic/global, not a per-row or per-edge Schur test.

Waleffe helical decomposition is now the best candidate representation lens for the live `Q` theorem, but it remains fail-closed. The current DASHI operator still comes from the phase-based Schur sign split `γ_e = cos(φ_l + φ_r - φ_o)`, not from an explicit helical Waleffe coefficient, so `Q_N` is not yet identified with a helical triad operator. The safe next audit is therefore: build a candidate canonical helical-channel lift of the current phase-based `Q_N`, measure off-block leakage in that lifted basis, and only then decide whether a genuine helical block proof route is live.

The first `N=12` helical coupling certificate is materially better than an opaque global PSD observation, but it is still only a finite-shell certificate. In the candidate lifted basis, write

\[
Q_N = D_N + E_N
\]

where \(D_N\) is the helical block-diagonal part and \(E_N\) is the off-block coupling. The current `N=12` telemetry reports

- \(\lambda_{\min}(D_{12}\mid \mathbf{1}_C^\perp) \approx 4.375958\times 10^{-6}\)
- \(\lambda_{\min}(Q_{12}\mid \mathbf{1}_C^\perp) \approx 4.320716\times 10^{-6}\)
- \(\|E_{12}\|_{\mathrm{op}} \approx 1.083606\times 10^{-2}\)
- \(\|D_{12}^{-1/2} E_{12} D_{12}^{-1/2}\| \approx 0.595611 < 1\)

Thus, if the relative-bound computation is correct,

\[
Q_{12} \succeq (1 - 0.595611)D_{12}
\]

on the tested mean-zero seam surface. This is a useful structural certificate, not a uniform theorem. The conservative perturbation lower bound is about \(1.77\times 10^{-6}\), below the observed \(4.32\times 10^{-6}\), so the bound is lossy but non-vacuous.

The new proof target is:

\[
Q_N = D_N + E_N,\qquad
D_N \succeq c_D(N)I,\qquad
\|D_N^{-1/2}E_ND_N^{-1/2}\|\le \kappa_* < 1
\]

uniformly in \(N\). Gate 1 therefore reduces to two obligations: a helical block floor and a helical coupling bound. The decisive finite audit is the same report for `N = 6, 8, 10, 14, 16`: \(\lambda_{\min}(D_N)\), \(\lambda_{\min}(Q_N)\), \(\kappa_N\), \((1-\kappa_N)\lambda_{\min}(D_N)\), actual/bound ratio, off-block Frobenius ratio, and the dominant sector-pair of \(E_N\).

Because the existing CPU runner can OOM while materializing dense Schur/Q objects, the recommended compute path is now checkpoint-first and overlay-only: produce one shell-scoped `.core.npz`/`.matrices.npz` checkpoint at a time, then run helical overlays from the checkpoint. GPU/Vulkan reuse from `../dashiCORE` is a performance scout only until CPU parity is recorded; it must not become proof authority.

The repo-side implementation target is correspondingly narrow. `../dashiCORE` already supplies the Vulkan substrate, and this repo already has a reusable edge-Laplacian executor in [scripts/gpu_vulkan_triad_laplacian.py](/home/c/Documents/code/dashi_agda/scripts/gpu_vulkan_triad_laplacian.py:1). The missing layer is the Schur/helical adapter: map the Schur sign split into parity-checked `x ↦ L_good x`, `x ↦ L_bad x`, then later `x ↦ Qx`, `x ↦ Dx`, `x ↦ Ex`, without turning GPU scouting into proof authority. The restricted-sector audit now exposes a non-authoritative `vulkan-scout` backend for exactly that bridge.

---

## Consequence

If the uniform bound holds, then:

- \(S_C \succeq 0\) on \(\mathbf{1}_C^\perp\)
- \(\ker S_C = \operatorname{span}\{\mathbf{1}_C\}\)
- the Gate 1 block floor follows through the Schur complement route

---

## Receipt Boundary

```text
schurSignedPsdRequired = true
signedDominationProbeInstalled = true
signedDominationRatioBelowOneObserved = true
schurComplementPsdVerified = true
qHelicalLiftAuditInstalled = true
qHelicalBasisRelevantObserved = true
qHelicalBlockDiagonalizationObserved = false
qHelicalCouplingBoundObserved = true   -- N=12, kappa approx 0.5956

signedDominationRatioUniformlyBounded = false
qHelicalCouplingUniformlyBounded = false
qHelicalBlockFloorUniformlyProved = false
schurSignedFactorizationProved = false
schurComplementPsdProved = false
gate1ConditionalTheoremProved = false

ordinaryKronLaplacianRoute = false
balancedSignedGraphRoute = false

gpuSchurMatvecInstalled = true
gpuCpuParityObserved = false
gpuHelicalCouplingScout = false
gpuKnAuthority = false
```

---

## Agda Status

```text
Python regression: passed
Matrix-free audit: passed
Dense sign/factorization audit: passed
Focused Agda check: passed
Full Everything.agda check: attempted, killed exit 137
Promotion check: not yet run
```

Exit `137` is an environment/resource failure, not a proof failure.

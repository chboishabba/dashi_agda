# MMP S² fermion stress / three separately driven plasma regions — 2026-10-24 max-cut

## Status, attribution and no-promotion policy

This is a **scoped source-first calculation**, not a new traversable-wormhole discovery. Original mathematical and physical foundations remain attributed to their authors: Maldacena–Milekhin–Popov (MMP), arXiv:1807.04726, *Classical and Quantum Gravity* **40** (2023) 155016, DOI 10.1088/1361-6382/acde30, constructed the magnetically charged fermionic-Casimir wormhole; standard spin-c sphere Dirac spectral/index theory gives the transverse zero modes and towers; Polyakov/anomaly and Schwinger response are classical 2D QFT results. Sadhukhan's arXiv:2609.33511 (2026-09-27) and arXiv:2610.09847 (2026-10-07) cover complementary first-order fermion anomaly, Hall and Schwinger/polarization responses in the MMP background. Do **not** promote their first-order l≥2 mode results to full nonlinear stability.

Published mathematical existence, authored theorem, finite computational fixture, same-object bridge, kernel-certified theorem, calibrated experiment and a working device are **different evidentiary levels**.

## Reused repo owners, not reinvented

- PR #1165: `CasimirBrownMaclayEnergyConditionExact`, `CasimirGRNullFocusingBridgeExact`, selected QFT stress and Casimir source-native outstanding same-object obligations. Plate stress is NOT automatically spherical Dirac stress.
- PR #1163: `QuantumStressEnergyEngineeringBridgeExact`, `QuantumStressEnergySourceWeldExact`. Strict separation of source-level QFT, QEI, controllability, gravitational magnitude and warp/wormhole capability.
- PR #701: `ZeroPointModeHyperfabricExact` and canonical Casimir mode/renormalisation machinery.
- PR #1215: `CMP119ClassicalCurvatureSpatialC3CovarianceExact` and actual side-four C3 SU2 field covariance. A spatial C3 theorem is not a physical plasma Floquet stress.
- PR #1239: twelve-step three-strand braid; `docs/c3-puncture-pin-monodromy-kk-maxcut-20261023.md` shows its actual strands hit the selected central puncture. Puncture, Pin/Spin, physical magnetic monopole flux and KK horizontal connection require separate identified carrier maps.
- PR #1241: physical KK/radion source and stabilization, including model-specific unbroken-U1 obstruction. Optional donor only; no automatic KK completion.
- PRs #1120/#1045: superconducting source-vs-constitutive gravitational response, historical anomaly/null-replication provenance, and conditional antigravity theorem.

No sibling branch is assumed merged merely because its files have been inspected.

## Calculated physical reduction

Assume an actual magnetically charged background `F_{theta phi}=Q sin(theta)`. For fermion charge e, its **spherical index** is `q=2eQ ∈ Z` (normalisation fixed by `e/(2pi) integral F`). A generic plasma ball without magnetic monopoles has zero net magnetic flux through its enclosing sphere; three rotating dipoles or 2D AB holonomies do NOT imply q≠0.

For a conventional round spin-c S² Dirac operator, the chiral zero-sector has `|q|` modes. Nonzero eigenvalues are `±sqrt(n(n+|q|))/r`, n≥1, with `|q|+2n` states per sign. This calculation uses the established spectrum and a **truncated adiabatic** nonzero-mode NS-circle Casimir energy, not the complete curved 4D determinant.

For the local effective potential from the finite massive tower, `W_KK = - integral sqrt(-h) V_KK(r)`, derive stress from **the same variation**:
- `rho4=V_KK/(4pi r²)`
- `pr4=-V_KK/(4pi r²)`
- `pt4=-V_KK'(r)/(8pi r)`.

This KK local-potential sector alone saturates radial NEC; the massless LLL/Polyakov state supplies candidate negative radial null energy. In spherical proper-radial geometry `ds²=-N²dt²+dx²+r²dOmega²`, with the standard Polyakov state and radial Maxwell field, the Einstein radial constraint

`C=r'²-1+2rr'Phi'+Q²/r²-2(P_Polyakov-V_KK)`

obeys exactly `C'=-Phi' C` when the sourced tt/theta equations are used. The 4D Ward conservation relation also closes by the derived transverse pressure. See committed symbolic acceptance script `scripts/check_mmp_s2_fermion_source_weld_20261024.py`.

## Independently executed local numerical extension — bounded model, not repository CI

A companion local Python study used `e=1`, NS state `t=-pi*|q|/(12L²)`, L=20, finite n≤4 spectral tower and solved the throat constraint with `Q=q/2`.

| q | symmetric throat a | r''(0) | interpretation |
|---:|---:|---:|---|
| 3 | 1.505925 | -0.01855394 | not a flaring throat |
| 12 | 6.096519 | +0.00382519 | local flaring throat; finite x≤45 constraint residual ≈9.4e-12 |
| 24 | 12.394416 | +0.00477549 | local flaring throat; finite x≤45 constraint residual ≈5.5e-12 |

At q=12,24 the radial effective pressure crosses zero at approximately x=33.12,41.67, respectively. This is at most a necessary **radial-extrinsic-curvature** matching indicator for a source-free RN exterior; it is NOT completion of global fermion state transition or smooth physical mouth matching. The quantum mode state and its transverse response do not automatically cease at those points. A 15-case q∈{10,11,12,13,24}, L∈{18,20,22} sweep yields local positive flaring for all listed cases. Thus **no special 12/24 numerological effect** is supported by these model equations.

Further local finite Wilson-Dirac Hamiltonian calculations show explicit local U(1) gauge covariance to ≈1e-15, gauge-invariant spectrum to ≈2e-15, and discrete static persistent-current continuity to ≈7e-10. The link-current and radius-response both derive from the **same finite regulated sea**; neither a renormalized 4D quantum state nor the dynamic Hall/Wen–Zee or Schwinger polarization current is thereby constructed.

## Three plasma balls are not a rotating disk

Use three separately time-dependent electromagnetic/plasma field regions `(E_i(x,t),B_i(x,t))`, potentially with internal field rotation, changing boundaries and mutual coupling. A minimal three-site driven Hermitian Floquet toy verifies combined C3 permutation/time-shift covariance and unitary monodromy, but supplies **no** quantum gravity source. Spatial permutation C3 need not be preserved at each instant if only spatiotemporal symmetry is present.

For three excluded 3D balls, H1(exterior)=0, H2(exterior)=Z³; for a punctured 2D cross-section, H1=Z³ and AB loop phases may be nonzero. With Maxwell div B=0 and no monopoles, each enclosing 3D sphere carries zero magnetic flux. Cross-section winding, C3 modes, Pin lift, and actual q-index on S² are different consumers. The repository 12-step braid actually hits its centre puncture; a physical spin/framing interpretation requires new clearance and bundle-identification proofs.

The user's 12/24 prior art includes the actual 12-step braid and other finite mathematics such as ternary length-12/binary length-24 Golay objects. No theorem identifies these numbers with monopole charge, LLL multiplicity, or a physical number of plasma modes. Do not substitute numerology for physical state construction.

## What still has to be proved / implemented

1. A **single covariantly renormalized curved-space charged-fermion generating functional** `W_ren[g_ab,r,A_ab; spin structure, state, flux]`, not a stitched finite NS potential plus separately asserted Schwinger and Hall terms.
2. Variations of that *same* W with respect to the 2D metric, spherical radius and both gauge sectors, including dilaton/spin-connection, trace anomaly, induced transverse Hall current and time-dependent polarization; gauge, diffeo and Bianchi Ward identities must close with no missing source.
3. Full nonlinear Einstein–Maxwell–fermion boundary-value solve through throat and **two physical magnetic mouths**, with charge quantization and verified C1 matching/no undeclared shells, quantum state transition and asymptotic conserved observables.
4. Mode convergence, QEI, stability and transmission from the **same** physical solution; transient driven-plasma boundary conditions rather than ideal stationary plates or a rotating disk.
5. Only then consider whether C3/Floquet/Pin/puncture and optional KK lift provide a physically derived coupling or a distinct experimental discriminator.

## Acceptance / provenance

Run `python3 scripts/check_mmp_s2_fermion_source_weld_20261024.py` to check the symbolic finite-spectrum / Ward / Einstein-constraint assertions. Code has been committed as *source-written*, not certified by a GitHub workflow. Separate local scripts and numerical JSON receipts are supplied in the chat and are not claimed as repository CI or Agda kernel receipts. No empirical evidence of a plasma-ball gravitational device or MH370 teleportation follows from these mathematical models.

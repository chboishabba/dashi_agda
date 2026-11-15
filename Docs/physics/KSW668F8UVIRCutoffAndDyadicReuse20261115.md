# KSW668 F8 ultraviolet / infrared maximum cut — original compact tensor source, exact dyadic reuse, two independent numerical scales

**Date:** 2026-11-15. **Owner:** current single Agda PR #1512. **Original model:** 5D Poincaré AdS5 with moving \(a(t)=t,\ z_b=1/t\) brane, \(n\cdot\partial H=-6\pi^{TT}\). **Do not substitute:** stationary RS2, scalar control, plane-infinite-transverse-energy source, or an unrelated Yang–Mills UV fixed point.

## Existing DASHI prior art — exact categorization

- \`DASHI/Physics/YangMills/BalabanClayDyadicCutoffTailExact.agda\` genuinely proves \`finiteDistanceBelowDoubleDyadic\`: if an adjacent scale increment is bounded by \(C\,2^{-j}\) in an ordered metric, a finite interval from \(j\) to \(j+n\) has distance \(\le 2C\,2^{-j}\). This is **true finite algebra**, with a **conditional physical adjacent-scale estimate**. **KSW adapter:** \`DASHI/Physics/Gravity/KSW668AdS5UVIRDyadicTailReuseExact.agda\`; imported into \`KSW668BraneBulkMaxCutEverything.agda\`. The source and receiver are **not** automatically instances of the same Yang–Mills physical operator.
- \`NSSprint106LittlewoodPaleyShellProjector.agda\`, \`NSSprint107SmoothDyadicCutoffPartition.agda\`, \`NSSprint108RadialBumpFunctionConstruction.agda\`, \`NSSprint109SmoothCompactSupportWitness.agda\` contain valuable typed decomposition interfaces but explicitly set the downstream analytic closure flags to **false**. Do not mark that physical smooth projector partition proved merely because the ledgers exist.
- \`BalabanClaySpectralUVCompatibilityExact.agda\` distinguishes an IR spectral support claim from a UV RG asymptotic using conditional data records. Its **YM mass-gap claims do not imply** a gap for the original AdS5 radial zero mode or its linear TT source.
- Previous frozen high-Laplace Neumann contraction and causal depth-two inverse are two **different inversions**, neither by itself the 3D UV/IR source-to-Weyl transfer estimate.

## F8-UV1 — the SAME C-infinity compact spatial profile as the actual solver

Take \(\varphi_\epsilon(\mathbf x)\) nonnegative radial, supported on \(|\mathbf x|<\epsilon\), normalized to \(\int_{\mathbb R^3}\varphi_\epsilon=1\), with the existing solver's exact shape
\[
\varphi_\epsilon(r)\propto \exp[-1/(1-(r/\epsilon)^2)]\ \text{for }r<\epsilon,\quad0\text{ otherwise}.
\]
Its real isotropic spatial Fourier transform with \(u=\epsilon |\mathbf k|\) is
\[
\widehat\varphi_\epsilon(k)=
\frac{\int_0^1 dr\,r^2e^{-1/(1-r^2)}\,\operatorname{sinc}(ur)}
{\int_0^1 dr\,r^2e^{-1/(1-r^2)}} ,\quad \operatorname{sinc}(z)=\sin z/z .
\]
Nonnegative normalized bump implies \(\widehat\varphi_\epsilon(0)=1\) and \(|\widehat\varphi_\epsilon(k)|\le1\) for every real \(k\). The exact *local* compact fourth-order spatial TT source generator \(PQP-\frac12P\operatorname{tr}(PQ)\) has homogeneous polynomial degree 4 and a nonzero angular polarization on the original x-directed lens ray.

The **physical mathematical source** \(\pi^{TT}\) therefore has \(L^2\) momentum radial weight \(u^{10}|\widehat\varphi(u)|^2\) (up to an angular constant and a common \(\epsilon\)-power). Applying *two more spatial derivatives* to this source has \(u^{14}|\widehat\varphi(u)|^2\). This is a **Weyl-sensitivity SOURCE diagnostic**, not a bound on the actual propagated Weyl field. Neither time derivatives nor receiver boundary trace estimates have been assumed away.

**Exact infrared result:** for \(q=10,14\),
\[
\boxed{\int_0^Uu^q|\widehat\varphi(u)|^2du\le\frac{U^{q+1}}{q+1}.}
\]
The original compact TT source suppresses the \(\mathbf k=0\) mode as \(O(|k|^4)\), and the infrared integrated weights scale at most like \(U^{11}\) and \(U^{15}\). This **does not remove** the stationary radial gravitational zero-mode at general spatial \(k\), which is a different use of “zero mode.”

**Exact ultraviolet source tail existence:** since \(\varphi_\epsilon\in C_c^\infty(\mathbb R^3)\), \(\widehat\varphi_\epsilon\) is Schwartz. Consequently, for any integer \(m>0\) and either \(q\),
\[
\boxed{\int_U^\infty u^q|\widehat\varphi|^2du
\le U^{-2m}\int_0^\infty u^{q+2m}|\widehat\varphi|^2du<\infty.}
\]
This is a rigorous SOURCE convergence theorem for \(U\to\infty\), but the multiplier on the right depends on the physical compact bump and its width; it is not a *uniform* or *quantitatively calibrated* Weyl-receiver estimate.

## F8-UV2 — concrete independent cutoff audit for actual F8 3D implementation

Existing F8 code \`scripts/ksw668_f8_moving_maxcut.py\` uses \(\epsilon=0.024,L=4\) and 3-grid \(N_x=256,512,768\), so \(u_{\max}=\epsilon \pi N_x/L\) is \([4.825486,9.650973,14.476459]\).

Because the full positive moment \(M_q(0,\infty)\) dominates \(M_q(0,100)\), we can *upper-bound the fraction of the full source norm captured* by the easily reproducible numerical ratio \(M_q(0,u_{\max})/M_q(0,100)\), provided quadrature is reliable.

| \(N_x\) | \(u_{\max}\) | TT source \(q=10\) captured fraction **upper bound** | Six-derivative proxy \(q=14\) captured fraction **upper bound** |
| ---: | ---: | ---: | ---: |
| 256 | 4.825486 | 0.000108931 | 0.000000002296 |
| 512 | 9.650973 | 0.002552649 | 0.000000831262 |
| 768 | 14.476459 | 0.010883195 | 0.000013432848 |

These are numerical **source** bounds, not rigorously interval-certified integrals. They use the exact original \(C^\infty\) bump shape and positive radial weight. The 192- vs 384-node Gauss–Legendre source transforms and 5001-point Simpson moment integrals agree in reported captured fractions within \(1.7\times10^{-15}\) for \(q=10\), and \(1.1\times10^{-17}\) for \(q=14\). The original 96-node source radial quadrature agrees with 384 nodes to floating-point noise at tested u values up to 100, so the dominant issue is **not** simply bump radial quadrature order.

At \(N_x=768\), at least **98.91%** of the full \(L^2\)-weighted TT-source spectral norm and **99.9986%** of the extra-two-spatial-derivative norm remain above the mesh cutoff, to the source quadrature's accuracy. These are conservative: a larger full-band denominator only lowers the fraction captured.

**Consequence:** the previously observed F8 compact-3D fine-to-medium field drift (48.4%), curvature drift (83.0%) and beyond-cone leakage cannot support receiver convergence with this mesh. This is now an independently reproduced UV under-resolution cause, not a new physical effect.

## F8-IR1 — *independent* wavenumber-spacing obstruction

The current Fourier grid has
\[
k_{\max}=\pi N_x/L,\qquad \Delta k=2\pi/L.
\]
At fixed \(L\), increasing \(N_x\) raises the UV cutoff but DOES NOT reduce the momentum spacing. The 3D angular-Bessel inversion at receiver \(r=1.8220210521210103\) has large-\(kr\) oscillatory phase step
\[
\Delta(kr)=\Delta k\,r=2.8620239760146555,
\]
only \(2.19536\) samples per full oscillation. This is a distinct *IR / quadrature-density* problem from the UV missing source norm.

To **illustrate** a uniform-grid dual-scale specification \(u_{\max}\ge100\), \(\Delta(kr)\le0.25\), one would need \(L\ge45.79238\) and an even \(N_x\ge60736\). These are *selected design criteria*, **NOT universal theorems that no lower-cost method can work**; adaptive oscillatory k quadrature is the appropriate next choice.

The exact \(\Delta k\) and \(k_{\max}\) constraints are in \`scripts/ksw668_f8_uvir_sampling_contract.py\` and its 12 local tests. \`scripts/ksw668_f8_uvir_source_cutoff.py\` and 13 tests independently audit the original bump, positive radial spectral moments, scale shells, quadrature stability and fail-closed physical promotion. Their combined **25/25 new source-equivalent local tests pass**.

## F8.3 updated exact remaining primitives and acceptance

1. \`ads5OriginalCompactTTSourceUVIRMomentAndShellContract\` — **math/source numerical diagnostic DONE**: correct original bump, IR inequality, Schwartz source UV tail, dyadic finite reusable algebra, independent 25 tests. **Agda continuum and rigorous numerical interval certificates still OPEN.**
2. \`ads5OriginalTTSourceAdjacentCutoffSobolevBound\` — **analytic source-only inequality available** as above; supply an explicitly normalized Sobolev constant for \(\epsilon=.024\) and the relevant source derivatives, and a physically faithful dyadic shell instance in Agda.
3. \`ads5OriginalMovingWeylSourceToReceiverSobolevTraceEstimate\` — **OPEN**: control normal/tangential boundary trace and two Weyl derivatives under *actual original moving* PDE, uniformly in spectral cutoff; this is the essential weld before one can transfer a source UV budget to the receiver.
4. \`ads5OriginalMovingTTAdaptiveKAndRadialPDEConvergence\` — **OPEN**: decouple \(\Delta k\) from \(k_{\max}\) using adaptive/oscillatory k integration and tested 1D radial propagators per band; independent \((k_{\max},\Delta k,\Delta y,\Delta T)\) refinements and outside-cone controls; an explicit error estimate rather than arbitrary threshold.
5. \`ads5MovingTTCompact3DSpectralCutoffConvergence\` — **OPEN** full compact 3D source→both Weyl receiver converged physical geometry; current \`--full\` expected to fail, not promoted by the source-only UVIR analysis.
6. \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` — **INDEPENDENT MATHEMATICAL AUDIT OPEN** of original prescribed-source theorem-application proof, with correct moving boundary phase, cutoff and residual. The compact high-frequency prepared packet route is complementary to full numerical convergence.
7. Beyond F8: F9 physical matter-generating action and coupled stability/cylinder, F10 calibrated scales, F11 Agda 2.9 kernel and semantic detector weld, D1 independent experiment remain **OPEN**. No 5D superluminality/free-energy promotion.

**Commands:**
\`\`\`bash
python3 scripts/test_ksw668_f8_uvir_source_cutoff.py
python3 scripts/ksw668_f8_uvir_source_cutoff.py
python3 scripts/test_ksw668_f8_uvir_sampling_contract.py
python3 scripts/ksw668_f8_uvir_sampling_contract.py
bash scripts/check_ksw668_f8_maxcut.sh --smoke
bash scripts/check_ksw668_f8_maxcut.sh --full  # still expected exit 42
\`\`\`

**Acceptance provenance:** 25/25 source-equivalent new UVIR tests independently run; the earlier 68/68 F8 checks remain as previously accepted at source-equivalent level. Exact GitHub current-head checkout, pinned local Agda kernel, rigorous interval-bounded moment calculation, global Neumann FIO theorem-review and actual physical observation are separate open gates.


## F8-NEG — exact local TT outside-support null control exposes discrete inverse leakage

An additional **equation-independent negative control** now independently checks the inverse 3D angular-Bessel transform itself. The original source is \(\pi_{ij}^{TT}=\epsilon^4[P_{ik}P_{jl}-\frac12P_{ij}P_{kl}]Q_{kl}\varphi_\epsilon\), where **every \(P\) is a local differential operator** and \(\operatorname{supp}\varphi_\epsilon\subset B_\epsilon(0)\). Therefore
\[
\boxed{\pi^{TT}_{yy}(\mathbf x)=0\quad\text{exactly whenever }|\mathbf x|>\epsilon.}
\]
In particular \(r=1.8220210521210103\gg\epsilon=0.024\) is a **mathematically exact zero** regardless of bulk propagation. Reconstruct this *unpropagated* source using precisely the existing \`ksw668_f8_moving_maxcut.py\` formula
\[
\pi_{yy,\mathrm{grid}}^{TT}(r)=
\epsilon^4\frac{\Delta k}{4\pi^2}
\sum_{n=0}^{N_x/2}k_n^6\widehat\varphi_\epsilon(k_n)
\,2\!\left(\frac25j_0(k_nr)-\frac47j_2(k_nr)+\frac1{35}j_4(k_nr)\right),
\quad k_n=\frac{2\pi n}{L}.
\]
The **false outside-support reconstruction** is:

| \(N_x\) | Exact compact TT outside-support value | Same-rule numerical value |
| ---: | ---: | ---: |
| 256 | 0 | \(+481.9432930\) |
| 512 | 0 | \(+611.4094224\) |
| 768 | 0 | \(+626.2563619\) |

The original 96-node vs independent 384-node radial bump quadrature changes the last value by **less than \(4\times10^{-11}\)**. The failure is not an original moving-AdS physical effect, not an incoming bulk signal, and not predominantly insufficient radial quadrature for the bump. It is a **static inverse-transform UV/spacing artifact**, observed before any PDE time evolution. Do **not** compare its numerical amplitude directly to the moving receiver signal (different source/response normalization); this is a zero-control of the reconstruction operator itself.

New owner: \`scripts/ksw668_f8_static_tt_reconstruction_null.py\` and its **10/10** local tests. This supplies a strict **mandatory acceptance prerequisite** for F8.3: the same inverse transform must reproduce compact local TT-source support to the designated numerical tolerance on an independently converged grid **before** the moving-wave source-to-Weyl value can be accepted. It also pinpoints the positive repair route: adaptive/oscillatory \(k\)-quadrature with independent \(\Delta k\) and \(k_{\max}\), plus a provably controlled source support null check.

**Combined independent source-equivalent run (2026-11-15):** F8 original 68 previous tests plus 13 source-UVIR, 12 IR-spacing, and 10 exact-support static null tests = **103/103 PASS**, captured in \`ksw668_f8_uvir_combined_local_acceptance_20261115.log\`. The 10 negative-control tests PASS because they correctly detect a failed numerical method; this does NOT mean the physical F8 receiver convergence passed. Exact GitHub-head executable, Agda 2.9 kernel and physical measurements remain unverified.


## F8-REAL — exact positive AND negative local TT source reference

The source support null test above now has an independent **real-space constructive differential formula**, not only an abstract support theorem. With \(P_{ij}=-\delta_{ij}\Delta+\partial_i\partial_j\), \(Q=\operatorname{diag}(0,1,-1)\), and a radial seed \(f(r)\), direct differential algebra on the \(x\)-axis gives
\[
\boxed{\left(PQP-\tfrac12P\,\operatorname{tr}(PQ)\right)_{yy}f(r,0,0)
=f^{(4)}+\frac{2f^{(3)}}r-\frac{3f''}{r^2}+\frac{3f'}{r^3}.}
\]
This identity is verified independently by SymPy against direct four-spatial-variable Cartesian differentiation of a nontrivial 3D Gaussian. Applied to the **same normalized original compact \(C^\infty\) radial bump**, with the existing \(\epsilon^4\) convention, it yields **\(-1{,}852{,}823.05935\)** at \(r=\epsilon/3=0.008\) and **exactly \(0\)** for any \(r\ge\epsilon=0.024\), including the F8 numerical receiver at \(r=1.82202\). At fixed scaled radius \(r/\epsilon\), the source value has the expected \(\epsilon^{-3}\) scaling. This is the independent reference that the **radial Fourier reconstruction must reproduce** before its wave-propagated version can be accepted. New \`scripts/ksw668_f8_exact_spatial_tt_local.py\` and **8/8** tests.

Full local source-equivalent F8 math suite: old 68 + new 13 UV moments +12 independent momentum-spacing +10 static false-source +8 exact real-space source = **111/111 PASS** in one independent unittest-discover run. **The numerical F8 3D receiver is still NOT converged.** Tests that demonstrate false nonzero values on an exact-zero control count as successful diagnostic tests, not successes of the physical signal criterion.

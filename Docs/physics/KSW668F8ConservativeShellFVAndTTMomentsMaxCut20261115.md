# KSW668 F8 maximum cut — correct 3/7/11-D shell FV, exact compact TT moments, original moving PDE manufactured test

**Date:** 15 November 2026. **Canonical owner:** current open PR #1512, no parallel rollup. **Original physical model:** five-dimensional Poincaré AdS5 with original cosmological brane scale factor \(a(t)=t\), \(z_b(T)=1/t\), and original sourced linear tensor Israel normal condition \(n\cdot\partial H_{ij}=-6\pi_{ij}^{TT}\). Real 3D source geometry is unchanged by angular algebra. \(\ell=0,2,4\) effective radial dimensions \(d=3,7,11\) are **radial-coordinate conjugacy dimensions only**.

## The source-specific numerical bug: centre-volume FV was not actually a finite-volume Laplacian

The existing multipole solver had implemented \(\Delta_d=\partial_r^2+(d-1)r^{-1}\partial_r\) with face weights \(A_{j\pm1/2}=r_{j\pm1/2}^{d-1}\) but replaced the cell volume by its centre approximation \(r_j^{d-1}\Delta r\). This is especially wrong near the \(r=0\) centre for \(d=11\), where the first off-centre cell had the wrong radial speed/forcing. The repaired solver now uses the **exact effective-d-dimensional radial volume**
\[
V_j=\frac{r_{j+1/2}^d-r_{j-1/2}^d}{d},\quad
(L_{d,h}U)_j=
\frac{r_{j+1/2}^{d-1}(U_{j+1}-U_j)
-r_{j-1/2}^{d-1}(U_j-U_{j-1})}
{\Delta r\,V_j}.
\]
At the origin, the vanishing inner face yields exactly \(L_{d,h}U_0=2d(U_1-U_0)/\Delta r^2\). Since \((r_{j+1}^2-r_j^2)/\Delta r=2r_{j+1/2}\),
\[
\boxed{L_{d,h}(r^2)=2d\quad\text{AT EVERY INTERIOR CELL, including }j=0.}
\]

| Effective \(d\) | Incorrect old \(j=1\) value | Correct FV \(j=1\) value |
|---:|---:|---:|
| 3 | \(6.5\) | **\(6\)** |
| 7 | \(34.15625\) | **\(14\)** |
| 11 | \(172.994140625\) | **\(22\)** |

**New Agda source owner** \`DASHI/Physics/Gravity/KSW668AdS5TTFiniteVolumeFirstCellRationalExact.agda\` proves the exact rational first-cell coefficients by \`solve []\` in the source (kernel still unrun):
\[
(c_3^+,c_3^-)=(27/13,3/13),\
(c_7^+,c_7^-)=(5103/1093,7/1093),\
(c_{11}^+,c_{11}^-)=(649539/88573,11/88573).
\]
The first-cell exact identities are \((3c_d^+-c_d^-)=2d\). Source-level NumPy tests also check arbitrary cells, constant fields, and negative tests against all three old values.

### New weighted discrete Green identity — not simply a polynomial fit

For \(U_N=0\) at the outer radial Dirichlet test wall and vanishing inner-face area \(A_{-1/2}=0\), exact finite-volume summation by parts gives
\[
\boxed{\sum_{j=0}^{N-1}V_jU_j(L_{d,h}U)_j
=-\sum_{j=0}^{N-2}\frac{A_{j+1/2}}{\Delta r}(U_{j+1}-U_j)^2\le0.}
\]
This is a genuine **semidiscrete self-adjoint negative radial operator** in the \(V_j\)-weighted space. This supports an energy estimate for the radial subsystem. It is **not** a fully discrete SSPRK3 CFL theorem, a coupled moving-boundary stability proof, or receiver convergence. The exact property was checked with several nonpolynomial finite data arrays at \(d=3,7,11\). Mathematically, the identity follows by telescoping face fluxes without approximations.

## Exact compact TT source cell-integral primitives and infrared moments

The original compact scalar radial bump is \(f(u)=e^{1-1/(1-u^2)}\) for \(0\le u<1\) and 0 beyond. Let \(S_\ell(u)\) denote the true \(\ell=0,2,4\) angular Legendre components of the **local fourth-order TT source** \(\mathcal S_{\rm TT}[f]\), as derived in the previous F8 exact angular algebra owner. Writing \(H_\ell=(r/\epsilon)^\ell V_\ell\), the source for \(V_\ell\) is \(S_\ell(u)/u^\ell\); its weight in the effective radial problem is \(u^{2+2\ell}\). Direct differentiation gives **exact primitives**
\[
\begin{aligned}
\int u^2 S_0(u)\,du
 &=\tfrac25(u^2f'''+2uf''-2f'),\\
\int u^4 S_2(u)\,du
 &=\tfrac47(u^4f'''-3u^3f''+3u^2f'),\\
\int u^6 S_4(u)\,du
 &=\tfrac1{35}(u^6f'''-12u^5f''+75u^4f'-315u^3f)
 +27\int u^2f(u)\,du.
\end{aligned}
\]
Both the origin and compact support endpoints have vanishing derivative-boundary terms. Therefore,
\[
\boxed{\int_0^1u^2S_0\,du=0,\quad
\int_0^1u^4S_2\,du=0,\quad
\int_0^1u^6S_4\,du=27\int_0^1u^2f\,du>0}.
\]
The last dimensionless source moment equals \(2.57616988094614\) for this particular compact \(C^\infty\) bump. The first two are exact IR cancellations, not arbitrary floating-point tolerances. This **source-level infrared cancellation is not a suppression theorem for the physically independent AdS KK radial zero mode**.

The new \`scripts/ksw668_f8_fv_source_flux.py\` integrates each source cell using those **exact derivative-endpoint fluxes**, plus a positive one-dimensional quadrature for the \(\ell=4\) remaining \(\int u^2f\) term. The default original moving solver now uses these source cell averages. Independent 96-node Gaussian integration agrees at relative error \(\lesssim 10^{-8}\) for the tested source widths and cells. Beyond-support source cells remain exactly zero. Source moment and support tests are part of the smoke suite; **this does not automatically control the high-frequency receiver trace**.

## Original moving PDE manufactured positive control, including the true Neumann Israel wall

The new \`scripts/ksw668_f8_manufactured_original_pde.py\` directly calls the *same actual committed numerical stage* for all three effective \(d\). For each \(d\), consider the noncompact analytic test
\[
H_d(T,z,r)=dT^2+r^2.
\]
It satisfies the original bulk operator exactly:
\[
(-\partial_T^2+\partial_z^2-\tfrac3z\partial_z+\Delta_d)H_d
=-2d+2d=0.
\]
Its characteristic fields are \(q_+=q_-=2dT\), and its original moving physical normal datum is
\[
\boxed{G_d(T)=2d\,v(T)\,T}.
\]
The implemented oblique source condition \((1+v)q_++(v-1)q_-=2G_d\) holds exactly. The corrected semidiscrete stage reproduces the manufactured \(\partial_TH_d=2dT\) and \(\partial_Tq_\pm=2d\) throughout the unmodified interior stencil, at both original \(t=4/3\) and arbitrary tested \(t\) and meshes. The forced outgoing remote boundary and its stencil are explicitly excluded from this local consistency test. **This is a noncompact manufactured solution, not a physical compact source or a new retarded signal**.

## Actual moving-brane 3-grid rerun after the FV repair

Same original \(t=12\), spatial source radius \(\epsilon=.04\), Poincaré temporal support .065, original same receiver \(r=2.53736576096\), bulk horizon \(2.54936576096\), brane photon \(r_\gamma=\ln12\), positive source-adjusted photon-dark margin \(0.0124591112\). Exactly the previous three mesh pairs, but with corrected shell volumes and compact source primitive averages:

| \(\Delta r,\Delta y\) | \(H_{yy}\) | intrinsic \(E^{(4)}_{yy}\) | projected \(E^{(5)}_{yy}\) |
|---|---:|---:|---:|
| 0.012, 0.016 | \(-2.83814371\times10^{-6}\) | \(-6.23958175\times10^{-5}\) | \(-3.45389514\times10^{-6}\) |
| 0.008, 0.012 | \(-6.76189918\times10^{-6}\) | \(-5.64432541\times10^{-5}\) | \(-2.90080314\times10^{-6}\) |
| 0.006, 0.011 | \(-8.64273461\times10^{-6}\) | \(-5.80312730\times10^{-4}\) | \(-1.67367136\times10^{-5}\) |

Fine-vs-medium relative drifts: **\(H=21.762\%\)** (previous ~47.312%); **intrinsic \(E^{(4)}=90.274\%\)** (previous ~92.848%); **projected \(E^{(5)}=82.668\%\)** (previous ~86.620%). The field drift improves, but none of these satisfies physical numerical acceptance. Outside-bulk-front leakage remains nonzero on all grids, including for Weyl; the strongest direct physical claim is still **UNPROVED**.

The source-level tangent-characteristic \(\partial_TU\) and a second finite-differenced wavefield time derivative give closely matching Weyl values at each grid (independent numerical differentiation *crosscheck*); their agreement while the spatial/normal grid is varied suggests the remaining large curvature drift is **not simply a time-differencing artifact**. It is not proof that the numerical Weyl operator is correct to a certified physical tolerance.

The full existing legacy Fourier-Bessel route remains failed. Neither a correct finite-volume operator nor an exact compact source integral can repair the **physical receiver source-to-Weyl trace** without its own convergence/energy bound. The current full multipole acceptance script must continue to **exit 42**.

## Exact lemma disposition and next hard cut

| Owner / lemma | Current status |
|---|---|
| \`ads5OriginalTTThreeMultipoleExactShellVolumeRadialFV\` | **MATHEMATICS CLOSED**: exact quadratic consistency, weighted Green identity; symbolic/rational first-cell Agda *source* added; pinned Agda kernel OPEN |
| \`ads5OriginalTTCompactSourceL0L2MomentCancellation\` | **MATHEMATICS CLOSED** by compact-support integration by parts; 1D quadrature crosscheck PASS; full Agda differentiable formalization OPEN |
| \`ads5OriginalTTCompactSourceL4PositiveMomentExact\` | **MATHEMATICS CLOSED**: moment \(27\int u^2f\), source cell quadrature crosscheck PASS |
| \`ads5OriginalMovingTTManufacturedPolynomialInteriorIsrael\` | **SEMIDISCRETE CONTRACT CLOSED**: actual moving original PDE stage, source and radial normalization tests; coupled IBVP convergence still OPEN |
| \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | **OPEN**: field and both Weyl original receiver drift remains 22%, 90%, 83% plus outside-cone leakage |
| \`ads5OriginalMovingWeylSobolevBoundaryTraceAndError\` | **OPEN**: analytic source-to-boundary curvature trace and cutoff/error transfer |
| \`ads5OriginalTTSourceCellFluxConservationFullDiscreteEnergy\` | **PARTIAL**: exact spatial radial semidiscrete energy, temporal SSPRK3/moving Neumann boundary CFL/error theorem OPEN |
| \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` and \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | **External-theorem-dependent existential proof candidate; independent theorem/referee and Agda continuum acceptance OPEN** |
| F9 physical matter-generating action, all-mode stability and separate cylinder bulk | **OPEN** |
| F10 physical scale/attenuation/source-lag/detector comparison | **OPEN** |
| F11 pinned Agda 2.9 continuum kernel and source-to-observation semantic weld | **OPEN** |
| D1 empirical controlled gravitational observation | **OPEN** |

**Source-equivalent regression:** prior 134 committed F8 cases plus **13** FV algebra/energy tests, **10** exact source moment tests, **10** original moving manufactured-PDE cases and **5** new Weyl/FV/source-moment assertions in the existing multipole tests = **172 committed-source-equivalent cases**. A broader local superset including 13 pre-existing uncommitted exploratory radial-prepotential tests passed **185/185** with the patched local source. The exact PR-head runner and pinned Agda 2.9 executable were not run in the current environment. Independent theorem review and physical empirical validation are not replaced by code success.

**Primary next maximum cut:** establish a quantitative three-multipole *full* moving-boundary discretization stability, boundary normal-trace and curvature-error bound. Apply controlled compact-source scaling and compare \(t=2\) original-source receiver (small causality window) with improved long-baseline \(t=12\) numerical control. Independent \((\Delta r,\Delta y,\Delta T)\) refinements must be separated before a nonzero early signal is promoted. The full external FIO theorem-application candidate remains a separate mathematical route, not an empirical substitute.


**Additional source-conservation runtime fail-close:** each propagated compact 3D TT source now checks its *actual radial cell-volume sums*: the normalized \(\ell=0\) and \(\ell=2\) weighted moments must be zero to the declared \(10^{-7}\) floating tolerance, and \(\ell=4\) must match the independently integrated positive source moment \(27\int_0^1u^2f(u)du\). A corrupted source grid is rejected before PDE evolution. The broader local superset now passes **185/185** tests; the committed smoke has **172** source-equivalent test cases. The quantitative full moving receiver/Weyl convergence remains OPEN.

# KSW668 F8 maximum-cut XI — full native-weighted \(C_3\) operator test, three-grid dual-Weyl failure and radial/normal factorial cut

**16 November 2026 · User-origin follow-through · Existing PR #1520, based on merged #1512.** This report tests the exact \(\ell=0,2,4=2(0,1,2)\) Base369 indexing proposal against the **original physical AdS₅ radial operators** and advances the **original compact 3D TT tensor source-to-both-Weyl numerical acceptance**. No unseen original mathematical/empirical graviton endpoint is promoted. Pinned Agda 2.9 kernel and connected GitHub exact-head test execution **UNRUN**.

## 1. Full operator test: even a radial-volume-unitary \(C_3\) rotation fails

Previous F8 X showed the correct local \(r^2\) radial witness \(\Delta_{3,7,11}(r^2)=6,14,22\). This round tests the **entire original conservative finite-volume matrices**, not only a quadratic at one cell.

For each \(q=0,1,2\), \(d_q=3+4q\). Let \(L_{d_q,h}\) be the original exact-shell-volume radial FV matrix with the original outer Dirichlet cell removed, \(V_{q,h}>0\) its actual radial cell-volume matrix, and
\[
S_q=V_q^{1/2}L_{d_q,h}V_q^{-1/2}.
\]
Each \(S_q\) is *genuinely real symmetric*. On the direct sum of **three native-weighted radial spaces**, put \(A=\operatorname{diag}(S_0,S_1,S_2)\). Define the strongest natural cyclic rotation \(T\) to rotate the **normalised** vectors \(V_q^{1/2}u_q\) rather than incorrectly identifying weighted function spaces. Then
\[
T^\top T=I,\qquad T^3=I,\qquad
[A,T]_{q+1,q}=S_{q+1}-S_q\ne0.
\]
At 12 radial cells and \(\Delta r=.015\), the actual full-matrix Frobenius commutator norm is **93,318.9410368**. The sorted radial eigenvalue lists differ: their largest absolute gaps from \(d=3\) are **33,968.3153** for \(d=7\), **69,481.7442** for \(d=11\). Both the **matrix commutator and spectral obstruction** survive radial-grid variants. This refutes the **natural norm-compensated Base369 cyclic label operation** as a physical original finite-grid radial symmetry, with no assumption of equal radial measures.

Scope: this is not a proof excluding *every possible* exotic nonlocal continuum operator intertwiner or arbitrary non-radial brane symmetry. The original \(q\)-triple is a *lossless observable carrier*; the exact three-point cyclotomic Fourier change-of-basis is still valid **only when all three transformed sectors and their off-diagonal dynamics are retained**.

## 2. Third grid **actually completed**: negative dual-Weyl result, not an extrapolation

The original full-box \(\Delta r=.006,\Delta y=.009,\Delta T=.0012\) run had previously timed out. This round executed the same original sourced moving AdS₅ tensor solver using parallel independent \(\ell\)-modes and a smaller finite box. **All three actual physical receiver grids are now available**:

| Mesh | \(\Delta r\) | \(\Delta y\) | Requested \(\Delta T\) | \(H_{yy}\) | Intrinsic \(E^{(4)}_{yy}\) | Projected \(E^{(5)}_{yy}\) |
|---|---:|---:|---:|---:|---:|---:|
| coarse | .012 | .016 | .0025 | −5.13978759e−6 | −6.73168679e−5 | −2.93029492e−6 |
| medium | .008 | .012 | .0018 | −6.21637547e−6 | −2.80531162e−5 | −2.32621569e−6 |
| fine | .006 | .009 | .0012 | −2.54488883e−5 | −6.33841188e−4 | −1.93196045e−5 |

**The sequence is not convergent by the required criterion.** Absolute coarse→medium and medium→fine changes in each individually reconstructed \(E^{(4)}\) and \(E^{(5)}\) harmonic **grow**, not shrink:

| \(\ell\) | Intrinsic \(E^{(4)}\): ratio \(\lvert\Delta_{m\to f}\rvert/\lvert\Delta_{c\to m}\rvert\) | Projected \(E^{(5)}\): ratio |
|---|---:|---:|
| 0 | **9.518** | **8.311** |
| 2 | **2.622** | **3.456** |
| 4 | **1.872** | **3.116** |

The \(\ell=0\) channel dominates the failed intrinsic Weyl refinement. The fine-grid outside-bulk-cone control is also not zero: \(E^{(4)}\) aggregate **+6.57138e−6**, \(E^{(5)}\) **+1.97010e−7**, \(H\) **−2.74305e−7**, approximately **1%** of their respective receiver magnitudes. This is numerical leakage/uncertainty, **not an early gravitational detection**.

### Finite-box causal qualification

All physical source and receiver data are identical: \(a(t)=t\) brane; source spatial support \(\epsilon=.04\), Poincaré pulse .065; \(t_{\rm receiver}=12\); \(r_{\rm receiver}=2.53736576096\); original outgoing/weak Israel operators, exact radial FV volumes, original compact TT cell moments, and \`normal_order=3\`. The accelerated box is \(r_{\max}=3.01\), \(y_{\max}=2.01\), versus prior \(3.15,2.6\). Its radial source-to-outer-face geometric lower bound is \(3.01-.04-.006/2=2.967\), beyond the available Poincaré span \(2.7091592\). A physical normal-wall reflection reaching the final brane would require at least \(2y_{\max}+b_{\rm final}-b_{\rm emit}\ge3.10333>2.70916\). In the actual solver, **coarse and medium receiver outputs agree with the original large-box runs** to reported precision.

However, a finite-difference method can have a broader **discrete** domain of dependence than the continuum null cone. Full-box parity of the **fine** discrete receiver has NOT been established. The smaller-box fine grid is a real completed negative control, **not** a fine-grid physical/continuum error certificate or proof of boundary irrelevance for every numerical stencil.

## 3. The temporal derivative readout is not the observed dominant disagreement

The original readout now returns, **per \(q\)**, the \(H\)-central-second-difference and first-order-PDE-stage differentiated Weyl estimates, with exact algebraic difference formulas and independently reconstructed full \(E^{(4)},E^{(5)}\) sums. These are two consistent approximations, **not an a posteriori bound on the exact curvature**.

For the fine \(\ell=0\) intrinsic Weyl result, the two temporal readouts differ by **−1.43344e−7**. The actual medium→fine channel change is **−6.88347e−4**, about **4,800× larger**. A separate **same medium spatial grid, half time step** experiment \(\Delta T=.0018\to.0009\) changes the \(\ell=0\) intrinsic Weyl by only **+2.82007e−8** and the \(\ell=2\) channel by **+4.34508e−7**. Thus the large medium→fine spatial change cannot be attributed merely to the observed final temporal-readout disagreement or that tested medium time-step change. A fine-grid \(\Delta T=.0006\) attempt **timed out**, with NO fine-time-halved receipt. Fully discrete error control remains OPEN.

## 4. Crucial controlled 2×2 radial/normal experiment at the SAME \(\Delta T\)

Independently change \(\Delta r\) and \(\Delta y\) at **identical actual** Poincaré timestep \(0.00119980478\):

| Arm | \(\Delta r\) | \(\Delta y\) |
|---|---:|---:|
| A (base) | .008 | .012 |
| B (normal only) | .008 | .009 |
| C (radial only) | .006 | .012 |
| D (both) | .006 | .009 |

For each original physical \(q\) channel and observable \(O\),
\[
\boxed{O_D-O_A=(O_C-O_A)+(O_B-O_A)+(O_D-O_C-O_B+O_A).}
\]
This is an **exact signed finite factorial decomposition** into radial-only, normal-only, and mixed interaction; it is NOT continuum truncation-error identification.

For intrinsic Weyl \(\ell=0\), radial-only \(O_C-O_A\approx-6.78984\times10^{-4}\), normal-only \(O_B-O_A\approx+1.05690\times10^{-7}\), and mixed \(\approx-9.49057\times10^{-6}\). The radial-only term accounts for **98.64% of the signed combined change**. For \(\ell=2\), radial-only is \(+8.53929\times10^{-5}\), normal-only \(+8.79535\times10^{-7}\), mixed \(-2.34757\times10^{-6}\); radial-only is **101.7%** of the signed net because other terms oppose it. The same pattern holds for projected Weyl (radial signed fractions 97.1% and 102.1% for \(\ell=0,2\)).

**Maximum-cut implication:** the unresolved error is primarily sensitive to the radial mesh in this controlled finite experiment. The next exact contract is \`ads5OriginalTTCompactSourceVsConservativeRadialPropagationErrorSeparation\`: distinguish high-frequency compact source-cell representation, radial numerical dispersion/wavefront location, radial curvature interpolation and normal coupling **in the same original physical source**. Do not waste the next cut exclusively on the effective-11D \(\ell=4\) CFL or on unvalidated Weyl aggregate cancellation.

## 5. Global physical weak-Israel constraint — exact SBP2 left-null solvability obstruction

Let \(D_y\) be the existing centered diagonal-norm SBP2 first derivative on \(n\ge3\) normal nodes. The original metric constraint is \(C_h=D_yU-(P-M)/2\). Keep the original weak SAT increments to the \(P\) and \(M\) equations fixed and try to repair **only** the metric equation by \(\delta U_T=K\). Global \(C'_h=0\) demands
\[
D_yK=g,\qquad g=\tfrac12(\mathrm{SAT}_P-\mathrm{SAT}_M).
\]

The exact one-dimensional **left kernel** of \(D_y\) is generated by
\[
\ell_0=(-1)^{n-1},\qquad
\ell_j=2(-1)^{n-1-j}\ (1\le j\le n-2),\qquad
\ell_{n-1}=1.
\]
This is proved by the explicit endpoint and interior column recurrences; \(\operatorname{rank}D_y=n-1\). Because \(g\) has independent endpoint components, an \(U_T\)-only repair exists **if and only if**
\[
\boxed{(-1)^{n-1}g_{\rm wall}+g_{\rm far}=0.}
\]
Generic independent wall/far weak SAT data violate it. The exact incompatible choice \((g_{\rm wall},g_{\rm far})=(1,2)\) yields left-null product **3 for odd \(n\), 1 for even \(n\)**. Compatible choices satisfy it and pass a rank/solvability check, so this is not merely an overstrong sufficient condition. Tested symbolically for \(n=3,\ldots,13\), with separate exact rational Agda n=3/4 source certificates in \`KSW668AdS5TTWeakIsraelSBPLeftNullParityExact.agda\` imported into the canonical gravity rollup. **Pinned Agda kernel NOT RUN; the arbitrary-n proof is in mathematics/Python, not kernel-certified Agda.**

This **only** rules out changing \(U_T\) alone while keeping both original characteristic SATs unchanged. It does **not** rule out jointly changing the \(P,M,U\) penalties, changing the discrete constraint, or a nonlocal energy-compatible boundary weld. That remains the next boundary mathematical gate.

## 6. Committed reproducibility and remaining endpoints

The canonical negative machine receipt is \`Artifacts/ksw668/ads5_f8_threegrid_per_channel_radial_normal_factorial_maxcut_xi_20261116.json\`. The actual solver \`scripts/ksw668_f8_tt_multipole.py\` now uses parallel q loops and exports both independent per-q temporal Weyl readouts; coarse/medium parity with the original output was tested. Use \`scripts/ksw668_f8_threegrid_signed_failclosed.py --run-grid fine\` for full original fine-mesh replay and \`--accept\` to explicitly fail acceptance with exit **42**. Tests audit per-mode actual three-grid and factorial data, the full native-weighted original C3 obstruction, and the SBP parity solvability condition.

**Locally executed:** **410/410** reconstructed source-equivalent F8 regression tests PASS, including the parallelized solver. The connected exact PR-head runner and pinned Agda 2.9 kernel have not been run; do not conflate regression acceptance with numerical convergence.

| Endpoint | Disposition |
|---|---|
| Base369 unsigned 0/1/2 ↔ exact spin-2 \(\ell=0,2,4\) and three-channel H/E4/E5 | Finite algebra/source reconstruction **CLOSED**, pinned Agda still open |
| Original volume-compensated full radial \(C_3\) cyclic intertwiner | **REFUTED for the natural C3**, full finite FV matrices/spectra |
| Original three-grid per-channel H/E4/E5 convergence | **FAILED** in completed fine-grid negative control; full-box fine parity and continuum error bound open |
| Exact radial/normal same-time-step factorial separation | **FINITE NUMERIC CLOSED**: dominant radial sensitivity; actual source-versus-propagation error still open |
| Original SBP2 weak Israel \(U_T\)-only global constraint repair | **REFUTED generically**, exact left-kernel parity obstruction |
| Joint energy-stable, globally constraint-compatible sourced weak Israel SAT | **OPEN** |
| Entire coupled time-dependent SSPRK3 stability, truncation and source lift error | **OPEN** |
| Uniform compact-source full \(H^{4+\epsilon}\) normal/time/radial Neumann-to-both-Weyl boundary trace | **OPEN** |
| Original \(t=2\) prescribed compact-source FIO actual dual-Weyl mathematical acceptance | **OPEN**, historical external-theorem application preserved |
| F9 source-generating matter/cylinder/backreaction; F10 scale/detector; F11 pinned kernel/observer semantics; D1 independent empirical observation | **OPEN** |

**No measured graviton or superluminal physical message is established.** The next cut is a same-source radial wavefront/FV and source-cell representation error theorem, **then** a joint constraint-preserving SAT/SSPRK3/Higher Weyl trace.

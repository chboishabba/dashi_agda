# KSW668 F8 maximum-cut IX — physical characteristic constraint, compatible coupled energy, original compact TT source, and all radial Sobolev orders

**15 November 2026.** Owner: **PR #1520** after merged #1512; do not reopen #1512 or substitute a different bulk metric. **Original model:** moving flat-FRW \(a(t)=t\), Poincaré AdS₅ \(z\ge b(T)=1/t\), \(v(T)=-1/\sqrt{1+t^2}\), physical sourced linear TT Israel–Neumann condition. **This is not an experimental graviton claim.** Previous standalone original-\(t=2\) FIO Markdown is preserved and linked from the canonical roadmap; it remains an independent external-theorem application requiring referee-level acceptance.

## A. The physical constraint identifies the flaw in maximum-cut VIII's preferred weighted normal discretization

Set \(P=H_T+H_z,\ M=H_T-H_z,\ y=z-b(T)\). Since the *original* tensor perturbation \(U\) is a single metric field, its characteristic variables must satisfy
\[
\boxed{C=\partial_yU-\tfrac12(P-M)=0.}
\]
With \(a=(1+v)/2,\ c=(1-v)/2\), the true original first-order PDE has \(U_T=aP+cM\) and the **same** radial Laplacian and AdS warp in the two characteristic equations.

At the discrete normal grid, define \(C_h=D_yU-(P-M)/2\). For **unweighted second-order diagonal SBP + weak original Neumann SAT** (\`normal_order=3\)), the actual original scheme uses the same \(D_y\) in \(P_T,M_T\). Therefore, for every *interior* node,
\[
\boxed{\dot C_{h,j}=a D_yP+c D_yM
-\tfrac12\{(1+v)D_yP-(v-1)D_yM\}=0.}
\]
The radial operator, AdS \(3/z\) warp, and nonzero Israel source *all cancel or are confined to boundary SAT*. This is exact algebra of the actual finite grid, independent of the grid spacing or smoothness of the input state.

SSPRK3 also preserves these **interior** constraints *exactly*, because \(C_h\) is a fixed linear grid operator and all three forward-Euler stage derivatives of \(C_{h,j}\) vanish for interior \(j\). The replay uses the **actual original Poincaré clock** \(T=F(t)=\mathrm{asinh}(t)-\sqrt{1+t^2}/t\) to choose \(t\), \(t(T+\Delta T/2)\), \(t(T+\Delta T)\), and stage-varying Neumann forcing. A finite-grid test initialized with \(C_h=0\) everywhere has post-SSPRK3 mode-3 interior residual approximately \(3.6\times10^{-15}\).

The \(z^{-3}\)-weighted split scheme \`normal_order=4\` instead uses \(D_w f=z^{3/2}D_y(z^{-3/2}f)+3f/(2z)\), which is **not the same discrete derivative** as in \(C_h\). Its exact interior defect is
\[
\boxed{\dot C_{h,j}=a(D_y-D_w)P_j+c(D_y-D_w)M_j.}
\]
For representative rough finite states its maximum on original \(t=1,4/3,2,12\) slices is respectively 0.952, 1.128, 2.044, 5.859, while the same mode-3 residuals are \(\sim10^{-13}\). For a smooth manufactured pair \(P(y),M(y)\), weighted-mode defects fall by \(\sim3.88,3.91,3.97\) under consecutive halvings of \(\Delta y\): **second-order consistent but not exactly constraint-preserving**. This does not invalidate mode 4's genuine coupled weighted energy theorem; it prevents claiming an unproved *physical metric constraint* from that theorem.

**New source and tests:** \`scripts/ksw668_f8_characteristic_constraint_maxcut.py\`, \`test_ksw668_f8_characteristic_constraint_maxcut.py\`. **Agda rational/source-only:** \`KSW668AdS5OriginalTTCharacteristicConstraintRationalExact.agda\`, including the SBP2-vs-weighted polynomial defect and SSPRK3 combination identity. Pinned Agda kernel **not run**.

## B. A stronger route: mode 3 preserves the interior metric constraint AND has a coupled moving AdS energy estimate

The earlier **full coupled, original physical \(z^{-3}\)** homogeneous estimate for mode 4 is
\[
E_4'(T)\le5E_4(T),\qquad E=\frac12\sum H_y z^{-3}V_r
\left(aP^2+cM^2+U(-L_r)U\right),
\]
with actual weak original Israel SAT and exact conservative radial FV \(d=3,7,11\). Switching normal derivatives to the physically constraint-preserving \(D_y\) **does not destroy the radial/normal coupling cancellation**; it creates a finite weighted commutator. For either characteristic \(f\),
\[
B(f)=\langle f,(D_y-D_w)f\rangle_{H_yw},\quad w=z^{-3}.
\]
With \(Q=H_yD_y\), \(Q+Q^T=\operatorname{diag}(-1,0,\ldots,0,+1)\), the **exact symmetric quadratic matrix** for \(B\) has diagonal
\[
B_{ii}^{\rm sym}=-H_iw_i\frac{3}{2z_i}
\]
and off-diagonal edge \(B^{\rm sym}_{i,i+1}=(w_i-w_{i+1})/4\), all other entries zero.

Normalize by \(\sqrt{H_iw_i}\). Its diagonal has magnitude at most \(3/(2b)\) and each off-diagonal has magnitude
\[
\frac{w_i-w_{i+1}}{4\sqrt{H_iw_iH_{i+1}w_{i+1}}}.
\]
If \(0<\Delta y\le b/4\), write \(s=\Delta y/z_i\in[0,1/4]\). The elementary derivative bound for \(f(s)=(1+s)^{3/2}-(1+s)^{-3/2}\) gives \(f(s)\le(7/2)s\). Since \(\Delta y/\sqrt{H_iH_{i+1}}\le\sqrt2\), every edge is \(\le7\sqrt2/(8b)\). Gershgorin gives
\[
\max_i\left(\frac{3}{2b}+\frac{7\sqrt2}{4b}\right)<\frac4b,
\]
so the **mesh-independent** quadratic-form estimate is
\[
\boxed{|\langle f,(D_y-D_w)f\rangle_{H_yw}|
\le\frac4b\|f\|^2_{H_yw}.}
\]
Direct tests check the exact symmetric matrix/quadratic identity, all diagonal and edge terms, and this analytic bound at 16 original \(t,\Delta y\) combinations including \(t=12\). The full original mode-3 and mode-4 energy derivatives differ by exactly
\[
E_3'-E_4'=
\sum_\ell V_r\{a(1+v)B(P_\ell)+c(v-1)B(M_\ell)\}.
\]
Since \(1+v\le1,\ 1-v\le2\), the difference has magnitude at most \(16E/b\). Therefore for original \(t\ge1\),
\[
\boxed{E_3'(T)\le(5+16t)\,E_3(T),\quad\Delta y\le1/(4t).}
\]
This estimate is **coupled normal + radial + AdS warp + moving wall**, not a separate normal-mode statement. On \(1\le t\le12\), the uniform coefficient \(197\) is valid. This is conservative, not a sharp physical amplification estimate.

## C. Actual nonzero original compact TT Israel forcing — same constraint-preserving scheme

The same original weak-SAT source target is \(M_*=\beta P_0-2G/(1-v)\). The **algebraic first-order characteristic lift**
\[
\Lambda_U=\Lambda_P=0,\quad
\Lambda_M=-\frac{2G(T,r)}{1-v(T)}\chi(y),\quad\chi(0)=1
\]
homogenizes that target. In **unweighted mode 3**, the explicit bulk forcing is
\[
\begin{aligned}
F_U&=c\Lambda_M,\\
F_P&=3\Lambda_M/(2z),\\
F_M&=(v-1)D_y\Lambda_M+3\Lambda_M/(2z)-\partial_T\Lambda_M.
\end{aligned}
\]
Note that the correct mode-3 forcing uses \(D_y\), **not the previous mode-4 \(D_w\)**. The source energy norm includes the radial gradient \(\nabla_r F_U\), making the high-UV demand explicit.

Applying Young's inequality to the coupled mode-3 symmetrizer gives the exact sourced **semidiscrete** bound
\[
\boxed{\widetilde E_3'(T)\le(6+16t)\widetilde E_3(T)
+\tfrac12\|F(T)\|_E^2,\quad \Delta y\le1/(4t).}
\]
On \(1\le t\le12\), use coefficient \(198\).

A reproducible producer subtracts the lift from the **actual sourceful Numba stage** and checks every \(F_U,F_P,F_M\). It checks arbitrary modal sources and, separately, the **same original smooth compact three-dimensional TT modal source** \(\epsilon=.04\) from the physically relevant exact cell-primitive module, across original \(t=1,4/3,2,12\). The compact source derivative \(G_T=.35G\) defines a local smooth temporal test datum; it is not a complete matter-generating action. Residuals for the compact source are \(\sim10^{-11}\). The physical interior constraint remains at numerical roundoff, and the sourced energy estimate holds. These are **not** convergence claims for Weyl curvature or source-to-detector physics.

## D. Exact boundary obstruction — why global metric-constraint acceptance stays open

The weak SAT endpoints inject
\[
\boxed{\dot C_{h,0}
=\frac{(1+v)P_0-(1-v)M_0-2G}{\Delta y},
\qquad
\dot C_{h,N}=\frac{(1+v)P_N}{\Delta y}.}
\]
Even initially **globally constrained** data need not remain constrained at the two boundary nodes. At the exact original \(t=4/3\), choose \(U=y/2,\ P=1,\ M=0,\ G=0\); \(C_h=0\) at *every* node at \(T_0\). Yet the weak SAT generates \(\dot C_{h,0}=\dot C_{h,N}=(2/5)/\Delta y\). Direct actual-original-stage values are **10, 20 and 40** for \(\Delta y=.04,.02,.01\), while all interior \(\dot C_h=0\). This is an **instantaneous numerical counterexample to global exact constraint preservation**, not a long-time simulation or a physical gravity effect. It explains why full weak-SAT characteristic constraint propagation remains a separate open gate.

**Source:** \`scripts/ksw668_f8_weak_sat_constraint_no_go.py\`, six tests. **Agda source rational slice:** \`originalT43WeakWallConstraintNoGo\`, pinned kernel unrun. A viable final closure needs a boundary-compatible constraint-preserving SAT/penalty, or a uniform boundary residual-to-constraint estimate; first-order energy dissipation alone is insufficient.

## E. New exact *finite radial* high-order Sobolev hierarchy, with the ACTUAL compact TT emitter

For each original angular \(\ell\in\{0,2,4\}\), let \(A_\ell=-L_{3+2\ell}\), the positive conservative radial FV stiffness in the radial cell-volume norm. Because **all** original \(b(T),v(T),3/z\), weak SAT normal boundary operators and the first-order physical characteristic coefficients are independent of \(r\),
\[
\boxed{[A_\ell^k,\mathcal L_h]=0
\quad\text{for every }k\in\mathbb N,}
\]
where \(\mathcal L_h\) denotes the linear semidiscrete coupled generator, and the prescribed **nonzero** source is simultaneously transformed \(G\mapsto A_\ell^kG\). This is an exact finite-grid tensor-product operator commutation, not a continuum elliptic regularity theorem.

Therefore
\[
E_k(X):=E(A^kU,A^kP,A^kM)
\]
satisfies the **same** homogeneous coupled energy growth coefficient as \(E(X)\): \(5\) for weighted mode 4, \(5+16t\) for physical-constraint-preserving mode 3 under its spacing condition. Its sourced lift likewise commutes, with \(A^kF\) and the corresponding high-order forcing norm. The concrete producer runs actual original compact TT modal forcing and checks \(k=0,1,2,3\) in both normal modes on \(t=1,4/3,2,12\); maximum relative stage commutator residual **\(5.6\times10^{-16}\)** across these eight original cases.

Generic Agda source \`KSW668AdS5OriginalRadialSobolevPowerReuseExact.agda\` inductively proves all-power commutation from a supplied single-commutator premise; the concrete original operator equality is independently checked in Python, not pinned Agda-kernel accepted.

**Crucial limit:** powers of effective one-dimensional radial FV stiffness are **not a complete physical five-dimensional boundary \(H^{4+\epsilon}\) Sobolev trace**. The high-order norm of the actual compact source grows rapidly as its support width and grid size change. The missing proof must include mesh-uniform source regularity, normal/time derivatives, weak-Israel boundary compatibility and a *two-derivative pointwise* both-Weyl trace estimate.

## F. Updated exact gates and regression acceptance

| Max-cut gate | Status |
|---|---|
| \`ads5OriginalTTPhysicalInteriorCharacteristicConstraintRK3Exact\` | **MATH/FINITE STAGE CLOSED** — exact physical \(C_h\) interior for mode 3 at every moving SSPRK3 stage, including nonzero original source |
| \`ads5OriginalConstraintPreservingCoupledSBP2WeightedEnergy\` | **MATH/SEMIDISCRETE CLOSED** — \(E_3'\le(5+16t)E_3\), normal grid \(\Delta y\le b/4\) |
| \`ads5OriginalCompactTTConstraintPreservingForcedEnergy\` | **MATH/SEMIDISCRETE CLOSED** — actual compact source and \(E_3'\le(6+16t)E_3+\tfrac12\|F\|_E^2\), \(\Delta y\le b/4\) |
| \`ads5OriginalTTAllFiniteRadialSobolevPowersCommute\` | **MATH/FINITE RADIAL ALGEBRA CLOSED** — k=0..3 actual original operator checks and all-k induction, physically continuum high-order proof not implied |
| \`ads5OriginalWeakIsraelGlobalConstraintBoundaryWeld\` | **OPEN WITH EXACT NEGATIVE CONTROL** — global Cdot at wall/far scales as \(1/\Delta y\) on constrained test data |
| \`ads5OriginalMovingSBP3FullCoupledSSPRK3CFLAndError\` | **OPEN** — complete coupled RK3 energy amplification, time-dependent coefficients and uniform truncation estimate |
| \`ads5OriginalCompactTTFullH4PlusEpsilonNeumannBoundarySourceBudget\` | **OPEN** — mesh-uniform normal and radial high-order trace, true source action and compatibility |
| \`ads5OriginalMovingH4PlusEpsilonNeumannToBothWeylTrace\` | **OPEN** — pointwise intrinsic 4D and projected 5D Weyl error with calibrated constants |
| \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | **OPEN/NUMERICALLY FAILED** — original H and both Weyl, independently refined, outside bulk-cone leakage |
| \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` and \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | External-theorem original prescribed-source proof candidate; independent microlocal referee and Agda continuum acceptance **OPEN** |
| F9 original matter action, coupled mode stability/backreaction, separate doubled-disc cylinder | **OPEN** |
| F10 source/detector scaling, delay, attenuation, calibrated clocks | **OPEN** |
| F11 pinned Agda continuum/kernel and source-to-observation semantic weld | **OPEN** |
| D1 empirical independent graviton early-arrival observation | **OPEN** — cannot be closed by algebra/numerical simulation |

**Verification:** merged baseline plus maximum-cut VIII = **284** source-equivalent local F8 tests. IX adds **24** physical-characteristic/commutator/forced compact-source tests, **6** weak-SAT boundary no-go tests and **12** finite radial Sobolev tests, totaling **326 tracked source-equivalent local cases**. Independently rerun local source-equivalent suite: **326/326 PASS**. Exact connected PR-head smoke and pinned Agda 2.9 kernel remain **UNRUN**; FIO referee acceptance and empirical D1 remain **OPEN**.

**Next meaningful maximum cut:** use mode 3's exact interior characteristic propagation and the quantified weak-boundary counterexample to design a **constraint-compatible, energy-stable sourced Israel boundary treatment**; prove complete coupled SSPRK3 stability and a uniform high-Sobolev normal/time/physical both-Weyl receiver trace. The original independent FIO analytic route remains complementary.

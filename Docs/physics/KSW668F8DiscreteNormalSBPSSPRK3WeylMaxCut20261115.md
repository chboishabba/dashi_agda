# KSW668 F8 maximum cut VII — actual original normal-direction SBP/SSPRK3, radial CFL, and pointwise Weyl trace obstruction

**Date:** 15 November 2026. **Canonical owner:** Agda PR #1512. **Original physical model:** five-dimensional Poincaré AdS with moving \(a(t)=t\), \(b(T)=1/t\), \(v=b'(T)=-1/\sqrt{1+t^2}\), domain \(z\ge b(T)\), original sourced linear Israel tensor \(\mathcal B H=n\cdot\partial H=-6\pi^{TT}\). **No cross-model substitution.** The \(\ell=0,2,4\) multipoles retain physical **three-dimensional** brane spatial geometry; their effective radial dimensions \(d=3,7,11\) are conjugate numerical coordinates.

## A. Radial-only SSPRK3 CFL — actual original \(d=11\) counterexample to the old input guard

The exact conservative radial FV shell-volume operator \(L_d\), already repaired in maximum cut VI, is selfadjoint nonpositive in the weighted cell-volume space. For a frozen **pure radial wave subsystem** \(\partial_TU=V,\partial_TV=L_dU\) with homogeneous far radial Dirichlet boundary, each positive stiffness eigenvalue \(\lambda\) gives mode pair \(\pm i\sqrt{\lambda}\).

For three-stage SSPRK3, the stability polynomial is \(R(z)=1+z+z^2/2+z^3/6\). The new generic rational Agda source lemma \`KSW668AdS5RadialSSPRK3ImaginaryPolynomialExact.agda\` proves the polynomial identity, and independent SymPy confirms
\[
\boxed{|R(i\xi)|^2-1=\frac{\xi^4(\xi^2-3)}{36}.}
\]
Therefore each **pure radial** mode has non-increasing energy exactly when \(\Delta T\sqrt{\lambda}\le\sqrt3\). Gershgorin on the weighted-symmetric negative radial stiffness matrix bounds \(\lambda_{\max}\le2\max_j(-L_{d,jj})\), providing a rigorous sufficient radial-only CFL. Across original modes \(d=3,7,11\), the sufficient ratios \(\Delta T/\Delta r\) are \(0.500000,\ 0.3273268,\ 0.26111648\). On a representative \(50\)-active-cell radial problem, the actual modal limits are \(0.6864363,\ 0.4627503,\ 0.3692729\). **Old solver validation permitted \(\Delta T/\Delta r<0.45\)**, which fails even this radial-only d11 mode: its one-step energy amplification is approximately **1.802185** at that ratio. The original solver now **rejects** any requested \(\Delta T/\Delta r\ge\sqrt{3/44}\), a safe radial-subsystem restriction. It still does NOT prove the full \((T,y,r)\) moving-warp/Neumann/SSPRK3 scheme stable.

**New producer and tests:** \`ksw668_f8_ssprk3_radial_cfl.py\`, 13 tests. **Formal owner:** \`KSW668AdS5RadialSSPRK3ImaginaryPolynomialExact.agda\`; pinned Agda kernel **not run**.

## B. Original AdS5 linear-wave NO-GO: finite first-order energy does not control pointwise electric Weyl

A genuine original five-dimensional bulk solution can have frequency-independent first-order bulk energy and unbounded **intrinsic four-dimensional electric Weyl**. For this counterexample only, take the **periodic three-torus** brane spatial domain (NOT the compact \(\mathbb R^3\) physical source), and set
\[
H_N(T,z,x)=N^{-1}\sin(Nx)\cos[N(T-T_*)],\quad N\in\mathbb N_{>0}.
\]
The original \(\mathcal L=-\partial_T^2+\partial_z^2-3z^{-1}\partial_z+\Delta_{\mathbf x}\) annihilates each \(H_N\) exactly. The **actual moving Israel Neumann datum** is \(G_N=bvH_{N,T}/\sqrt{1-v^2}\), with inward unit normal, not a substituted stationary boundary law.

The weighted bulk first-order energy on a \(2\pi\)-periodic \(\mathbb T^3\), integrated over the original normal half-line \(z\in[b,\infty)\), is
\[
E_N(T)=\frac12\int_{T^3}\int_b^\infty z^{-3}
 (|H_{N,T}|^2+|\partial_xH_N|^2)\,dz\,d^3x
=\boxed{\frac{\pi^3}{b(T)^2}}
\]
independent of \(N\). On the original \(t=2,T=T_*\) receiver slice, the intrinsic electric-Weyl expression used by the exact same F8 receiver gives
\[
\boxed{|E^{(4)}_{yy}(x=\pi/(2N))|=\frac{9N}{64}\to\infty.}
\]
Hence **NO uniform bound of pointwise two-derivative Weyl curvature by this first-order energy exists**. The existing sourced Neumann energy estimate and its \(2\sqrt5\) wall flux alone can never certify the numerical curvature extraction. A sufficient regularity target is a localized higher-order estimate (e.g. bulk spatial \(H^{4+\epsilon}\) controlling a two-derivative pointwise trace in spatial dimension four), with compatible time derivatives/boundary regularity and a **source-to-receiver** transfer constant. This does **not** refute the microlocal existential compact-source FIO proof candidate; it precisely identifies why its proof must not be replaced by \(H^1\) numerical-energy reasoning.

**New exact symbolic producer:** \`ksw668_f8_original_energy_weyl_trace_no_go.py\`, 10 committed tests.

## C. Exact original moving Neumann first-order normal SBP — legacy stencil counterexample

For \(q_\pm=P,M\), \(P_{\rm far}=0\) and \(M_{\rm wall}=\beta P_{\rm wall}-2G/(1-v)\), \(\beta=(1+v)/(1-v)\), the **first-order** correct upwind derivatives give a finite-grid identity:
\[
\boxed{
2\Delta y\,Q=
F_{\rm wall}
-(1+v)\sum_j(P_{j+1}-P_j)^2
-(1-v)\sum_j(M_{j+1}-M_j)^2
-(1-v)M_{\rm far}^2,
}
\]
where \(Q=(1+v)\sum P D_+P+(v-1)\sum M D_-M\) and \(F_{\rm wall}=(1-v)M_{\rm wall}^2-(1+v)P_{\rm wall}^2\le2\sqrt5\,G^2\). Therefore for \(G=0\), \(Q\le0\) **at every finite normal grid**. The new Agda source \`KSW668AdS5MovingNormalFiniteSBPTelescopeExact.agda\` gives generic rational finite-list forward/backward discrete summation-by-parts telescopes, imported into the KSW canonical Agda rollup. The pinned Agda kernel remains unrun.

The **old second-order one-sided derivative with first-order remote closure** is *not* dissipative: the exact homogeneous 16-node outgoing integer vector
\[
P=(0,0,-1,-2,-2,-1,1,4,10,19,30,41,51,53,40,0)
\]
satisfies \(\sum P D^{\rm legacy}_+P=\boxed{277/2>0}\) at \(\Delta y=1\), with zero outer inflow. This is an exact numerical-scheme counterexample, not a counterexample to the continuum physical AdS5 PDE. The solver now exposes \`normal_order=1\` as a source-equivalent first-order SBP comparator; historical \`normal_order=2\` remains the default for reproducible legacy receipts.

## D. Fully discrete normal-only forced SSPRK3 energy closes

For first-order upwind normal transport, set \(h=\Delta T/\Delta y\), \(\alpha=(1+v)h\), \(\gamma=(1-v)h\). If
\[
0\le h\le\frac1{1+1/\sqrt2}=2-\sqrt2\approx0.58578644,
\]
both characteristic forward-Euler stages are convex nearest-neighbor averages. The original moving Israel \(\beta\) makes their **combined** squared characteristic norm satisfy
\[
\|FE_{t,G}X\|^2\le\|X\|^2+hF_{\rm wall}
\le\|X\|^2+2\sqrt5\,h\|G\|^2.
\]
The standard SSPRK3 convex stage composition with actual stage times \(T,T+\Delta T,T+\Delta T/2\) then yields the exact **normal-only fully discrete forced** estimate
\[
\boxed{\|X_{n+1}\|^2\le\|X_n\|^2+
2\sqrt5\,h\left(\frac{\|G_n\|^2}{6}
+\frac{2\|G_{n+1/2}\|^2}{3}
+\frac{\|G_{n+1}\|^2}{6}\right).}
\]
The existing normal-step input ratio \(\Delta T/\Delta y<0.45\) fits this **normal-only** CFL. Producers \`ksw668_f8_normal_sbp_upwind.py\` (12 tests) and \`ksw668_f8_normal_ssprk3_energy.py\` (13 tests) verify finite-grid forced/homogeneous and over-CFL controls. The radial and normal subsystem theorems **do not automatically imply** the full unsplit moving warped SSPRK3 operator stable.

## E. Second-order SBP–SAT weak physical Neumann boundary — retained accuracy, controlled energy

A superior accuracy candidate uses a diagonal summation-by-parts norm \(H=\mathrm{diag}(\Delta y/2,\Delta y,\dots,\Delta y,\Delta y/2)\), centered interior derivative and first-order edge derivatives, satisfying \(\boxed{2\langle U,DU\rangle_H=U_{\rm far}^2-U_{\rm wall}^2}\) exactly.

With the **physical original Israel target** \(M_*=\beta P_0-2G/(1-v)\) and \(P_{{\rm far},*}=0\), add SAT penalties at the two inflow faces:
\[
\dot P=(1+v)DP-\frac{1+v}{H_{\rm far}}P_{\rm far}e_{\rm far},\qquad
\dot M=(v-1)DM+\frac{1-v}{H_{\rm wall}}(M_*-M_0)e_{\rm wall}.
\]
The original semidiscrete normal quadratic energy then satisfies the **exact** identity
\[
\boxed{\dot E_H=F_{\rm wall}
-(1+v)P_{\rm far}^2
-(1-v)M_{\rm far}^2
-(1-v)(M_0-M_*)^2
\le2\sqrt5\,|G|^2.}
\]
This is **weak enforcement** of Neumann data: \(M_0\) need not equal \(M_*\) on any finite grid. \`scripts/ksw668_f8_tt_multipole.py\` now supports \`normal_order=3\` (SBP2–SAT) alongside first-order \`1\` and historical \`2\`. The manufactured original bulk polynomial \`H_d=dT^2+r^2\` passes all three stencil modes and their corresponding physical Israel source, while source-to-receiver convergence is explicitly unproved. Producer \`ksw668_f8_normal_sbp2_sat.py\` and 13 tests provide independent normal-only algebra/energy acceptance.

**Do not claim complete RK3 SAT energy:** centered SBP2 is dissipative in the continuous semidiscrete norm with SAT penalties, but an explicit RK stability proof for the **full (time-dependent, radial, warp, normal) coupled** operator is still a separate analytic gate.

## F. Actual three-normal-scheme original t12 numerical comparison — ALL fail receiver

The original spatially compact TT source (\(\epsilon=.04\)), same Poincaré pulse (.065), exact \(t=12\) photon-dark receiver, source cell primitives and exact shell radial FV, and **two** mesh pairs \((\Delta r,\Delta y,\Delta T)=(.012,.016,.00249922435),(.008,.012,.00179891049)\) were compared.

| Normal scheme | \(H_{yy}\) coarse | \(H_{yy}\) medium | medium-relative tensor drift | intrinsic Weyl drift | projected Weyl drift |
|---|---:|---:|---:|---:|---:|
| Legacy order2 strong | \(-2.83814e-6\) | \(-6.76190e-6\) | 58.0% | 10.5% | 19.1% |
| SBP1 order1 strong | \(+3.33579e-6\) | \(+2.55655e-7\) | **1204.8%** | 13.9% | 48.3% |
| SBP2–SAT order3 weak | \(-5.13979e-6\) | \(-6.21638e-6\) | **17.3%** | **140.0%** | 26.0% |

Outside the bulk causal front, numerical field and Weyl values are still nonzero in all three schemes. **None passes three-grid, source-to-Weyl, boundary or physical acceptance.** The full SBP1 finest-resolution run exceeded a bounded execution window, so the new methods have **only two-grid receipts**, not invented three-grid receipts. **The legacy corrected three-grid negative receipt is preserved**.

Machine comparator: \`Artifacts/ksw668/ads5_f8_three_normal_schemes_SBP_comparison_20261115.json\`; \`scripts/ksw668_f8_normal_operator_comparison.py --reproduce\` intentionally returns status **42** after producing a non-promoted two-grid receipt. The option is \`scripts/check_ksw668_f8_maxcut.sh --normal-compare\`.

## G. Exact remaining lemma/phase ledger — prioritized for next large mathematical cut

| Gate | Status / exact acceptance |
|---|---|
| \`ads5OriginalRadialFiniteVolumePureWaveSSPRK3CFLExact\` | **Closed math** by exact RK polynomial, weighted-symmetric radial spectral bound, negative large-step witness; pinned Agda kernel OPEN |
| \`ads5OriginalMovingNormalFirstOrderFiniteSBPTelescope\` | **Closed math**, generic finite-grid rational Agda source written; pinned Agda kernel OPEN |
| \`ads5OriginalMovingNeumannNormalFullyDiscreteSSPRK3ForcedEnergy\` | **Closed math normal-only**, original-stage source weights and \(2-\sqrt2\) CFL; full bulk OPEN |
| \`ads5OriginalMovingNormalSecondOrderSBPSATForcedEnergy\` | **Closed math semidiscrete normal-only**; actual original wall **weak SAT**; full explicit RK3 spectrum OPEN |
| \`ads5OriginalFirstOrderEnergyNotEnoughForPointwiseWeyl\` | **Closed exact counterexample on periodic original AdS5**, periodic source **NOT** compact original FIO emitter |
| \`ads5OriginalMovingFullCoupledYRadialSSPRK3SymmetrizerCFL\` | **OPEN**, need actual weight \(z^{-3}\), radial FV, full normal and moving coefficients, SAT/outer source, SSPRK3 spectral or energy inequality and proof of uniform constants |
| \`ads5OriginalMovingH4PlusEpsilonNeumannToBothWeylTrace\` | **OPEN**, compatible high-order source/normal trace and actual curvature error; H1 cannot substitute |
| \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | **OPEN**, actual three-grid original compact H/E4/E5 and outside-cone error remains failed |
| \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\`, \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | External-theorem-dependent prescribed-source microlocal **proof candidate**, independent mathematical/referee/Agda acceptance OPEN |
| F9 physical brane matter source action, all-mode stability/backreaction and separate doubled-disc cylinder retarded physics | **OPEN** |
| F10 physical scales, source timing, attenuation, detector transfer, calibrated clock | **OPEN** |
| F11 pinned Agda 2.9 continuum/energy/FIO kernel and actual observation semantics | **OPEN** |
| D1 replicated independent physical early gravitational signal | **OPEN**; mathematical code cannot substitute experimental evidence |

**Verification/ownership:** prior **184** distinct committed-source-equivalent cases plus 13 radial modal CFL, 10 original Weyl no-go, 12 first-order normal SBP, 13 forced SSPRK3, 13 SBP2–SAT, 5 normal comparator, and 5 additional existing manufactured/multipole assertions = **255/255 committed-source-equivalent regression cases**. The broader local selection including 13 pre-existing exploratory prepotential cases and an additional local trace check passed **269/269**; that broader set is NOT advertised as exactly the connected GitHub-head runner. Pinned Agda kernel and actual exact-connected-PR checkout not run. The actual original two-grid normal comparisons were executed locally from source-equivalent versions. None passes the full F8 numerical/physical gate.

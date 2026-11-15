# KSW668 F8 maximum cut VIII — full original moving AdS₅ coupled weighted SBP–SAT energy and compact Neumann source lift

**15 November 2026.** Follow-on to **merged** [PR #1512](https://github.com/chboishabba/dashi_agda/pull/1512), on a fresh branch based on current \`master\`. The original independent prescribed-source FIO proof Markdown \`Docs/physics/KSW668F8OriginalT2NeumannFIOProof20261115.md\` remains committed in the merged baseline. This report adds a genuinely *coupled* moving-boundary finite-volume / summation-by-parts energy theorem and its explicitly sourced version. It does **not** assert a gravitational detection, fully discrete SSPRK3 stability, actual Weyl receiver convergence, complete original FIO referee acceptance, or pinned Agda 2.9 acceptance.

## 1. Preserve the original physical equations

Five-dimensional Poincaré AdS:
\[
ds_5^2=z^{-2}(-dT^2+dz^2+dx_1^2+dx_2^2+dx_3^2),\quad
z\ge b(T)=1/t,\quad
v=b'(T)=-1/\sqrt{1+t^2}.
\]
For each exact TT angular multipole \(\ell=0,2,4\), after conjugating \(H_\ell=r^\ell V_\ell\), the effective **numerical** radial dimension is \(d=3+2\ell=3,7,11\), but the physical brane remains three-dimensional. Define \(P=H_T+H_z\), \(M=H_T-H_z\), \(y=z-b(T)\), and \(a=(1+v)/2,\ c=(1-v)/2\). The physical original linear tensor equations are
\[
\begin{aligned}
U_T &=aP+cM,\\
P_T &=(1+v)P_y+\Delta_dU-\tfrac3{2z}(P-M),\\
M_T &=(v-1)M_y+\Delta_dU-\tfrac3{2z}(P-M).
\end{aligned}
\]
At \(y=0\), the ORIGINAL sourced tensor Israel Neumann condition is
\[
(1+v)P_0+(v-1)M_0=2G,
\quad M_*=\frac{1+v}{1-v}P_0-\frac{2G}{1-v}.
\]
At finite normal boundary, outgoing \(M_N\) is not reset; incoming \(P_N=0\) is weakly enforced by SAT. At the radial outer numerical boundary, use homogeneous Dirichlet cells for \(U,P,M\).

## 2. Exact AdS-weighted normal SBP operator, not a formal continuum substitution

Let \(w(y,T)=z^{-3}\), \(z=b(T)+y\), and \(D\) be the second-order diagonal-norm normal SBP derivative with trapezoidal \(H_y\):
\[
\langle f,Df\rangle_{H_y}=\tfrac12(f_N^2-f_0^2).
\]
The new \`normal_order=4\` option in the **actual original** \`scripts/ksw668_f8_tt_multipole.py\` uses the weighted *split form*
\[
\boxed{D_w f=w^{-1/2}D(w^{1/2}f)+\frac3{2z}f.}
\]
The added lower-order coefficient restores consistency with \(f_y\), since \(w_y/(2w)=-3/(2z)\). The weighted discrete integration identity is **exact at every finite grid**:
\[
\boxed{\langle f,D_w f\rangle_{H_y w}=
\tfrac12(w_Nf_N^2-w_0f_0^2)
+\Big\langle \tfrac3{2z}f^2,1\Big\rangle_{H_y w}.}
\]
For the radial operator use **exact shell volumes** \(V_j=(r_{j+1/2}^d-r_{j-1/2}^d)/d\). Its existing Green identity is \(\langle U,\Delta_{d,h}U\rangle_{V_r}=-\|\nabla_r U\|^2_{V_r}\), including the effective 11D mode. The new numerical owner independently checks these matrix symmetries, the exact weighted boundary identity and second-order normal *interior* consistency. The original strong boundary modes \`normal_order=1,2\` and unweighted weak-SAT \`normal_order=3\` are preserved unchanged as historical comparisons.

## 3. Complete homogeneous *coupled* semidiscrete energy (stronger than two separate energy lemmas)

Use the **compatible** moving symmetrizer
\[
\boxed{E(T)=\tfrac12\sum_{y,\ell}H_y\,w\,
\left(a\|P\|_{V_r}^2+c\|M\|_{V_r}^2
          +\langle U,-\Delta_{d,h}U\rangle_{V_r}\right).}
\]
Its radial terms cancel **exactly** with the \(aP+cM\) evolution of \(U\). The wall SAT and incoming far SAT produce the exact homogeneous negative boundary squares. Using \(w_T/w=-3v/z\) and \(v_T=t^3/(1+t^2)^2\), the warp and time-dependent weight simplify exactly, **with no discarded terms**:
\[
\boxed{\begin{aligned}
E'={}&-\frac{w_0}{4}\sum_\ell
 \big\|(1+v)P_0-(1-v)M_0\big\|_{V_r}^2\\
&-\frac{w_N}{4}\sum_\ell
 \big[(1+v)^2\|P_N\|_{V_r}^2+(1-v)^2\|M_N\|_{V_r}^2\big]\\
&+\sum_y H_y w\sum_\ell\left[
 \frac{3v}{2z}\left(\langle P,M\rangle_{V_r}
 -\langle U,-\Delta_{d,h}U\rangle_{V_r}\right)
 +\frac{v_T}{4}\left(\|P\|_{V_r}^2-\|M\|_{V_r}^2\right)
 \right].
\end{aligned}}
\]
The central exact scalar identity is
\[
\frac3{2z}\left[
a(1+v)P^2+c(v-1)M^2-(aP+cM)(P-M)
-v(aP^2+cM^2+R)\right]
=\frac{3v}{2z}(PM-R).
\]
This algebra and the wall square have new rational Agda **source-only** lemmas in \`DASHI/Physics/Gravity/KSW668AdS5OriginalCoupledSBPSymmetrizerRationalExact.agda\`. The complete finite-grid matrix energy identity is independently checked with the actual normal-order-4 Numba stage, so it is not an untested interface postulate.

**Uniform original physical interval \(t\ge1\)** (including original \(t=2\) analytic receiver and \(t=12\) numerical controls):
\[
\frac{3|v|}{2z}\le\frac32,\qquad
\frac{3|v|}{4z\sqrt{ac}}\le\frac32,\qquad
0\le\frac{v_T}{4a}<1.
\]
Since \(R=\langle U,-\Delta_{d,h}U\rangle_{V_r}\ge0\) after radial summation and \(2\sqrt{ac}|PM|\le aP^2+cM^2\), the identity yields **mesh-independent**
\[
\boxed{E'(T)\le5E(T),\qquad E(T)\le e^{5(T-T_0)}E(T_0).}
\]
The bound is for the *homogeneous semidiscrete system* built from the specified SBP2 split operator, SAT and exact radial FV; it does not prove the explicit SSPRK3 amplification bound of the **coupled** system.

## 4. The nonzero original Israel source: exact boundary obstruction and real semidiscrete lift

For nonzero prescribed \(G\), the coupled energy wall contribution becomes
\[
\boxed{-\frac{w_0}{4}\|(1+v)P_0-(1-v)M_0\|_{V_r}^2
-w_0(1-v)\langle M_0,G\rangle_{V_r}.}
\]
**Do not silently import** the former normal-only \(\le2\sqrt5\|G\|^2\) boundary flux into this differently weighted coupled symmetrizer. For fixed \(G=1\), choosing \(M_0=\beta P_0\) and \(P_0=-N/(1+v)\) makes this wall work \(+Nw_0\), disproving any pure uniform \(C\|G\|^2\) wall term independent of state. A source lift or compatible normal trace is essential.

The new **algebraic characteristic** lift in the first-order state space (not a physical H-only matter action) is
\[
\Lambda_U=\Lambda_P=0,\qquad
\Lambda_M=-\frac{2G(T,r)}{1-v(T)}\chi(y),
\quad \chi(0)=1,\quad \chi\in C_c^\infty([0,\infty)).
\]
It exactly removes the sourced term from the weak SAT target of \(\widetilde X=X-\Lambda\). The transformed bulk forcing is
\[
\boxed{\begin{aligned}
F_U&=c\Lambda_M,\\
F_P&=\frac{3\Lambda_M}{2z},\\
F_M&=(v-1)D_w\Lambda_M+\frac{3\Lambda_M}{2z}
       -\partial_T\Lambda_M.
\end{aligned}}
\]
Importantly, the energy norm \(\|F\|_E^2\) contains \(\|\nabla_rF_U\|^2\), not just \(\|G\|^2\). For smooth resolved compact original TT source data and their \(T\)-derivatives, this norm is finite on each finite grid. By Cauchy–Schwarz/Young,
\[
\boxed{\widetilde E'(T)\le6\widetilde E(T)
+\tfrac12\|F(T)\|_E^2,}
\]
hence
\[
\boxed{\widetilde E(T)\le
e^{6(T-T_0)}\widetilde E(T_0)+
\tfrac12\int_{T_0}^T e^{6(T-S)}
\|F(S)\|_E^2\,dS.}
\]
This is a **full coupled nonhomogeneous semidiscrete energy estimate** for the specified original 3-mode discretization, not an analytic uniform-in-grid bound on the source derivatives and not a fully discrete RK3/curvature theorem. The source lift does **not** assert that arbitrary lifted state triples are an independent scalar metric perturbation; the original physical \(P,M,U\) constraint propagation with weak SAT remains a separate gate.

The executable \`scripts/ksw668_f8_full_coupled_source_lift.py\` subtracts the lift from the **actual sourced** semidiscrete RHS, checks the new forcing in every component, and evaluates the full energy source-work pairing on original \(t=1,4/3,2,12\) slices. This is an actual operator check, not solely symbolic manipulation.

## 5. Original compact TT receiver numerical negative control — new mode 4

One **actual** original \(t=12\) compact TT spatial radius 0.04 / source Poincaré pulse 0.065, same photon-dark receiver event, was run with both original coarse and medium radial/normal/time discretizations using \`normal_order=4\`. Source cells retain the exact compact TT primitive-moment check.

| Observable | Coarse | Medium | coarse/medium drift relative to medium |
|---|---:|---:|---:|
| \(H_{yy}\) | −5.4591942e−6 | −6.2951421e−6 | **13.28%** |
| Intrinsic \(E^{(4)}_{yy}\) | −6.8123758e−5 | −2.6411758e−5 | **157.93%** |
| Projected \(E^{(5)}_{yy}\) | −2.8751354e−6 | −2.1828310e−6 | **31.72%** |

Medium-grid beyond-bulk-cone ratios are 2.07% for the field, 4.38% for intrinsic Weyl and 1.73% for projected Weyl, all nonzero. **The corrected coupled-energy structure does not certify numerical early reception.** Only TWO grids completed for new mode 4; the legacy three-grid failed receipt is preserved. There is no independent error-bound, full coupled RK3 stability, continuum trace or physical observation. Receipt \`Artifacts/ksw668/ads5_f8_full_coupled_weighted_SBP4_maxcut_20261115.json\`.

## 6. Acceptance and exact remaining lemmas

**Locally verified:** baseline from merged PR #1512 plus 29 new source-equivalent unit tests yields **284/284 local replay PASS** when the old invalid-mode test is updated to reject mode 5 rather than the newly valid mode 4. Exact connected GitHub PR-head runner and **pinned Agda 2.9 kernel were NOT run**. The previous standalone Neumann/FIO proof remains present and updated in merged \`master\`.

| Gate | Disposition |
|---|---|
| \`ads5OriginalMovingAdSWeightedSBP2SATCoupledHomogeneousEnergy\` | **MATHEMATICS/SEMIDISCRETE CLOSED**: exact finite-grid identity, original t>=1 uniform E'<=5E, actual Numba operator equality, Agda generic polynomial source only |
| \`ads5OriginalMovingCharacteristicSourceLiftCoupledForcedEnergy\` | **MATHEMATICS/SEMIDISCRETE CLOSED**: exact sourced weak-Israel lift and E_tilde'<=6E+0.5||F||²; source derivative regularity explicit |
| \`ads5OriginalMovingSBP4SATFullyDiscreteSSPRK3CFLAndTruncationError\` | **OPEN**: full coupled time integration, characteristic constraint and outer boundary, uniform original source error |
| \`ads5OriginalMovingCompactTTCharacteristicLiftUniformSobolevSourceBudget\` | **OPEN**: physically compatible H-only source and mesh-uniform high-order original source estimates |
| \`ads5OriginalMovingH4PlusEpsilonNeumannToBothWeylTrace\` | **OPEN**: pointwise two-derivative intrinsic/projected Weyl trace, boundary regularity and explicit source-to-receiver error |
| \`ads5OriginalMovingTTThreeMultipoleThreeObservableConvergence\` | **OPEN**: 3 independently varied meshes field/E4/E5 and outside-cone suppression, new mode4 currently FAILS |
| \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\`, \`ads5OriginalT2ActualCompactTTNonzeroEarlyBothWeyl\` | **OPEN for independent original FIO microlocal theorem/referee acceptance**; committed prescribed-source theorem-application candidate retained |
| F9 generating matter action, all-mode/coupled backreaction, distinct doubled-disc cylinder | **OPEN** |
| F10 original physical scale, attenuation/source lag/detector calibration | **OPEN** |
| F11 pinned Agda 2.9 continuum kernel and source/observation semantic weld | **OPEN** |
| D1 controlled independent physical gravitational observation | **OPEN** — not a software theorem |

**Next strongest cut:** a *fully discrete* source-lifted SBP4 SAT/RK3 stability plus a mesh-independent \(H^{4+\epsilon}\) physical Weyl boundary trace bound. Without these, no amount of passing source-level algebra or a nonzero uncoupled receiver value warrants promotion. The original prescribed-source FIO paper candidate remains a complementary *analytic* route.

# Source-complete LOCAL electroweak Higgs vacuum on the selected E6-derived orbifold

**IMPORTANT 2026-10-25 CORRECTION — ZERO-MODE-TRUNCATION ONLY:** The 36-real gradient and 18-even Hessian in this document are taken for the INTEGRATED spatially constant four-dimensional effective potential. They are NOT a solution to the separate five-dimensional interior E-L equations and fixed-plane Robin conditions. At the reported t=0.0246, the bulk t-force is +0.147406469832 and does not vanish. See the new physical owner [KKE6OrbifoldIntervalBoundaryELMaxCut20261025.md](KKE6OrbifoldIntervalBoundaryELMaxCut20261025.md) and executable `check_kk_e6_orbifold_interval_higgs_bvp.py` for a nonconstant dimensionless interval solution and its strict physical-normalization limits. The old 7+11 even Hessian count remains a correct claim about that HOMOGENEOUS TRUNCATION, not a complete 5D scalar-stability proof.

2026-10-25. Canonical [KK PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241); original 2-VEV source [first-Tits E6 PR #1106](https://github.com/chboishabba/dashi_agda/pull/1106). This is **TREE-LEVEL LOCAL** Hessian research, not an anomaly-safe full E6/SM theory, complete five-dimensional spectral vacuum, or numerical prediction of observed Higgs parameters.

## Original exact first-Tits source and a gauge-allowed new boundary term

Existing \`DASHI/Physics/Closure/Ternary27TrinificationInvariantTwoVEVPotentialExact.agda\` already owns the six-invariant positive two-bifundamental potential \`V6(Phi,Chi)\`. On the original \`Phi=E32\`, \`Chi=E33\` vacuum, a source-selected orbifold-even \(SU2_L\) doublet with hypercharge \(+1/2\) is \(\Chi_{21}\). The **exact** one-parameter restriction is
\[
V_6(E_{32},E_{33}+tE_{21})=3t^2+t^4.
\]
Therefore the ORIGINAL source, unchanged, positively penalizes this direction and **does not** produce electroweak breaking. Merely listing an even Higgs doublet was insufficient.

Under the actual orbifold \(P_L=P_R=\operatorname{diag}(-,-,+)\) with intrinsic Phi odd and Chi even, the two-by-two top-left complex matrix \(\Chi_{2\times2}\) is EVEN. Let \(P_2=\operatorname{diag}(1,1,0)\). The **boundary-restricted gauge symmetry** is \(SU2_L×U1_L×SU2_R×U1_R\); the projector commutes with its gauge action. Hence a localized interaction
\[
V_{\rm bdry}=-\mu^2\,\mathrm{tr}(P_2\Chi P_2\Chi^\dagger)
+\lambda_{\rm b}\,[\mathrm{tr}(P_2\Chi P_2\Chi^\dagger)]^2
\]
is invariant under this **reduced fixed-plane** group. It is NOT invariant under the entire bulk SU3L×SU3R, so it must genuinely be a boundary source with physical interval/boundary action, not a freely inserted bulk potential. Physical field dimensions and delta(y) normalization must be supplied before comparison to observed Higgs masses.

Along the original restricted path \(\Chi=E_{33}+tE_{21}\),
\[
V_{\rm total}=(3-\mu^2)t^2+(1+\lambda_{\rm b})t^4,
\qquad t^2=\frac{\mu^2-3}{2(1+\lambda_{\rm b})}
\]
at a nonzero restricted stationary point when \(\mu^2>3,\lambda_{\rm b}>-1\). **That original slice alone is NOT a full vacuum**, because the old E32/E33 amplitudes have nonzero gradients at \(t\neq0\).

## Correct full stationary branch of the 36-real scalar source

Allow BOTH original VEV amplitudes to respond:
\[
\Phi=a E_{32},\qquad
\Chi=bE_{33}+tE_{21},\qquad a,b,t\in\mathbb R.
\]
The ACTUAL matrix source potential restricted to this three-real-parameter family is exactly
\[
\begin{aligned}
V_6={}& a^4 +a^2t^2-2a^2
+b^4+4b^2t^2-2b^2+t^4-2t^2+2,\\
V_{\rm total}={}&V_6-\mu^2t^2+\lambda_{\rm b}t^4 .
\end{aligned}
\]

For nonzero a,b,t, the full three-coordinate stationary equations give
\[
a^2=1-\frac{t^2}{2},\qquad
b^2=1-2t^2,\qquad
\mu^2=3+\left(2\lambda_{\rm b}-\frac{13}{2}\right)t^2.
\]
Thus with \(\lambda_{\rm b}=4\), \(t=0.0246\), choose
\[
\mu^2=3.00090774,\quad
a=0.9998486985539362,\quad
b=0.9993946567797929.
\]
These are SOURCE-SELECTED dimensionless trial values. If one *illustratively* chooses \(v_{\rm high}=10\,\mathrm{TeV}\) and identifies \(t\,v_{\rm high}=246\,\mathrm{GeV}\), the numbers reproduce an electroweak *scale ratio*, not actual Standard Model W/Z or Higgs masses/couplings, nor a derivation of 246 GeV.

**A stronger independent automatic-differentiation test** \`scripts/check_kk_e6_orbifold_boundary_higgs_hessian.py\` uses the literal original six-invariant V6, the actual projector boundary interaction and **ALL 36 REAL fluctuations** \(\Re\Phi,\Im\Phi,\Re\Chi,\Im\Chi\) to evaluate the full gradient/Hessian. At that selected stationary point the maximum absolute gradient is \(\approx8.9\times10^{-16}\), i.e. all 36 classical Euler–Lagrange first variations vanish for homogeneous scalar configurations. This is beyond simply solving the three-coordinate path.

## The decisive parity-projected Hessian distinction

The ORIGINAL two complex bifundamentals contain 36 real bulk scalar components, but on the physical S1/Z2 orbifold:
- \(\Phi\) has intrinsic parity ODD. Only the 4 complex components with opposite L/R \(\mathbb Z_2\) entries are even → **8 REAL constant zero-mode scalar components**.
- \(\Chi\) has intrinsic parity EVEN. Only its \(2\times2\) top-left block (4 complex) and E33 (1 complex) are even → **10 REAL scalar zero-mode components**.
- Hence the actual **parity-even scalar zero-mode consumer has 18 REAL dimensions**, not the old 36. The remaining 18 are orbifold-odd and have no constant 4D zero modes.

The complete unconstrained 36×36 source Hessian has **2 negative, 11 near-zero and 23 positive** numerical eigenvalues, and its even–odd mixed block is exactly zero to floating precision. Projecting to the correct **18×18 orbifold-even Hessian** gives:
\[
\boxed{0\text{ negative},\quad7\text{ gauge zero modes},\quad11\text{ strictly positive}.}
\]
The smallest positive selected even-mode eigenvalue is **0.00362163040251646** in the dimensionless source potential normalisation. This exactly matches **8 parity-even L/R gauge generators → 1 unbroken photon**, hence 7 Goldstone directions. The exact source neutral mass Gram (separate \`check_kk_e6_gs_photon_rank.py\`) has rank 3 of 4 with \(Q=T3_L+Y\), supporting the group interpretation of these zero modes.

The 2 negative Hessian directions are in the **18-dimensional ORBIFOLD-ODD** scalar sector, so they cannot be used as constant zero-mode destabilisations. **This does NOT prove stability of the full five-dimensional interval theory:** the odd sine/Kaluza–Klein tower must be included with its positive \(y\)-gradient, boundary conditions and physically dimensionful kinetic source; the global scalar potential and all loop contributions also need checking. No false promotion of a 36D saddle to a physical 4D vacuum, and no false rejection of the actual orbifold-even vacuum.

## Relation to the Green–Schwarz, chiral 16 and Casimir critical path

The local scalar construction is compatible with the SOURCE-SPECIFIC orbifold chirality (16 LH SM-generation-like + 10R+1R SM-vectorlike), and the photon generator remains \(Q=T3_L+Y\) with no independent old Maxwell U1B. It does NOT remove the pre-VEV UV orbifold gauge anomaly. A separate \`KKE6OrbifoldGreenSchwarzPhotonSourceMaxCut20261025.md\` now proves the LOCAL UV anomaly factorisation along \(F_L-F_R\) and maps an E33 Goldstone/axion WZ possibility with a still-unpaid global mod-2 charge-lattice issue. This Green–Schwarz action, if actually sourced, alters quantum physics and fixed-plane stress.

**Next actual physical obligations, in priority order:**
1. Localised GS/two-form global spin/quotient periodicity and fixed-point anomaly consistency, without removing the chiral 16.
2. Gauge/fermion Yukawa source for exotic 10R+1R and observed SM masses; all relevant gauge and scalar masses and couplings, without extra photon.
3. Dimensionful five-dimensional BOUNDARY scalar action, correct odd-mode KK tower, global 18-real scalar vacuum, full gauge ghost/Goldstone regulator, radiative stability of the small E21 Higgs VEV.
4. Proper orbifold one-loop interval Casimir and SOURCE metric path \(\delta S/\delta G_{MN}\) using existing QFT stress compiler #1165; same-action radion/Wilson/VEV vacuum and fifth pressure \(T55\).
5. Empirical source-bound weak field, rotating Earth, PPN and LARES tests. The prior smooth-S1 D>409 negative control is not an orbifold prediction.

**Evidence/attribution:** Source six-invariant potential and E6 VEVs originally from #1106, source orbifold choices and new fixed-plane interaction #1241, all external group/anomaly physics credited to Slansky (1981) and original orbifold anomaly papers. Local exact SymPy potential derivatives and independent PyTorch 36×36 real Hessian on CPU passed; new script committed and GitHub head verified separately. This is source-selected, *classical local* algebra/numerical evidence, NOT an Agda kernel proof, a global quantum action, or experimental particle physics.

# E6-derived orbifold 27: one anomalous U1 direction and a photon-preserving local Green–Schwarz repair

**2026-10-25 GLOBAL FORM HARD GATE:** Original first-Tits action on the `27` has centre characters `(a-b,c-a,b-c)` mod 3; its kernel is the diagonal `Z3`. The faithfully acting trinification group is `(SU3c×SU3L×SU3R)/Z3_diag`. The exact 27-case audit and explicit T² clock/shift quotient holonomies demonstrate a NONLIFTABLE bundle with central commutator `(ωI,ωI,ωI)`: lifted CP3/S²×S⁴/S²×K3 spin index tests do NOT settle that sector. The new concrete top global-CS obligation is regulator- and eta-consistent anomaly/CS/WZ on nonliftable diagonal-Z3 flux sectors, not more naive polynomial coefficient matching. [Owner](KKE6OrbifoldCSWZTransferSpinIndexMaxCut20261025.md), `check_kk_e6_trinification_global_z3_quotient.py`, `KKE6TrinificationDiagonalZThreeQuotientExact.agda`.\n\n
**LATEST 2026-10-25 CS/WZ SPIN-INDEX CORRECTION:** The earlier apparent \(\mathbb Z_2\) Chi33 half-phase obstruction was conditional on *symmetric independent WZ terms at both fixed planes*, not a universal charge-two no-go. [CS transfer/spin-index owner](KKE6OrbifoldCSWZTransferSpinIndexMaxCut20261025.md) explicitly redistributes the source half-anomalies by a 5D bulk CS variation \((+I_6/2,-I_6/2)\), yielding \((I_6,0)\). A SINGLE first-plane Chi33 WZ term \(-\theta_\Chi X_4/2\) then cancels the local anomaly; every coefficient is integral in the original **unnormalised source trace lattice**. Spin \(\mathbb CP^3\) full-27 indices are even for arbitrary integral two-U1 fluxes (proved via nine residues modulo three), as are selected \(S^2\times S^4\) instanton and \(S^2\times K3\) families. This is significantly more promising than extra mirror fermions, but DOES NOT establish the true integral spin/quotient CS, all APS eta/torsion sectors or a complete anomaly-free 5D QFT. Earlier global half-phase warnings remain valid ONLY for their specific two-brane ansatz.\n\n
**FOLLOW-ON BOUNDARY HIGGS ERRATUM (2026-10-25):** The cited 18-real even Hessian was calculated for the INTEGRATED HOMOGENEOUS zero-mode potential, not separate 5D interior/Robin equations. The old t=.0246 spatially constant field has bulk t-force +0.147406469832 ≠0. The later `KKE6OrbifoldIntervalBoundaryELMaxCut20261025.md` constructs a nonconstant length-one normalized classical comparison BVP; its 3-field FEM Hessian is positive but the full 18-real interval functional and anomaly-safe global quantum action are still OPEN.

2026-10-25. **Owning PR:** [Agda KK #1241](https://github.com/chboishabba/dashi_agda/pull/1241). **Original repo donors:** [E6 first-Tits #1106](https://github.com/chboishabba/dashi_agda/pull/1106), \`Ternary27TrinificationInvariantTwoVEVPotentialExact\`, \`Ternary27TrinificationTwoNeutralVEVBreakingExact\`; existing \`AnomalyCancellationVerificationReceipt\`, \`StandardModelFiniteAnomalyHyperchargeCheck\`, \`GravitationalAnomalyCancellationReceipt\`, original 3D CS and [QFT stress #1165](https://github.com/chboishabba/dashi_agda/pull/1165). **Other source-critical documents:** \`KKE6OrbifoldChiralSourceMaxCut20261024.md\`, \`KKTOEPhysicalModelForkPareto20261024.md\`.

## Root attribution — not a discovery of Green–Schwarz or E6

E6 27 branching: R. Slansky, *Group theory for unified model building*, *Physics Reports* 79 (1981) 1–128, DOI 10.1016/0370-1573(81)90092-2. Five-dimensional orbifold chiral anomalies and fixed-point inflow: N. Arkani-Hamed, A. Cohen, H. Georgi, *Anomalies on orbifolds*, Phys Lett B 516 (2001), DOI 10.1016/S0370-2693(01)00946-7; C. Scrucca, M. Serone, L. Silvestrini, F. Zwirner, *Anomalies in orbifold field theories*, Phys Lett B 525 (2002), DOI 10.1016/S0370-2693(01)01430-7. **Decisive source** G. von Gersdorff, M. Quirós, *Localized anomalies in orbifold gauge theories*, Phys Rev D 68 (2003) 105002, DOI 10.1103/PhysRevD.68.105002: a 5D Green–Schwarz four-form is equivalent to a CS counterterm and cannot cancel a globally surviving 4D zero-mode anomaly; a GS two-form can cancel *certain mixed U1 anomalies*, with an anomalous surviving U1 becoming massive. The latter is a conditional mechanism, not a demonstrated action for this repo's spectrum.

Existing default-branch DASHI SM anomaly table proves the conventional **IR Standard Model** 16-matter anomaly cancellation in an all-left-handed convention; it does NOT pay the higher-rank **UV orbifold** anomaly. Distinguish E6 original representation theory, source-selected 27 parity, the Python anomaly polynomial, finite Agda source code, a real global spin-quantum theory and measured particles.

## Exact source-selected 27 anomaly polynomial

The **actual gauged source** for this test is SU3c×SU3L×SU3R on S1/Z2, *not* the full gauged E6 adjoint. Choose \(P_c=1\), \(P_L=P_R=\operatorname{diag}(-1,-1,+1)\) and one bulk Dirac27 with \(\Psi(-y)=\gamma^5\rho(P)\Psi(y)\); its zero modes are 16 left + 11 right. Original E32/E33 VEVs are parity-even when the bifundamental Phi has intrinsic odd parity and Chi intrinsic even. Use the **CENTRAL commuting** pre-VEV U1 generators
\[
U_L=\operatorname{diag}(-1,-1,2),\qquad U_R=\operatorname{diag}(-1,-1,2)
\]
for the SU2L/SU2R commutants. These are NOT the final R-side hypercharge generator \(T_R=\operatorname{diag}(-4,2,2)\).

Define \(x=F_L\), \(y=F_R\) in the source's unnormalised charge-trace basis, using chirality sign \(+1\) for LH and \(-1\) for RH (the exact code enumerates all 27 states). The complete **tested Abelian cubic** contribution is
\[
P_{\rm cubic}(x,y)=40x^3+24x^2y-24xy^2-40y^3
=(x-y)(40x^2+64xy+40y^2).
\]
The gravitational U1 coefficient is \(16(x-y)\), and all three tested mixed \(SU3_c^2 U1\), \(SU2_L^2 U1\), \(SU2_R^2 U1\) coefficients are \(2(x-y)\) in their explicitly declared Dynkin/trace normalisation. Pure colour cubic is zero and the tested SU2 Witten parity is even. **Every tested local perturbative gauge-anomaly polynomial factors through \(F_L-F_R\)**; this is stronger than declaring both independent U1s anomalous. The rank-one direction \(U1_L-U1_R\) is anomalous, while their diagonal sum is unaffected in this basis.

Executable \`scripts/check_kk_e6_orbifold_gs_anomaly_factor.py\` independently constructs the 27 states and proves all these factorisations using exact SymPy integer-polynomial expressions. This is a SOURCE-SELECTED infinitesimal/local anomaly polynomial statement, **not** a regulator- or global-quotient-normalised cohomology class: signs and rational coefficients may change with the consistent-versus-covariant anomaly convention or Bardeen local counterterms, while actual anomaly-freedom must be tested on the correct integral lattice.

## Candidate localized Wess–Zumino / Green–Schwarz action

At two fixed planes \(y=0,\pi b\), suppose (as in the simplest symmetric orbifold regulator) each endpoint carries one HALF of the above 4D zero-mode anomaly. Let \(X_4(F,R)\) denote the **correctly normalised invariant four-form** whose SOURCE TRACE-COEFFICIENT analogue is
\[
40F_L^2+64F_LF_R+40F_R^2+16\,p_1(R)
+2\,\operatorname{tr}F_c^2
+2\,\operatorname{tr}F_{SU2L}^2
+2\,\operatorname{tr}F_{SU2R}^2 .
\]
**This expression is symbolic**: it has NOT been converted into normalized spin/quotient characteristic classes; don't treat 16 or 2 as real gravitational Dynkin/CS quantization.

A candidate pair of localized axionic phases \(a_0,a_\pi\) with
\(\delta a_i=\lambda_L(y_i)-\lambda_R(y_i)\)
and suitable WZ variation
\[
\delta S_{{\rm WZ},i}=-(\lambda_L-\lambda_R)X_4/2
\]
could cancel each endpoint's **consistent local variation**, up to the standard local Bardeen/descent convention. Unlike **bulk CS-only inflow**, these two WZ variations have the **same sign** at the endpoints and can cancel a nonzero integrated anomaly. This is an *infinitesimal algebraic ansatz* and not yet a globally defined 5D gauge/spin-invariant action. The source tests every displayed polynomial coefficient divisible by 2 for this particular trace basis; this does **not** establish integral characteristic-class or axion periodicity quantization.

**Most economical original source donor:** the actual #1106 Chi E33 Higgs VEV carries \((Q_L,Q_R,Q_{T3R})=(2,-2,0)\), precisely the anomalous direction. Locally \(\theta_\Chi=\arg \Chi_{33}\) shifts by \(2(\lambda_L-\lambda_R)\); hence \(a_i=\theta_\Chi(y_i)/2\) has the desired **infinitesimal** shift and could avoid introducing an unrelated axion. But \(\theta_\Chi\) is defined modulo \(2\pi\), so its HALF is defined only modulo \(\pi\). Whether the endpoint WZ phases are globally single-valued depends on the true gauge/spin charge lattice and WZ coefficients; naive per-endpoint \(X_4/4\) would give half-integral nonabelian coefficients in the displayed trace basis. **Do not claim this source satisfies global quantization**. Alternative truly charge-one localized fields or a proper 5D GS two-form are still distinct candidate actions and must be screened for gauge representations and massless states.

## Photon and electroweak source: a real mass-matrix rank test

The original two-VEV hypercharge generator is
\[
Y=\frac{U_L+U_R-3H_R}{6},\qquad H_R=\operatorname{diag}(1,-1,0),
\]
since \(U_R-3H_R=\operatorname{diag}(-4,2,2)=T_R\) from #1106. Along a pure Y gauge transformation the **two central U1 coefficients coincide**, so \(\delta a=0\). Both original E32 and E33 VEVs are Y-neutral. Thus a GS/Stueckelberg mass along \(U1_L-U1_R\) does **not** automatically remove Y or make the photon massive.

The **selected orbifold-even Chi E21** component is an \(SU2_L\) doublet with \(Y=+1/2,T3_L=-1/2\). In neutral Cartan basis \((T3_L,U_L,U_R,H_R)\) its scalar VEV charge vectors are:
- \(\Phi E32:\ q_\Phi=(0,2,1,1)\)
- \(\Chi E33:\ q_\Chi=(0,2,-2,0)\)
- GS difference \(q_a=(0,1,-1,0)=q_\Chi/2\)
- candidate EW \(\Chi E21:\ q_{\rm EW}=(-1/2,-1,+1,-1)\).

The **sourced** neutral mass Gram \(M\propto\sum q q^\top\) has rank 2 after only E32/E33, still rank 2 after the candidate GS mass, and rank **3 of 4** after an additional E21 electroweak VEV. Its unique null vector is
\[
Q=T3_L+\frac{U_L+U_R-3H_R}{6}=T3_L+Y.
\]
This is an exact tree-level *Cartan* source result, code \`scripts/check_kk_e6_gs_photon_rank.py\`; it is not a full electroweak gauge diagonalisation or a prediction of \(g\), \(\sin^2\theta_W\), W/Z masses, or an E6 universal gauge coupling. **No independent old Maxwell U1_B is retained in this candidate** (keeping it would add the earlier extra photon).

**Critical scalar negative control:** the source #1106 two-bifundamental potential has the E32/E33 orbit as its zero set and positive transverse curvature, so a spontaneous E21 VEV **does not follow** from that unchanged potential. A physical electroweak tachyonic scalar potential, boundary-localised Higgs source or new coupled VEV sector must be provided and the old Higgs vacuum **re-minimised**, including new KK mode shifts, fermion masses, photon masses and scalar instabilities. Merely exhibiting an orbifold-even doublet does not solve electroweak symmetry breaking.

## Updated BIDI/Pareto outcomes and unavoidable blockers

1. **Confirmed producer:** original E6 27 under selected SU3³ orbifold parity yields a chiral SM-like 16L, an SM-vectorlike 10R+1R, E32/E33 Higgs compatibility and IR anomaly cancellation in existing repo conventions. Not a full E6 gauged model.
2. **New positive discriminatory test:** the *entire tested* UV anomaly polynomial has rank-one anomalous direction \(F_L-F_R\); a **local** GS/WZ variation and the existing E33 phase provide a physically structured repair avenue that preserves Y. A mirror 27 is **not** mathematically necessary to cancel *local Abelian anomalies* in an EFT.
3. **Additional conditional positive:** one massless photon after E21 EW VEV in the selected SU3³ Cartan sector; GS doesn't increase the mass rank and doesn't charge Y.
4. **Actual hard blockers:** fully normalized *integral spin/quotient* anomaly polynomial and GS/WZ axion periodicity, both endpoint counterterms and 5D regulator/eta; full SU3³ or E6 gauge field source and all mixed anomalies; a real dynamical E21 electroweak source; Yukawa/brane-orbifold-compatible masses for vectorlike exotics; anomaly-safe quantum action and brand-new interval Casimir.
5. **Strict downstream consumers:** a new source-specific \(V(b,\mathrm{holonomies},\mathrm{VEVs})\), full metric variation \(T55,T_{\mu\nu}\), Einstein source and PPN/LARES with predeclared uncertainty. Old smooth-circle D>409 no-go and 3D CS owners are negative controls, NOT automatically the orbifold determinant.

## Verification, kernel and empirical status

Independent local SymPy full27 charge/polynomial factorization, VEV charge vectors and 4×4 Gram ranks: PASS. Scripts committed on KK #1241:
- \`scripts/check_kk_e6_orbifold_gs_anomaly_factor.py\`
- \`scripts/check_kk_e6_gs_photon_rank.py\`

Finite Agda \`DASHI/Physics/Gravity/KKE6OrbifoldGreenSchwarzConsumerExact.agda\` imports the original SM anomaly and orbifold BIDI owners and proves coefficient arithmetic and source-indexed non-transport. The continuum polynomial is **not Agda kernel-proved**; code is source-written and exact-head kernel check UNVERIFIED. Nor has an action with global gauge/spin anomaly freedom or experimental particle-spectrum viability been established.

The scientifically valuable advance here is **not discovering Green–Schwarz**. It is locating a specific one-direction, photon-preserving candidate repair for an explicit otherwise anomalous 27 zero-mode construction, with a quantified global-periodicity and electroweak-VEV payment. A failure of its global quantization would itself be a sharp source-specific no-go.


## 2026-10-25 improved electroweak source: fully stationary even-18 scalar vacuum

The earlier correct warning that the original #1106 V6 has positive E21 curvature has now been acted on, not merely reiterated. New executable `scripts/check_kk_e6_orbifold_boundary_higgs_source.py` uses the LITERAL original six-invariant V6, and `scripts/check_kk_e6_orbifold_boundary_higgs_hessian.py` independently checks the FULL 36-real scalar gradient/Hessian with torch autodiff on the SOURCE-SELECTED orbifold projection. Canonical `Docs/physics/KKE6OrbifoldBoundaryHiggsHessianMaxCut20261025.md` has exact formulas and attribution.

An actual orbifold-fixed-plane gauge-invariant reduced-group term `-mu² Tr(P2 Chi P2 Chi†)+lambda [Tr(P2 Chi P2 Chi†)]²` can produce the EW candidate, but only by changing the old action and allowing original Phi E32 and Chi E33 magnitudes to relax. Set `Phi=a E32`, `Chi=b E33+t E21`; exact stationarity requires `a²=1-t²/2`, `b²=1-2t²`, `mu²=3+(2 lambda-13/2)t²`. For illustrative `lambda=4,t=.0246,mu²=3.00090774`, the FULL 36-real scalar gradient vanishes, with parity-even projected 18×18 Hessian having **0 negative, 7 Goldstone zero, 11 strictly positive** directions (smallest positive about .0036216304). This matches 8 even L/R generators → 1 photon, and preserves the GS direction's neutrality under Y.

Full 36 Hessian has 2 negative directions in the **orbifold-odd** 18-real sector, which has NO constant four-dimensional zero modes. Their full positive KK-gradient tower must still be computed. No full interval source, global minimum, regulator-complete GS/CS, measured EW parameters or full gauged E6 is thereby proved.

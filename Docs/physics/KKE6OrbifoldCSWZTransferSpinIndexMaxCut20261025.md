# E6-derived trinification orbifold: bulk CS transfer + one Chi33 WZ source
**Date:** 2026-10-25. **Owner:** [physical KK #1241](https://github.com/chboishabba/dashi_agda/pull/1241). **Original mathematical donor:** [E6 first-Tits/trinification #1106](https://github.com/chboishabba/dashi_agda/pull/1106) (separate unmerged PR: no illicit Agda import). **TOE:** [Agda #1217](https://github.com/chboishabba/dashi_agda/pull/1217), [Lean #80](https://github.com/chboishabba/dashi_lean4/pull/80). This document supersedes the old inference that the half-period Chi33 WZ obstruction inevitably requires an independent charge-one scalar.

## Attribution and old CS owners

Original physical results are NOT ours: Slansky 1981 (E6 27/trinification), Arkani-Hamed/Cohen/Georgi 2001 (orbifold anomaly localization), Scrucca/Serone/Silvestrini/Zwirner 2002 (fixed-plane anomaly), **von Gersdorff & Quirós, *Localized anomalies in orbifold gauge theories*, Phys Rev D 68 (2003) 105002, DOI 10.1103/PhysRevD.68.105002** (4-form/CS redistribution versus globally surviving anomaly and GS two-form), and **Christopher T. Hill, *Exact equivalence of the gauged Wess-Zumino-Witten term and the Yang-Mills Chern-Simons term*, Phys Rev D 73 (2006) 126009, DOI 10.1103/PhysRevD.73.126009** (five-dimensional boundary CS/WZW interplay). Early parity/orbifold anomalies: Barbieri/Contino/Creminelli/Rattazzi/Scrucca, PRD 66 (2002) 024025, DOI 10.1103/PhysRevD.66.024025. The 5D global parity/CS and eta regularization are still NOT paid by any of these papers for OUR selected gauge+matter source.

Existing repo KacMoodyLevelReceipt, CSLevelFlowFullReceipt, BulkBoundarySU3Receipt and FermionicLoopCSShiftReceipt are real PRIOR finite/local/topological source owners, but mainly 2+1D CS/WZW and explicitly conditional levels; they cannot be copied as a new 4+1D spin CS functional. The selected mixed U1 5-form test in \`scripts/check_kk_minkowski_cs5_same_source.py\` is a correct specialized test, not a full \`SU3³\` functional.

## Exact 27 ZERO-MODE anomaly in the declared local trace basis

Source is **gauged SU3c×SU3L×SU3R**, not 78-dimensional full gauged E6. One 5D Dirac 27 on S1/Z2 with \(P_c=I,P_L=P_R=\operatorname{diag}(-1,-1,+1)\) and the original source-compatible opposite Phi/Chi parities gives a chiral 16 and SM-subgroup vectorlike 10+1. The source's EXACT enumerated, pre-VEV UV chiral anomaly polynomial factors in the \`U1_L\` and CENTRAL \`U1_R\` curvature variables \(x=F_L,y=F_R\) as
\[
P_3=(x-y)(40x^2+64xy+40y^2),\qquad P_{\rm grav}=16(x-y).
\]
The selected mixed \`SU3c²U1\`, \`SU2L²U1\`, \`SU2R²U1\` triangular source coefficients are each \(2(x-y)\) in the **source's own index/trace-normalization convention**. We can package the symbolic local formal polynomial as \(I_6^{\mathrm{trace}}=(x-y)X_4\), with
\[
X_4=40x^2+64xy+40y^2+16p_1+2(c_{2c}+c_{2L}+c_{2R}).
\]
**CRITICAL:** \(p_1,c_2\) in this display are FORMAL source coefficient tags, NOT already normalized integral characteristic classes. The precise index/anomaly polynomial has e.g. cubic/6 and gravitational/24 \(\hat A\)-normalizations, and the nonabelian fundamental Dynkin-to-c2 normalization differs by factors of two. This \`X4\` is a trace-ring consumer, NOT a complete integral \(\Omega^{\mathrm{spin}}_6(BG)\) action. Always distinguish **index** from triangle coefficients and consistent/covariant anomaly representatives.

## New correct fixed-plane allocation — the half-phase problem is not universal

The initial source test used **symmetric** fixed-plane anomaly assignment \((I_6/2,I_6/2)\). Trying a WZ counterterm separately on EACH plane with a charge-two Chi33 phase required, schematically, \(-\theta_\Chi X_4/4\) per plane. Its mixed source coefficient \(2/4=1/2\) implied a \(-1\) under a 2π phase winding when evaluated on a hypothetical unit mixed-instanton background. That was a **conditional failure of that symmetric two-WZ ansatz**, not a general global no-go.

A 5D CS term can transfer anomaly between endpoints without changing its integrated sum. Choose its local descent to contribute \((+I_6/2,-I_6/2)\). Then the total anomaly is:
\[
(I_6/2,I_6/2)+(+I_6/2,-I_6/2)=(I_6,0).
\]
The ORIGINAL Chi33 Higgs phase has charges \((U_L,U_R)=(+2,-2)\) and \(\delta\theta_\Chi=2(\lambda_L-\lambda_R)\). One fixed-plane Wess–Zumino coupling \(-\theta_\Chi X_4/2\) consequently transforms as \(-(\lambda_L-\lambda_R)X_4\) at that plane. Its infinitesimal variation cancels ALL of the locally transferred \(I_6\), and nothing needs cancelling at the other plane. Explicitly for independently variable endpoint gauge parameters \(\alpha_0,\alpha_\pi\):
\[
\delta\Gamma_{\rm 27}=\tfrac12(\alpha_0+\alpha_\pi)X_4,\quad
\delta S_{\rm CS}=\tfrac12(\alpha_0-\alpha_\pi)X_4,\quad
\delta S_{\rm WZ}=-\alpha_0X_4,
\quad \sum\delta=0.
\]
This is a FINITE **consistent-local-variation SOURCE ANSATZ**; it assumes the chosen regulator supports the claimed endpoint distribution and an allowed 5D orbifold CS action. It is not itself a nonperturbative gauge invariance proof.

All coefficients of the SOURCE \`X4/2\` are integers: Abelian \(20,32,20\), gravitational \(8\), and each nonabelian mixed coefficient \(1\). Thus on the **NAIVE INTEGRAL SYMBOL RING** the one-brane \(2\pi\) Chi-phase winding does not flip the path integral's phase. The previous "Chi33 has charge two, so we must add charge-one axion" inference is NOT justified at this level. Source executable: \`scripts/check_kk_e6_orbifold_cs_wz_anomaly_transfer.py\`, which enumerates all 27 original charges and checks boundary cancellation for **independent endpoint parameters**.

This does NOT mean those coefficients automatically meet the TRUE integral spin/quotient gauge-CS levels. The physical gauge group is a quotient of SU2×U1 factors inside SU3; spin classes, mixed nonabelian trace normalization, torsion and APS eta/5D parity require separate work. A local Bardeen/descent choice must also be constructed before identifying the actual CS5 functional. A single Chi33 phase cannot cover configurations where Chi33 vanishes; a nonlinear Higgs/WZ EFT must specify its domain and UV completion.

## Stronger global test on actual spin six-manifold families

\`scripts/check_kk_e6_orbifold_spin_index_test_families.py\` tests a meaningful class of nontrivial **global gauge backgrounds**, not simply free integer coefficients.

**1. Spin CP3**: \(\mathbb CP^3\) is spin with \(p_1=4h^2\) and \(h^3=1\). For charge \(q\) in line bundle \(\mathcal O(q)\), the 6D Dirac index is
\[
\mathrm{ind}\,D_{\mathcal O(q)}=\int_{\mathbb CP^3}\hat A(T)\operatorname{ch}(\mathcal O(q))=(q^3-q)/6.
\]
For arbitrary integers \(m,n\) defining central \(U1_L,U1_R\) line-bundle fluxes, the actual chiral 27 index is
\[
I(m,n)=\frac{(m-n)(40m^2+64mn+40n^2-16)}{6}
=\frac43(m-n)(5m^2+8mn+5n^2-2).
\]
**For every \(m,n\in\mathbb Z\), this index is EVEN.** Reason: \(d=m-n\); modulo three \(5m^2+8mn+5n^2-2\equiv2d^2+1\), and \(d(2d^2+1)=0\) for all \(d\in\{0,1,2\}\). Hence the numerator's \(d(5m^2+8mn+5n^2-2)\) is divisible by 3, so \(I\) is twice an integer. The script checks all 9 residue classes and an independent \([-15,15]^2\) rational index test. Finite Agda \`KKE6OrbifoldCSWZTransferConsumerExact.agda\` supplies a *three-case mod-three residue theorem*, NOT the physical index theorem.

**2. Spin S2×S4** with integer central-U1 \(m,n\) flux on S2 and a unit SU3c, SU2L or SU2R instanton on S4: the source's chiral mixed **index** coefficient in the fundamental-index-one convention is \(4(m-n)k\), always even. Note that this differs from the source's \(2(m-n)\) **triangle Dynkin-half convention**: 6D Chern character/integral \(c_2\) has its own normalization. The script checks each representation/multiplicity explicitly.

**3. Spin S2×K3** with \(\hat A(K3)=2\) gives gravitational-U1 index \(32(m-n)\), also even.

These are nontrivial TEST FAMILIES of spin backgrounds and strongly improve the viability of the required half-CS anomaly-transfer level. They do **not** establish that every spin \(\Omega^{\rm spin}_6(BG)\) generator, finite-quotient/torsion bundle, interval-boundary eta phase or chiral 5D fermion regulator passes. No globally defined CS5+WZ quantum functional is claimed.

## BIDI / physically relevant consequences

- **The best steelman improves:** anomaly-free IR chiral16+vectorlike10+1, selected source-compatible two E32/E33 VEVs and a single tree-level photon after even E21, and now one candidate CS+single-WZ local/naive-lattice anomaly repair using the ALREADY OWNED Chi33 Higgs phase. No separate charge-one field is forced by the original naive mod2 test.
- **No automatic physics:** that WZ term is a boundary interaction; its gauge-covariant nonlinear Higgs field and spin/quotient action must be established **along the SAME scalar/gauge path**, not just at the chosen vacuum. The original scalar has nonconstant Robin profile, and the existing \`Docs/physics/KKE6OrbifoldIntervalBoundaryELMaxCut20261025.md\` corrected the old integrated zero-mode stationary claim. Need incorporate the WZ boundary response into source field variations and metric stress; cannot reuse the prior comparison BVP without modification.
- **No CS/flat vacuum magical repair:** flat F=R=0 classical CS vanishes, so the old smooth-S1 D>409 one-loop source no-go remains valid for THAT source and radius. The new orbifold Higgs/WZ theory has an entirely different spectrum/regulator and cannot inherit the smooth circle Casimir.
- **Next decisive payoff:** (1) compute physically normalized 5D SU3³ orbifold CS + local WZ with actual Bardeen descent, full gauge quotient integral spin bordism/APS eta and interval regulator; (2) correct boundary scalar/gauge/fermion dynamics including WZ and use old #1165 same-metric-path action→stress; (3) coupled orbit/radion/holonomy effective vacuum and gravity/PPN/LARES discriminators. The 78-dimensional full E6 gauge adjoint retains another 30 parity-even coset generators and has not been constructed physically here.

**Status:** Exact rational and SymPy source polynomial, anomaly allocation, 2π naive phase and CP3/instantons/K3 test-family algebra locally reproduced; source scripts and finite Agda BIDI committed on #1241 (kernel typecheck NOT performed). No proof of full gauged E6, measured mass/particle spectrum, anomaly-free global 5D quantum theory or experimental gravity anomaly. Earlier claims of an *unconditional* Chi33 charge-two obstruction should be marked SUPERSEDED, not deleted or misattributed.


## Highest-value extra global cut: the original E6 27 is FAITHFUL only on (SU3³)/Z3_diag

Original source E6 #1106 actually specifies the **same first-Tits action** on three 3×3 blocks \((X,Y,Z)\): \(X\mapsto A X B^{-1}\), \(Y\mapsto B Y C^{-1}\), \(Z\mapsto C Z A^{-1}\). For the centres of SU3c/L/R, with exponents \(a,b,c\in\mathbb Z_3\), the central characters of the three \(9\)-dimensional blocks are
\[
a-b,\quad c-a,\quad b-c\pmod 3.
\]
All three vanish **iff** \(a=b=c\). An exact exhaustive 3³=27 enumeration in \`scripts/check_kk_e6_trinification_global_z3_quotient.py\` therefore identifies the kernel as precisely \(\{(0,0,0),(1,1,1),(2,2,2)\}\). Formal finite owner \`DASHI/Physics/Gravity/KKE6TrinificationDiagonalZThreeQuotientExact.agda\` proves all 27 kernel conditions by cases. Accordingly the source's **faithfully acting compact gauge group** is
\[
G_{\mathrm{tri}}=\big(SU(3)_c\times SU(3)_L\times SU(3)_R\big)/\mathbb Z_3^{\mathrm{diag}},
\]
consistent with the E6 subgroup literature (e.g. original E6 representation conventions and Slansky's review). This is not a discovery of the subgroup; it is a necessary actual-group identification for our previously unspecified \(\Gamma\).

**Explicit nonliftable bundle discriminator.** Let \(\omega=e^{2\pi i/3}\) and in SU3 take
\(C=\operatorname{diag}(1,\omega,\omega^2)\) and \(S\) the cyclic permutation matrix. Their commutator is \(CSC^{-1}S^{-1}=\omega I\). The two SU3³ holonomies \(H_1=(C,C,C)\) and \(H_2=(S,S,S)\) have nontrivial commutator \((\omega I,\omega I,\omega I)\) IN THE COVER but **commute in \(G_{\rm tri}\)**. They therefore define an ordinary flat quotient holonomy pair on \(T^2\) with nonzero \(\mathbb Z_3\) obstruction to a commuting SU3³ lift. The finite 27 matter acts consistently on the quotient because the diagonal centre acts trivially. This nonliftable quotient bundle is a genuine missing class in the earlier global test set.

**Consequence:** our stronger CP³, S²×S⁴, S²×K3 spin-index parity receipts covered certain LIFTABLE gauge backgrounds, NOT all \(G_{\rm tri}\) bundles. The previous source's "all coefficients of X4/2 are integers" was likewise only for naive separately integral source symbols. The actual global CS/WZ completion must evaluate the correctly normalized spin/gauge anomaly and five-dimensional fermion eta on these *nonliftable diagonal-Z3 flux sectors*, including possible fractional individual SU3 instanton classes, torsion, quotient charge lattice and boundary inflow. Do not assert anomaly freedom or a universal \(\mathbb Z_2\) absence before that test; likewise do not infer failure from a speculative fractional value. The concrete \(T^2\) witness is a strict new TEST INPUT, not a computed 5D CS phase.

This upgrades the prioritized research gate from the vague phrase "global quotient Γ" to a defined \(G_{\rm tri}\) and an explicit nonliftable bundle. It also prevents overindexing on the old Chi-phase half-unit or irrelevant 3D CS formulas: the new highest-information question is whether the specific original E6 27 + orbifold regulator + candidate one-boundary CS/WZ action is consistent on the *whole* faithful quotient gauge bundle class. The actual full gauged E6 adjoint is still a different action and has additional parity-even coset generators.


## Even sharper: NONLIFTABLE gauge bundle preserving the actual orbifold parity

**Corrective qualification:** the earlier simple bulk \`T²\` clock/shift witness proves global quotient obstruction in \`SU3³/Z3\`, but its cyclic shift matrix does NOT commute with \(P_L=P_R=\operatorname{diag}(-,-,+)\). Therefore it was *not* an explicit flat bundle for the **fixed-plane parity-even gauge subgroup** and must not be promoted as such.

The faithful FIXED-PLANE source group is instead
\[
H_{\mathrm{even}}=
\big(SU(3)_c\times S(U(2)\times U(1))_L
              \times S(U(2)\times U(1))_R\big)/\mathbb Z_3^{\mathrm{diag}}
\cong (SU(3)_c\times U(2)_L\times U(2)_R)/\mathbb Z_3^{\mathrm{diag}},
\]
where the relevant diagonal \(\mathbb Z_3\) acts through the concrete \(\mathrm{diag}(\omega,\omega,\omega)\) inside all three SU3 factors. It is contained in the parity-even cover. Its quotient matters even though the local gauge Lie algebra is unchanged.

**Explicit boundary-compatible bundle:** take the equator of \(S^2\), parameter \(t\in[0,1]\), and define an SU3 loop *up to the centre*
\[
h(t)=\operatorname{diag}\big(e^{2\pi i t/3},
  e^{2\pi i t/3},e^{-4\pi i t/3}\big).
\]
This commutes with \(\mathrm{diag}(-,-,+)\) for **every** \(t\), has determinant one and lies in \(S(U2\times U1)\). Form the quotient clutching transition
\[
g(t)=[(h(t),h(t),h(t))]\in H_{\mathrm{even}}.
\]
At \(t=0\), its lift equals the cover identity; at \(t=1\), it equals \((\omega I,\omega I,\omega I)\), which is **not** the cover identity but is the diagonal kernel. Thus \(g(1)=g(0)\) in the quotient: it is a legal \(S^1\to H_{\mathrm{even}}\) clutching LOOP defining a principal boundary group bundle over \(S^2\). Any lift starting at the identity uniquely ends at nontrivial deck \(\mathbb Z_3\), so it **cannot lift to the original three-factor cover**. Repeating the loop three times gives zero *deck obstruction*; it does not imply the original loop has order three in the full \(\pi_1(H)\).

The exact matrix/commutator and endpoints are checked in \`scripts/check_kk_e6_orbifold_even_quotient_s2_clutch.py\`. This is now a **genuine orbifold-parity-compatible nonliftable-bundle test input**, stronger than the bulk \`T²\` clock/shift witness. It demonstrates precisely why all earlier CP³ and S²×S⁴/S²×K3 **liftable** spin-index successes and naive \`X4/2\` integrality do NOT settle the full global quantum anomaly on the actual faithful gauge group.

The missing physical calculation is well posed: place the boundary gauge and matter sources on spin 4D/5D geometries supporting this nontrivial \(\mathbb Z_3\) obstruction (for example a product containing that \(S^2\) as a 2-cycle), construct the actual five-dimensional parity/APS eta and consistent CS plus first-plane Chi33 WZ functional, and test independence of gauge representatives and regulator at both fixed points. No assertion about the sign/phase on this bundle is made without those calculations. The nonconstant scalar Robin interval source and full18-even FEM from #1241 are separate classical producers.


## Diagonal-Z3 quotient MIXED fractional-instanton result (2026-10-25)

The new parity-even \(S^2\) clutch source proves nonliftable gauge bundles are real. We can additionally PAY one selected part of their CS/WZ integrality test rather than leaving the entire quotient issue a black box.

Under the faithful \(G=(SU3_c\times SU3_L\times SU3_R)/Z3_{\rm diag}\), each projected **PSU3** gauge bundle on a closed oriented 4D test background carries the SAME \(\mathbb Z_3\) lifting obstruction \(B\in H^2(X,\mathbb Z_3)\). In the standard \(\mathrm{tr}_{\bf3}F^2\) instanton convention, its fractional instanton part is \(\mathfrak q_i\equiv\frac{(N-1)}{2N}\int{\cal P}(B)=\frac13\int B\cup B\pmod1\) for \(N=3\), up to overall orientation/sign convention. The three projected fractions are **equal** as functions of \(B\), because the central twist is diagonal. Thus
\[
\mathfrak q_c+\mathfrak q_L+\mathfrak q_R
\equiv3\frac{\int B^2}{3}\equiv0\pmod1.
\]

That is exactly the structure of the mixed non-Abelian source **trace-lattice** coefficient \(c_{2c}+c_{2L}+c_{2R}\) of the proposed ONE fixed-plane WZ term \(-\theta_\Chi X_4/2\). It need not acquire a fractional phase merely because each projected PSU3 instanton individually has a \(1/3\) or \(2/3\) fractional charge. In particular on the spin 4-fold \(S^2\times S^2\), take \(B=u+v\) with \(u^2=v^2=0,\int uv=1\). Then \(\int B^2=2\pmod3\), each \(\mathfrak q_i\equiv2/3\), but the equal-weight sum is \(2\equiv0\pmod1\). A counterterm weighting only one SU3 factor would instead have a fractional \(2/3\) period on this same test. This is an important **three-factor cancellation**, not evidence that all individual fractional charges are integral.

Executable \`scripts/check_kk_e6_z3_fractional_instanton_mixed_wz.py\` checks all three Pontryagin residues and this \(S^2\times S^2\) test, distinguishing weights divisible by three from weights that fail. Original fractional PSU(N) instanton formula is established in the global-form/1-form-anomaly literature (e.g. *The global form of flavor symmetries*, SciPost Phys. 13 (2022) 024; and work on PSU(N) Chern–Weil symmetry breaking). **Strict limitation:** the source's earlier \(2(c_{2c}+c_{2L}+c_{2R})\) were HALF-Dynkin triangle coefficients, not a fully normalized characteristic class. We have verified the equal-weight *fractional PSU3 structure* only. Mixed U1 classes, quotient-correlated first Chern classes, spin/APS eta, counterterm descent and 5D fermion regulator remain unpaid, and the orbifold's parity-compatible fixed-plane bundle must be included in a full physical test.

**Updated critical path:** global field theory needs the FULL normalized spin/quotient \(\Omega_6^{\rm spin}(B H_{\rm even})\) gauge anomaly, possibly refined by eta/torsion, and its WZ+CS extension to the five-dimensional boundary field configuration space. The lifted spin CP3 index parity and new equal-weight diagonal-Z3 mixed instanton cancellation are *partially paid* test families, not a complete all-bundles theorem. This makes "add arbitrary new charge-one axion" lower priority than closing the remaining quotient- and WZ-quantization receipts with the original Chi33 field.


## 2026-10-26 superseding index theorem and exact remaining wall

**Correction to the preceding test-family-only roadmap:** the earlier CP3, S2×S4, S2×K3 and equal-weight fractional PSU3 checks remain valid bounded fixtures, but are no longer the strongest *free/index-period* result. Physical KK #1241 now owns the same-source proof and regression at `Docs/physics/KKE6Chi33PhaseFieldSpaceGate20261026.md` and `scripts/check_kk_e6_orbifold_index_even_universal_trace.py`.

The selected parity-even H=(SU3c×U2L×U2R)/Z3_diag representation is a genuine associated 27 complex vector bundle E27 even on nonliftable quotient bundles. Its original SL3^3 block formula gives ch1(E27)=0 and ch3(E27)=0 as rational characteristic classes because the first/cubic trace polynomials cancel A+B+C IDENTICALLY on the full Lie algebra. The source orbifold parity commutes with H and hence gives E27=Eplus⊕Eminus as genuine H subbundles. For any closed spin SIX-manifold X, the classical Atiyah-Singer Dirac formula then yields ind(D_E27)=0, so
`ind(D_Eplus)-ind(D_Eminus)=2 ind(D_Eplus)`.
Thus the signed HALF-INDEX is integral for all such H bundles on spin sixfolds, NOT merely the previously sampled lifted bundles. This conclusion relies on the external classical index theorem and source-equivariant representation split; the new Agda kernel does not itself implement these bundle constructions. Exact symbolic 27-weight regression and a nonliftable spin (S2)^3 witness yield signed index -12. This is a stronger POSITIVE candidate necessary quantisation test, not a global 5D action.

**Concurrent negative all-field test:** the parity-compatible H clutch can give ANY integer c1(L_Chi33), including odd +/-1, at fixed nontrivial Z3 lift-obstruction. Thus the old 'only even' degree observation belongs to the equal-doublet U2 torus SUBFAMILY, not the full H group. Nonzero c1 forces zeros of the Chi33 section, so a pure unpatched arg(Chi33) WZ functional cannot be defined on every admitted H bundle. This does not disprove a defect-complete differential cocycle, a justified nowhere-zero Higgs reduction, or another UV completion.

**Remaining global max-cut, now sharper:** a genuinely defined five-dimensional spin H quotient determinant/Pfaffian and APS/eta phase (including torsion/global anomalies of the relevant spin bordism), a *normalized exponentiated* CS transfer and an all-field WZ/defect completion. They must cancel for actual small/large gauge transformations, and be compatible with the full coupled KK spectrum and same-action boundary source. Equality of a closed sixfold free index period is necessary but does not supply the torsion eta datum or construct the path integral. None of the old trace-lattice coefficient integrality claims should be promoted to a global gauge theorem. Do not expend another cut on additional equivalent CP3 samples.

Original-root priority: Atiyah–Singer spin Dirac index theorem; Hatcher *Vector Bundles & K-Theory* clutching; von Gersdorff–Quirós (2003) localized anomalies; Kazuya Yonekura, *General anomaly matching by Goldstone bosons*, JHEP 03 (2021) 057, DOI 10.1007/JHEP03(2021)057, as a global-WZW methodology donor. Current selected 27 calculations are repository derivations, not results attributed to those general sources. Proof status: external standard theorem + source-specific analytic reduction, local SymPy execution, GitHub source-writing; Agda kernel, complete η, and quantum experimental claims OPEN.

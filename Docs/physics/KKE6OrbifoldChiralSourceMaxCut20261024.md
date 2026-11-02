# Physical E6-derived trinification orbifold: exact VEV parity, chiral 16 + vectorlike 10+1 and UV anomaly blocker

**2026-10-25 GLOBAL FORM HARD GATE:** Original first-Tits action on the `27` has centre characters `(a-b,c-a,b-c)` mod 3; its kernel is the diagonal `Z3`. The faithfully acting trinification group is `(SU3c×SU3L×SU3R)/Z3_diag`. The exact 27-case audit and explicit T² clock/shift quotient holonomies demonstrate a NONLIFTABLE bundle with central commutator `(ωI,ωI,ωI)`: lifted CP3/S²×S⁴/S²×K3 spin index tests do NOT settle that sector. The new concrete top global-CS obligation is regulator- and eta-consistent anomaly/CS/WZ on nonliftable diagonal-Z3 flux sectors, not more naive polynomial coefficient matching. [Owner](KKE6OrbifoldCSWZTransferSpinIndexMaxCut20261025.md), `check_kk_e6_trinification_global_z3_quotient.py`, `KKE6TrinificationDiagonalZThreeQuotientExact.agda`.\n\n
**LATEST 2026-10-25 CS/WZ SPIN-INDEX CORRECTION:** The earlier apparent \(\mathbb Z_2\) Chi33 half-phase obstruction was conditional on *symmetric independent WZ terms at both fixed planes*, not a universal charge-two no-go. [CS transfer/spin-index owner](KKE6OrbifoldCSWZTransferSpinIndexMaxCut20261025.md) explicitly redistributes the source half-anomalies by a 5D bulk CS variation \((+I_6/2,-I_6/2)\), yielding \((I_6,0)\). A SINGLE first-plane Chi33 WZ term \(-\theta_\Chi X_4/2\) then cancels the local anomaly; every coefficient is integral in the original **unnormalised source trace lattice**. Spin \(\mathbb CP^3\) full-27 indices are even for arbitrary integral two-U1 fluxes (proved via nine residues modulo three), as are selected \(S^2\times S^4\) instanton and \(S^2\times K3\) families. This is significantly more promising than extra mirror fermions, but DOES NOT establish the true integral spin/quotient CS, all APS eta/torsion sectors or a complete anomaly-free 5D QFT. Earlier global half-phase warnings remain valid ONLY for their specific two-brane ansatz.\n\n
**FOLLOW-ON VALIDITY CORRECTION (2026-10-25):** The old E32/E33/E21 constant-profile 18-even Hessian was a stationary HOMOGENEOUS ZERO-MODE effective potential only, not a 5D bulk+boundary solution. The selected source V6 bulk t-force t(6−13t²) is nonzero at the old t=.0246 trial. A new dimensionless Robin interval BVP and its source-current checks are recorded in `KKE6OrbifoldIntervalBoundaryELMaxCut20261025.md`. Global UV GS anomaly and actual five-dimensional metric/fermion quantum vacuum remain unresolved.

2026-10-24. **Canonical source implementation:** [KK #1241](https://github.com/chboishabba/dashi_agda/pull/1241). **Existing first-Tits original code:** [E6 #1106](https://github.com/chboishabba/dashi_agda/pull/1106). **Parent strategy:** [KKTOEPhysicalModelForkPareto20261024.md](KKTOEPhysicalModelForkPareto20261024.md).

## Why this is the most productive cross-PR candidate

The previous smooth S1 full-27 5D Dirac sector is vectorlike as a four-dimensional zero-mode theory. Its index obstruction must be resolved before completing more irrelevant scalar mass tuning. The minimal **constructive** boundary change below selects actual chiral zero modes, reuses the literal E32/E33 2-VEV source from #1106, retains its quartic potential's sign invariances, and reproduces a Standard-Model-like chiral **16** with vectorlike **10+1** companion under the measured subgroup. This is a source-specific **candidate**, NOT an actual anomaly-free 5D orbifold action or completed Standard Model.

**Scientific original authorship:** E6 representation decomposition and trinification (Slansky, *Group theory for unified model building*, *Physics Reports* 79 (1981) 1–128, DOI 10.1016/0370-1573(81)90092-2); orbifold chiral modes and fixed-plane anomaly (Arkani-Hamed, Cohen, Georgi, *Anomalies on orbifolds*, *Phys Lett B* 516 (2001) 395–402, DOI 10.1016/S0370-2693(01)00946-7); explicit local fixed-point anomaly conditions (Scrucca, Serone, Silvestrini, Zwirner, *Anomalies in orbifold field theories*, *Phys Lett B* 525 (2002) 169–174, DOI 10.1016/S0370-2693(01)01430-7). Local source selection, code/arithmetical checks and formal BIDI distinction are downstream repo work, not newly discovered group theory or index theory.

## Source-specific classical choice

**Actually gauged model at this stage** is \(G=SU(3)_c\times SU(3)_L\times SU(3)_R\), NOT all 78 adjoint generators of E6. The fermion matter transforms as E6-derived
\[
27=A\oplus B\oplus C,\quad
A=(3,\bar3,1),\quad B=(\bar3,1,3),\quad C=(1,3,\bar3).
\]

On \(S^1/\mathbb Z_2\) choose inner involutions

\[
P_c=\mathbf1_3,\quad P_L=P_R=\operatorname{diag}(-1,-1,+1)\in SU(3).
\]

For one five-dimensional bulk Dirac-27, choose orbifold action \(\Psi(-y)=\gamma^5\rho(P_L,P_R)\Psi(y)\), using convention \(\gamma^5=+1\) on right-handed four-dimensional spinors. Thus an internal parity \(+1\) produces an even **right-handed** zero mode; internal parity \(-1\) produces an even **left-handed** zero mode. Existence of compatible smooth gauge/Higgs/fermion **kinetic terms and boundary conditions** remains part of the candidate action.

**The existing #1106 VEVs actually survive:**
- \(\Phi\) (complex (1,3L,\bar3R)) intrinsic orbifold parity \(\eta_\Phi=-1\), with vacuum \(E_{32}\). Its internal parity is \(p_L(3)p_R(2)=-1\), so total parity \(+1\).
- \(\Chi\) (another complex (1,3L,\bar3R)) intrinsic parity \(\eta_\Chi=+1\), with vacuum \(E_{33}\). Internal parity is \(p_L(3)p_R(3)=+1\), so total parity \(+1\).

Crucially, #1106's ACTUAL six-invariant potential is comprised of individual quadratic norm penalties and the mixed **even** invariants
\(\operatorname{tr}(\Phi^\dagger\Phi\Chi^\dagger\Chi)\) and \(n_\Phi n_\Chi-\operatorname{tr}(\Phi\Phi^\dagger\Chi\Chi^\dagger)\). It is invariant under INDEPENDENT sign flips \(\Phi\mapsto-\Phi\) or \(\Chi\mapsto-\Chi\), exactly the parity pattern used here. This verifies **source-potential compatibility**, not full E6-invariant scalar action or physical tachyon-free electroweak breaking.

The even SU3L/SU3R Lie algebra generators are four on each side; their shared kernel for both E32/E33 has exact real dimension **4**. It is \(SU(2)_L\times U(1)_Y\) (Lie algebra), with unbroken SU3c independent. One convenient hypercharge normalisation is

\[
Y=\frac16\left(T_L=\operatorname{diag}(-1,-1,2),\
T_R=\operatorname{diag}(-4,2,2)\right).
\]

Both diagonal generators are traceless and commute with the orbifold parities; the combined \(T_L E_{3j}=E_{3j}T_R\) holds for j=2,3. This specifies the low-energy **electroweak gauge algebra** but NOT yet its photon (the latter requires sourced electroweak Higgsing), couplings or Weinberg angle.

## Actual chiral zero-mode content

With selected gamma5 convention, the 27 branches split:

| Original SU3³ matter block | Left-handed 4D | Right-handed 4D |
| --- | ---: | ---: |
| \(A=(3,\bar3,1)\) | 6 | 3 |
| \(B=(\bar3,1,3)\) | 6 | 3 |
| \(C=(1,3,\bar3)\) | 4 | 5 |
| **TOTAL** | **16** | **11** |

The LEFT chiral content under \(SU(3)_c\times SU(2)_L\times U(1)_Y\), using \(Y\) above, is
\[
Q_L:(3,2,+1/6),\quad
u^c_L:(\bar3,1,-2/3),\quad
d^c_L:(\bar3,1,+1/3),\quad
L_L:(1,2,-1/2),\quad
e^c_L:(1,1,+1),\quad
\nu^c_L:(1,1,0).
\]
Its dimensions \(6+3+3+2+1+1=16\) match **one E6/SO10-type chiral generation**. This is meaningful ORIGINAL E6 group-theory content, recovered by the SELECTED orbifold parity; it does not yet explain fermion masses or family replication.

The eleven RIGHT modes form an **SM-subgroup vectorlike 10 plus neutral singlet**: \(D_R:(3,1,-1/3)\), \(\bar D_R:(\bar3,1,+1/3)\), \(H_R^+:(1,2,+1/2)\), \(H_R^-:(1,2,-1/2)\), \(N_R:(1,1,0)\), dimension \(3+3+2+2+1=11\). Their gauge-invariant masses and decoupling have NOT been supplied. Under the chosen scalar parities, \(\Chi\) retains candidate scalar \(SU(2)_L\) doublets of \(Y=\pm1/2\), another useful DONOR for electroweak Higgsing; neither a tachyonic doublet nor observed mass/VEV is yet derived.

## Independent exact local four-dimensional anomaly checks

`scripts/check_kk_e6_orbifold_vev_anomaly_gate.py` enumerates **all 27 states** with exact rational hypercharges and left/right parity signs, derives the L/R even-generator stabiliser in an actual SU3 Hermitian matrix basis, tests the real source six-invariant potential under sign flip, and verifies the IR anomaly coefficients:

| Post-VEV unbroken gauge consumer | Selected integrated 4D coefficient |
| --- | ---: |
| \(SU(3)_c^3\) | 0 |
| \(SU(3)_c^2 U(1)_Y\) | 0 |
| \(SU(2)_L^2 U(1)_Y\) | 0 |
| \(U(1)_Y^3\) | 0 |
| gravitational-\(U(1)_Y\) | 0 |
| \(SU(2)_L\) Witten mod-2 | 6 Weyl doublets = even |

**This is a strong IR necessary check, not a full gauge/anomaly proof.** There is no physical single photon until the \(SU2_L×U1_Y\) candidate electroweak scalar sector is reduced further, and possible local orbifold fixed-plane anomalies remain independent.

## Decisive upstream anomaly obstruction

For the UV anomaly table, the **central** pre-VEV U(1)_R generator is diag(−1,−1,2), unlike the final hypercharge projection T_R=diag(−4,2,2), which also contains an SU(2)_R Cartan component. This distinction is necessary: a generator used as an independent U(1)_R factor must commute with SU(2)_R. The table below uses the commuting UV generator, not the final Y_R projection.

The orbifold gauge symmetry **before** E32/E33 breaking is
\[
SU(3)_c\times SU(2)_L\times U(1)_L\times SU(2)_R\times U(1)_R.
\]

The same exact zero-mode spectrum yields NONZERO integrated coefficients in its natural integer-charge convention:

| UV unbroken orbifold gauge anomaly | Coefficient |
| --- | ---: |
| \(U(1)_L^3\) | +40 |
| \(U(1)_R^3\) | −40 |
| \(U(1)_L^2U(1)_R\) | +8 |
| \(U(1)_LU(1)_R^2\) | −8 |
| gravitational-\(U(1)_L\) | +16 |
| gravitational-\(U(1)_R\) | −16 |
| \(SU(3)_c^2U(1)_L\) | +2 |
| \(SU(3)_c^2U(1)_R\) | −2 |
| \(SU(2)_L^2U(1)_L\) and \(SU(2)_R^2U(1)_L\) | +2 each |
| \(SU(2)_L^2U(1)_R\) and \(SU(2)_R^2U(1)_R\) | −2 each |

These are normalisation-relative source coefficients, not measured anomalies. For a gauge zero mode whose gauge transformation has the SAME value at both fixed planes, a bulk five-dimensional CS descent generates **opposite-sign endpoint variations**. Regardless of bulk coefficient k, they sum to zero. The NONZERO integrated 4D anomaly is therefore NOT cancelled by classical 5D bulk CS inflow alone.

Explicit source test `scripts/check_kk_e6_orbifold_fixed_plane_anomaly.py` checks a symmetric representative: local orbifold anomaly \((A/2,A/2)\) plus CS inflow \((-k,+k)\) gives equations \(A/2-k=0\), \(A/2+k=0\), which imply \(A=0\). For each nonzero A above, NO k solves the pair. The integrated argument is independent of precisely how anomaly density is distributed between endpoints: endpoint inflow sums to zero. **To make this UV gauge action admissible**, one needs physically specified additional boundary/bulk fermions, a consistent anomaly-cancelling Wess–Zumino/Green–Schwarz/Goldstone sector, or modified gauge/boundary symmetry—not an arbitrary change in CS level.

This is a stronger source-obstruction than simply finding a locally integral five-dimensional half-CS shift in the earlier smooth-circle model. It keeps the original #1241 5D CS parity work useful without falsely treating it as a completed orbifold anomaly cure.

## Gauged SU3³ is NOT full gauged E6

The 78-dimensional E6 adjoint decomposes under SU3³ as \((8,1,1)+(1,8,1)+(1,1,8)+(3,3,3)+(\bar3,\bar3,\bar3)\) in a conventional orientation. Under the selected \(P_c=1,P_L=P_R=\mathrm{diag}(-,-,+)\):
- SU3c×SU3L×SU3R even adjoint dimension = **8+4+4=16**.
- Two off-diagonal E6 27-dimensional gauge-generator sectors have **15 even and 12 odd EACH**, so **30 more even** gauge generators.
- A FULL gauged E6 would have **46 orbifold-even zero-mode gauge generators** before its Higgs source, not 16.

The #1106 comparison potential acts on TWO truncated complex bifundamentals (36 real). It is SU3L×SU3R invariant but **not shown E6 invariant** and not closed under all E6 gauge transformations. Thus the actually checked construction is an **E6-motivated SU3³ trinification gauge EFT** with a 27 matter carrier, not a fully gauged E6 orbifold. To upgrade, supply complete 27 scalar multiplets, adjoint/coset gauge-mass operators, involution action, full gauge potential, and recompute every anomaly and spectrum. Same cardinal or group-root result is not physical equivalence.

## Pareto decision / highest-value next consumers

**P0 selected chiral IR source = CONDITIONAL POSITIVE**. We have a concrete 27→16L+10R+1R parity model, old E32/E33-compatible Higgs potential, and vanishing tested post-VEV 4D subgroup anomalies. This significantly raises the value of pursuing this particular orbifold gauge candidate compared with further smooth-S1 mass numerology.

**P1 source UV consistency = FAIL**. The pre-VEV gauge theory is anomalous for one bulk Dirac27. Adding an identical intrinsic-parity-opposite 27 would trivially offset many source anomalies but can also erase the desired chiral content. Seek **minimal anomaly-completing** boundary matter/inflow/G-S physical action while retaining net chiral16; derive exact zero-mode charge/anomaly table of EVERY additional field. No speculative solution is counted as paid.

**P2 one photon = OPEN**. The orbifold+E32/E33 leaves SU2L×U1Y (colour external). Source an even electroweak scalar doublet with a physically selected potential, derive exactly one unbroken U1_EM with observed charges and no independent old U1_B. The existing KK QED Casimir photon \(B\) is not silently the same vector; replace and recompute it.

**P3 full orbifold quantum vacuum = OPEN**. Orbifold interval length, zero/odd/even KK spectra, gauge ghosts/Goldstones, Higgs, fermions and fixed-plane action differ from the previous periodic-S1 winding function. Rebuild \(V(b,\theta,\mathrm{VEVs})\), renormalization and metric stress from the selected source. Old QCD + E6 Higgs + spurion D>409 no-go applies ONLY to that old smooth periodic spectrum; it is a benchmark negative control, not a proof against this different model.

**P4 gravitational observation = OPEN**. Only after one gauge/anomaly/source-complete 5D action, apply existing #1165 same-metric-path action→stress, #1241 sourced radion and selected GR/T55, and test LARES/PPN/fifth-force predictions against external experimental records. No present result implies antigravity, anomalous satellite motion or a TOE.

## Verification and attribution grades

- **Independently reproduced exact SymPy/Fraction script** for parity matrices, source six-invariant potential, 8 even L/R gauge generators, 4-dimensional VEV stabiliser, 27 charge/parity enumeration, IR and UV gauge anomaly coefficients, and 46 even FULL-E6 adjoint counterexample: PASS.
- **Independent exact fixed-plane inflow script** for selected 16+10+1 grouping and nonzero-integrated-anomaly CS-only no-go: PASS.
- **Finite Agda BIDI** `DASHI/Physics/Gravity/KKE6OrbifoldVEVAnomalyModelForkExact.agda`: selected matrix parity multiplication and typed "IR ≠ UV" / "SU3³ gauge ≠ full E6" non-descents; SOURCE-WRITTEN, KERNEL UNVERIFIED. Its concrete anomaly Boolean is a LABEL from source script, NOT a kernel proof of continuum triangle diagrams or orbifold APS.
- No full 5D anomaly-inflow model, physically viable scalar/superpartner masses, full gauged E6, experimentally calibrated fermion family or chiral Standard Model construction has been established. Retain Slansky, Arkani-Hamed/Cohen/Georgi and Scrucca et al source priority separately from original repository checks.


## Later restricted parity search and five-dimensional mass-source veto

**No parity-only repair inside this exact diagonal family:** `scripts/check_kk_e6_orbifold_parity_scan_no_go.py` exhausts ALL determinant-one diagonal involutions (P_Rin SU3_R) while fixing (P_c=1) and (P_L=mathrm{diag}(-,-,+)) so colour and the selected (SU2_L) survive. The source exact-rational coefficient table is:

| (P_R) | (SU3_c^3) | (U1_L^3) | canonical (U1_R^3) |
| --- | ---: | ---: | ---: |
| (I) | +4 | 0 | 0 (full (SU3_R), no central (U1_R) distinguished) |
| (mathrm{diag}(-,-,+)) | 0 | +40 | −40 |
| (mathrm{diag}(-,+,-)) | 0 | +40 | −40 |
| (mathrm{diag}(+,-,-)) | 0 | +40 | −40 |

Hence **none of those four candidates eliminates all of the pre-VEV gauge anomalies for one 27**. This is a restricted family and does NOT rule out different gauge parities, representations, boundary spectator matter or a consistent anomaly-cancelling Goldstone/Green–Schwarz sector. The canonical UV generators are (T_L=mathrm{diag}(-1,-1,2)) and (U1_R=mathrm{diag}(-1,-1,2)) for the selected (mathrm{diag}(-,-,+)) projector; DO NOT conflate the latter with the final hypercharge (T_R=mathrm{diag}(-4,2,2)), which has an (SU2_R) Cartan component before VEV breaking.

**Old smooth-circle mass sector does NOT transport:** `scripts/check_kk_orbifold_bulk_mass_parity.py` verifies explicitly (gamma^5gamma^0gamma^5=-gamma^0). Under the candidate reflection (Psi(-y)=gamma^5ho(P)Psi(y)), the 5D Dirac bilinear (arPsiPsi) is odd; an ordinary constant-even bulk Dirac mass coefficient would make the term odd and is FORBIDDEN. A parity-odd kink/background mass or compatible boundary/multiplet mixing changes the action and is a possible new source, not presently constructed. The previous 3/4/9TeV smooth-circle Dirac and spurion mass input cannot simply be imported into the chiral orbifold quantum determinant.

**Updated Pareto conclusion:** the positive chiral (16_L) plus SM-vectorlike (10_R+1_R), old E32/E33 parity-compatible source quartic, and IR anomaly cancellation justify this as the leading **research candidate**, but its UV pre-VEV anomaly and source-derived mass parity make it **NOT an admissible completed physical theory**. The next model change must pay boundary/fixed-plane UV gauge consistency without erasing the chiral 16, then introduce an allowed mass/VEV structure, derive one EM photon and compute NEW interval Casimir/metric stress. The exact finite source status is also recorded in `KKE6OrbifoldVEVAnomalyModelForkExact.agda`; the Agda file is kernel UNVERIFIED.


## 2026-10-25 one-anomalous-direction WZ/GS alternative to mirror fermions

The pre-VEV UV obstruction above remains a REAL FAILURE of the unaugmented source. A stronger direct next producer is documented in `KKE6OrbifoldGreenSchwarzPhotonSourceMaxCut20261025.md`: exact 27-weight polynomial `(F_L−F_R)(40F_L²+64F_LF_R+40F_R²)`, corresponding gravitational coefficient `16(F_L−F_R)` and each tested SU3c²/SU2L²/SU2R² mixed coefficient `2(F_L−F_R)`. Thus one anomalous Abelian direction is sufficient at the LOCAL polynomial level. Original von Gersdorff/Quirós 2003 source distinguishes local GS WZ mixed-U1 cancellation from CS-only opposite-endpoint inflow, and warns surviving anomalous U1 becomes massive. This could preserve the chiral16 and the anomaly-free hypercharge (Y=(U_L+U_R-3H_R)/6).

One existing source candidate is the Chi E33 phase with central charges (+2,-2), but a=argChi33/2 has an unresolved GLOBAL half-phase/charge-lattice and possible Z2 WZ sign on unit instanton backgrounds. No source-constructed globally single-valued counterterm is claimed. Exact neutral 4x4 Gram rank test shows source E32/E33 2 VEVs leave SU2L×U1Y; a GS mass parallel to their broken Chi direction leaves rank unchanged; and an even Chi E21 EW VEV would then leave one EM photon. The latter EW vacuum is NOT the original positive-Hessian #1106 V6 minimum and requires new dynamics. These conditional results upgrade the steelman without clearing the UV quantum anomaly, full E6 gauging, new orbifold Casimir or physical source stress.


## 2026-10-25 explicit positive orbifold-even Higgs Hessian

The positive original E21 curvature and limited unbroken SU2L×U1Y source have been taken beyond a toy Cartan rank. New `scripts/check_kk_e6_orbifold_boundary_higgs_source.py` derives exactly `V6(E32,E33+tE21)=3t²+t⁴` from the actual original six-invariant E6 two-bifundamental potential. A FIXED-PLANE, parity-even 2×2 Chi block term `−mu²||P2ChiP2||²+lambda||P2ChiP2||⁴`, invariant under the actual reduced orbifold gauge group, can create a nonzero EW component. The ORIGINAL E32/E33 amplitudes must shift: exact source stationary equations `a²=1−t²/2,b²=1−2t²,mu²=3+(2lambda−6.5)t²`.

For selected `lambda=4,t=.0246`, complete source numeric 36-real gradient ≈0. Full 36 Hessian has two NEGATIVE eigenvalues, but they lie in ORBIFOLD-ODD scalar fluctuations with no constant modes. Only 18 real orbifold-even zero-mode scalar directions are physically relevant to this consumer; their Hessian has `7` gauge-orbit zero directions and `11` positive modes, smallest +0.00362163, no negatives. This is coherent with 8 even gauge generators broken to exactly one EM generator. The FULL odd KK tower, fixed-plane terms, quantum effective potential, regulator-complete UV Green–Schwarz WZ, and observed Higgs/photon couplings remain genuinely open. Canonical mathematical and provenance report: `Docs/physics/KKE6OrbifoldBoundaryHiggsHessianMaxCut20261025.md`.

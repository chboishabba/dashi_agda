# E6 two-VEV × KK same-action physical max-cut — 2026-10-24

**Owner:** [Agda KK PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241). This corrects the earlier two-extra-massless-SU3-octet 48-unit shortcut. Proof statuses are source-specific.

## Inspected original owners, not rediscoveries

- [Agda E6/F4/first-Tits/trinification PR #1106](https://github.com/chboishabba/dashi_agda/pull/1106), stacked on #1098: Ternary27TrinificationE6SameActionExact (same literal M3^3 cubic and SL3^3 action); Ternary27TrinificationTwoNeutralVEVBreakingExact; Ternary27TrinificationTwoVEVGeneralMassSpectrumExact; Ternary27TrinificationTwoVEVLocalStabilityExact; Ternary27TrinificationOct14GaugeMaxCutExact. Existing results: E32/E33 neutral directions in TWO complex 3x3 bifundamental scalars, LR stabilizer SU2_L×U1_Y, colour SU3_C unchanged; four unbroken and twelve broken LR gauge generators. Equal-unit broken vector mass-squared shape (1/4)^4,(1/2)^7,(5/6)^1. Scalar comparison Hessian zero^12,4^6,6^8,8^10 on 36 real components; twelve zero directions match the broken gauge tangent. These remain local computation/source-written receipts, NOT physical mass calibration or present-head kernel proof.
- [Torque/SO3 #1164](https://github.com/chboishabba/dashi_agda/pull/1164) and [Hopf U1 #1235](https://github.com/chboishabba/dashi_agda/pull/1235) provide different spatial torque and circle-bundle consumers. The selected SO3 Lie algebra is perfect and admits no nonzero homomorphism into abelian U1; there is no physically justified torque-as-fifth-dimension identification.
- The existing FermionicLoopCSShiftReceipt.agda is a conditional SU2 Kac-Moody level 3→1 bookkeeping surface, NOT a constructed five-dimensional SU3×U1 Chern–Simons action.

**Original external literature:** Bonetti, Grimm, Hohenegger, *One-loop Chern–Simons terms in five dimensions*, JHEP07(2013)043, DOI 10.1007/JHEP07(2013)043 (parity-odd gauge/gravitational loop terms); *Comments on Global Symmetries and Anomalies of 5d SCFTs*, Commun. Math. Phys. 2024, DOI 10.1007/s00220-024-05139-8 (five-dimensional CS level/quotient restrictions). Trinification phenomenological actions/breaking: *Scale hierarchies, symmetry breaking, and particle spectra in SU(3)-family extended SUSY trinification*, PRD99(2019)035041, DOI 10.1103/PhysRevD.99.035041, and Babu/Bajc/Susic, *Trinification from E6 symmetry breaking*, JHEP07(2023)011, DOI 10.1007/JHEP07(2023)011. None prove the physical viability of this selected DASHI 5D spectrum.

## Correct gauge-Higgs spectral budget

Five-dimensional massless vector: 3 polarizations. Five-dimensional massive Higgsed vector: 4. TWO complex 3x3 bifundamentals: 36 real scalar fields. E6 #1106's actual VEV stabilizer breaks 12/16 LR gauge generators and eats 12 scalar Goldstones, leaving 24 physical scalar modes.

- Before symmetry breaking: (16 massless vectors ×3) + 36 real scalars = **84**.
- After: (4 unbroken vectors ×3) + (12 massive vectors ×4) + (24 uneaten physical scalars) = **12+48+24=84**.

Thus treating the same E6 branch as 16 EXTRA permanently massless vectors contributing ONLY 48 bosonic Casimir units is NOT the actual physical source. Nor may the eaten 12 Goldstones be included again after using four polarizations for massive vectors.

The executable check_kk_e6_two_vev_source.py instantiates the ORIGINAL equal-unit masses as a clearly SYNTHETIC common-VEV scale v and computes the selected noninteracting periodic S1 contribution to the stationarity defect D=W'(1)-5W(1), with the source quark/gluon sector. At reference radius b0=1e-24m:
- QCD quarks/gluons alone contribute approximately -239.99999999979.
- The selected 4 massless vectors + 12 massive vectors + 24 physical scalar mode masses for v=10 TeV contribute +419.999989813728.
- Total INCREMENTAL defect = **+179.999989813938**, not zero.
- In the selected equal-unit scalar/gauge normalization only, the incremental defect happens to vanish at v≈86,935,854.28065 GeV, which is 0.4405675/b0 (natural units). This pays one equation for these sectors, NOT the full KK vacuum. All other previous baseline fields, the E6 27 matter spectrum, actual gauge couplings, physical Higgs quartics, metric source and mixed Wilson/VEV Hessians remain excluded from that limited comparison. This is no predicted VEV.

The source E6 Higgs Hessian was obtained in an independently chosen comparison potential; reading its eigenvalues as physical squared masses at this v is an EXPLICIT NEW ASSUMPTION, not a same-action theorem. Graviton/gauge/Goldstone ghosts must be handled with consistent gauge fixing in the actual one-loop determinant.

## Constructive classical interacting 5D EFT ansatz — not a full SUSY/E6 model

A candidate five-dimensional gauge-invariant EFT uses an Einstein-Hilbert term, bulk cosmological counterterm, SU3_C×SU3_L×SU3_R and optionally a separate U1_B Yang–Mills kinetic term, covariant kinetic terms for two bifundamental Higgs fields Phi_1,Phi_2, a gauge-invariant V(Phi_1,Phi_2), colour-triplet Dirac fermions Psi_i, TWO complex colour-triplet scalars S_i,a for each Dirac, adjoint colour matter, and a properly quantized CS counterterm:

S5 = ∫d5x sqrt(-G)[ M5^3 R5/2 - Lambda5 - Σ_I tr(F_I^2)/(4g_I5^2) - H_B^2/(4e_B5^2) - Σ_(a=1,2)|D Phi_a|^2 - V(Phi_1,Phi_2) - Σ_i barPsi_i(iGamma·D-M_i)Psi_i - Σ_(i,a)(|D S_i,a|^2 + m_Si^2|S_i,a|^2 + lambda_i,a|S_i,a|^4) + L_adjoint ] + S_CS.

For the illustrative mass-split free determinant choose m_Si^2=M_i^2+Delta_i^2>0. Exotic M_i=9 TeV, scalar m_S=3 TeV gives Delta_i^2=-72 TeV^2: the SOFT coefficient is negative, but the total scalar quadratic is POSITIVE, and lambda>=0 stabilizes the isolated scalar origin. script check_kk_soft_source_action.py verifies the elementary algebra and SU3 representation norm. This is a **classical gauge-covariant EFT with explicit input mass terms**, NOT a derived soft-SUSY-breaking spurion, off-shell 5D superfield action, or proven complete anomaly-compatible theory. Gauge interactions modify the one-loop free determinant at higher order; the spectrum must be regenerated from the full actual action.

## Double-photon same-object failure

The earlier QED-only #1241 uses an INDEPENDENT bulk Maxwell B_mu as the physical photon, keeping geometric KK graviphoton A_mu distinct. But E6 #1106 already has SU2_L×U1_Y, which upon electroweak Higgsing yields a photon generated by Q=T3+Y. If B is simply added and the SM Higgs is neutral under B, the neutral gauge charge vector in (B,T3,Y) is q=(0,-g2/2,gY/2). The Higgs mass Gram v^2 q q^T has rank one and TWO independent massless U1 directions (one B, one EW photon). With geometric graviphoton the theory has yet another ultraweak massless U1 unless separately handled.

**Required physical branch decision:** either remove/identify B as the observed photon and derive the actual electroweak Q Wilson spectrum from E6 with all quark/lepton charges and mixed gauge kinetic terms, OR retain B and introduce an actual independent Higgs/mixing current which removes/decouples the extra photon. No old numerical B-photon Wilson curvature is automatically transportable to the E6 residual photon.

## Selected 5D parity/CS lattice — NECESSARY not sufficient

The eight SU3 fundamental five-dimensional Dirac candidates of the previous paired-QCD toy have electric charges (2/3,-1/3,-1/3,2/3,-1/3,2/3,2/3,-1/3). In integral normalization q3=3Qem this is (2,-1,-1,2,-1,2,2,-1). These all satisfy triality+q3=0 modulo3 for the selected diagonal (SU3×U1)/Z3 quotient; the electron is colourless q3=-3.

Their charge moments Σq3^n, n=0,1,2,3, are (8,4,20,28), all EVEN, with nominal half-shift integer witnesses (4,2,10,14). An additional adjoint Dirac has doubled SU3 Dynkin index 6, so its elementary half-shift is 3. The exact Fraction script check_kk_5d_parity_cs_charge_lattice.py verifies this counting and one-mass-sign flips.

This is only a necessary arithmetic check under a declared normalisation: the complete 5D spin CS quantization lattice for the quotient gauge group, higher-order/mixed gravitational CS terms, regulated parity-odd fermion eta invariant, actual light modes, bulk/boundary anomaly inflow, and possible bare CS counterterms remain OPEN. Eight vectorlike flavours do not automatically prove a physically consistent chiral compactified Standard Model, and light quarks must not be improperly integrated out.

## Verification and roadmap

New artifacts on #1241:
- scripts/check_kk_e6_two_vev_source.py — independently executed equivalent SymPy/mpmath, PASS.
- scripts/check_kk_5d_parity_cs_charge_lattice.py — independently executed exact Fraction arithmetic, PASS.
- scripts/check_kk_soft_source_action.py — independently executed core SymPy mass/representation audit, PASS.
- DASHI/Physics/Gravity/KKE6TrinificationSourceConsumerBIDIExact.agda — exact FINITE 84-degree count and three consumer non-descent predicates. Source-written, **no Agda kernel receipt**. Sibling #1106 referenced by source/PR, NOT imported as a theorem.
- Existing #1106 and #1164 scientific owners unchanged; separate roadmap updates document cross-PR dependencies without silent merge.

**Pareto next:**
1. Decide the physically observed photon operator, remove/identify independent B or pay an extra gauge-breaking source. Recompute its actual Wilson determinant.
2. Construct SAME 5D E6 two-VEV kinetic, Higgs scalar coefficients, full 27 matter and vacuum spectrum, including 24 physical Higgs modes and broken gauge vectors, with consistent gauge fixing.
3. Compute full mixed spin-CS/large-gauge/parity functional for actual gauge quotient and regulator.
4. Solve all-field radion, EM, colour, and both Higgs VEV stationary equations with mixed Schur-complement Hessian/global-vacuum bounds, then derive stress T_AB from THE SAME action.
5. Build a conserved pressure-supported rotating material Earth and actual held-out geodetic observable only after the full gauge/matter source is admissible.

Spatial SO3 torque / Hodge and Hopf circle geometry provide separate legitimate donor structures, not a shortcut past these source-specific physical equations. **No accepted TOE, complete E6 symmetry breaking, empirical antigravity, or satellite anomaly is claimed.**


## Additional crucial source distinction: selected LR 3×3 vs complete 27 and gauged E6

The preceding **84** counts ONLY the gauged SU3_L×SU3_R sixteen-generator sector, with TWO selected 3×3 complex bifundamentals (36 real). The source #1106 calls them two selected components/directions from 27 carriers; it does not automatically prove that 2 entire complex 27-plet scalar multiplets have the SAME 36-real-coordinate Hessian. If one elects full dynamical 27s, there are **2×27×2=108** real scalars and 96 uneaten after the 12 LR Higgs Goldstones: 16×3+108 = 4×3+12×4+96 = **156** free bosonic polarization units. The 72 previously omitted real scalar modes have UNPAID masses/interactions and cannot inherit the selected 24-Higgs comparison spectrum.

Likewise gauging physical colour SU3_C is another EIGHT massless vectors, already separately counted in #1241's QCD baseline. The source-branch count table is:

| Declared physically gauged group and Higgs source | Before | After | Units |
| --- | --- | --- | --- |
| SU3_L×SU3_R, 2 selected complex 3×3 | 16×3+36 | 4×3+12×4+24 | **84** |
| SU3_C×SU3_L×SU3_R, 2 selected complex 3×3 | 24×3+36 | 8×3+4×3+12×4+24 | **108** |
| SU3_C×SU3_L×SU3_R, 2 entire complex 27s | 24×3+108 | 8×3+4×3+12×4+96 | **180** |
| FULL E6 gauge algebra (78), illustrative real 650 Higgs E6→SU3³ plus two entire complex 27s | 78×3+(650+108) | 12×3+66×4+(758−66) | **992** |

The last example is a DIFFERENT published E6-source candidate, relying on a real 650 to break E6→SU3³ (Babu/Bajc/Susic 2023/2024), not already present as a physical 5D scalar in #1106. This table is free-field DOF bookkeeping, NOT a massless-Casimir coefficient for all modes: many are gauge-Higgs massive and may decouple, and actual 5D mass/Higgs/ghost spectra depend on the specific same action. The source-to-physics model selection must happen BEFORE attempting a universal radion or Wilson determinant.

When two entire 27s plus a 650 are used, the selected 36-coordinate scalar Hessian from the #1106 comparison potential cannot certify stability of the other **722** real Higgs coordinates (650+72), nor their cosmological-stress effects. This exposes a much larger physical representation-realisation obligation than the original 48-unit octet shortcut.


## Physical trace and mixed Hessian corrections (latest)

For the selected eight Dirac **colour fundamentals**, the unweighted integer charge moment list (8,4,20,28) and half-moments (4,2,10,14) are a **combinatorial test**, NOT four physical 5D Chern–Simons levels. In a pure U1/gravitational trace every fundamental has THREE colour components, so the appropriately colour-multiplied formal half-moments are sum(3 q3)/2=**6** and sum(3 q3³)/2=**42**, respectively. The mixed U1–SU3² coefficient instead contains the fundamental Dynkin-index trace and requires separately declared normalization. The required spin CS integrality lattice of the quotient group remains entirely unproved. This latest correction supersedes interpreting (4,2,10,14) directly as correctly normalized CS coefficients.

A second necessary consumer is the FULL mixed Hessian in (radion b, E6 VEVs v32/v33, EM/colour phases). Even if separate scalar-Higgs and radion Hessian blocks are positive, positivity of their joint fluctuation matrix requires the **Schur complement**
H_eff,rr = H_rr - H_rPhi (H_PhiPhi)^(-1) H_Phir > 0
(and the remaining mixed Wilson blocks likewise). check_kk_e6_two_vev_source.py includes an explicit SYNTHETIC 3×3 counterexample with H_PhiPhi=diag(4,6), H_rr=15, H_rPhi=(8,0): both separate blocks are positive but Schur =15-16=-1. The cross entry 8 is **NOT** a measured or source-derived value. This demonstrates why inheriting the #1106 scalar-local spectrum and a positive #1241 radion curvature does NOT prove a common E6 KK vacuum.

In the selected classical spectator scalar EFT, Δsoft²<0 is an adjustable coefficient and the physical m_S² remains positive; that only guarantees an isolated tree-level scalar origin for nonnegative quartic, not quantum stability of all coloured scalars and electroweak states. A complete gauge-invariant, spin-regulated quantum action is still a distinct source obligation.


## Stronger full paired-QCD + dynamical-spurion no-go and full 27 alternative (2026-10-24)

**Later critical recut:** see \`Docs/physics/KKE6TrinificationInteractingActionParityVacuumMaxCut20261024.md\`. The prior part above already correctly discovered the 84-mode source and the 10TeV Higgs-only QCD residual ≈+180. That was an incremental result, not a guarantee that the latest 8-flavour split-scalar spectrum or physical mass-source action survived.

New source scripts:
- \`scripts/check_kk_trinification_higgs_5d_mode_budget.py\` — same Higgsed two-bifundamental 84-mode sector with mass scale g=.65, VEV=10TeV and quartic spectral λ=.1; gives a *neutral-stabilizer-independent* stationary vacuum defect D>164 in the older six-quark/E6-octet reference at b0=1e-24m. Only that selected action and TeV mass regime are excluded.
- \`scripts/check_kk_5d_spurion_parity_cs_source.py\` — specifies a candidate **dynamical** 5D gauge-singlet X with V_X=λ5(X²−w5²)², Yukawa (M_i+y5 X)barPsiPsi, scalar portal (μ_i²+κ5 X²)|S_i|². At w4=1TeV and properly normalized 5D couplings y5=y4 sqrt(2πb0), κ5=κ4(2πb0), λ5=λ4(2πb0), it reproduces the 3/9TeV scalar/exotic fermion mass inputs with positive scalar squared masses, while adding a NEW propagating X scalar of mass ~1.78885TeV. This makes the old fixed free-field one-loop spectrum INCOMPLETE, not automatically an interacting SUSY/QFT completion.
- \`scripts/check_kk_joint_e6_qcd_spurion_radion_pressure.py\` — genuinely combines the old eight-flavour paired SU3c×U1_B free Casimir with the SOURCE-REQUIRED 84 L/R Higgsed bosonic modes and X fluctuation. At the previously stationary mass parameter z≈0.9081569400, the new same-spectrum defect is **D≈+424.9999986**, and for *every* neutral-fermion z>0 the analytic periodic kernel bound gives **D>409** at b0=1e-24m with the selected 3/4/9TeV QCD split masses and <30TeV new Higgs/gauge masses. The 5D internal pressure p5=−c0 D/(2πb0^5) therefore cannot vanish after flat 4D vacuum energy retuning.
- \`scripts/check_kk_e6_full27_hyper_cs_supertrace.py\` — source-faithful expansion to **two full complex 27 Higgs fields**, not the prior 36-real truncated sector: 108 real scalar fields, 12 eaten, 96 physical; 4 massless and 12 massive LR vectors give 156 boson modes. A hypothetical FULL 5D N=1 vector multiplet adds 16 real adjoint scalars; one 27 hypermultiplet adds a Dirac 27. Count becomes **172 bosons =172 fermions**, potentially cancelling a full free winding determinant *only if mass, Wilson character and kinetic operators match mode-by-mode*. The entire full-27 potential and 108-real Hessian are still OPEN. The 27=(3,bar3,1)+(bar3,1,3)+(1,3,bar3) has local pure cubic SU3 index +3−3=0 per each factor under one uniform fermion mass sign. Unlike just one (3,bar3) Dirac (±3/2 half-level), this condition avoids the elementary half-index, but does NOT prove global mixed/parity/CS.

**No new physical closure claimed.** These are SOURCE-WRITTEN/locally independently numerically checked gates. The 5D scalar normalization, gauge-fixing/Goldstone determinant, quantum tadpoles, global CS/quotient, full E6 650 vs truncated-27 alternatives, 5D stress conservation, actual observed EW photon and full joint multi-holonomy potential remain outside the paid set. The torque SO3 source stays independent of the fibre U1 action. This latest no-go is a controlled way to RETIRE an inadmissible TeV parameter slice, not a universal exclusion of E6 or KK theories.

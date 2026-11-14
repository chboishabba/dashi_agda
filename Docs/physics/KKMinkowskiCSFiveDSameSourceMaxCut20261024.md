# Native Minkowski and Chern–Simons prior art: five-dimensional E6/KK source audit (2026-10-24)

**LATEST 2026-10-25 CS/WZ SPIN-INDEX CORRECTION:** The earlier apparent \(\mathbb Z_2\) Chi33 half-phase obstruction was conditional on *symmetric independent WZ terms at both fixed planes*, not a universal charge-two no-go. [CS transfer/spin-index owner](KKE6OrbifoldCSWZTransferSpinIndexMaxCut20261025.md) explicitly redistributes the source half-anomalies by a 5D bulk CS variation \((+I_6/2,-I_6/2)\), yielding \((I_6,0)\). A SINGLE first-plane Chi33 WZ term \(-\theta_\Chi X_4/2\) then cancels the local anomaly; every coefficient is integral in the original **unnormalised source trace lattice**. Spin \(\mathbb CP^3\) full-27 indices are even for arbitrary integral two-U1 fluxes (proved via nine residues modulo three), as are selected \(S^2\times S^4\) instanton and \(S^2\times K3\) families. This is significantly more promising than extra mirror fermions, but DOES NOT establish the true integral spin/quotient CS, all APS eta/torsion sectors or a complete anomaly-free 5D QFT. Earlier global half-phase warnings remain valid ONLY for their specific two-brane ansatz.\n\n
**Owner:** [Agda KK PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241), branch `lares2-kk-observable-maxcut-20261023`. **Existing E6 owner:** [Agda #1106](https://github.com/chboishabba/dashi_agda/pull/1106). **TOE:** [Agda #1217](https://github.com/chboishabba/dashi_agda/pull/1217), [Lean #80](https://github.com/chboishabba/dashi_lean4/pull/80).

## Attribution: the work ALREADY present, and what it actually says

These are existing **source-written repository theorem/receipt owners**; they are not newly derived mathematical phenomena or interchangeable physical theories.

| Existing canonical file (default branch unless noted) | Actual source scope | Not supplied by that file |
| --- | --- | --- |
| `DASHI/Physics/Closure/MinkowskiLimitReceipt.agda` | B4 intrinsic exact 3+1 Lorentzian flat quadratic form over `HFZ.CausalCountsZ 3` | Continuous dynamical 5D Einstein matter source; nonflat curvature |
| `DASHI/Physics/Closure/GRConcreteLeviCivita.agda` | Selected flat metric-compatible Levi-Civita closure on finite carrier, source explicitly keeps nonflat GR open | Five-dimensional sourced Einstein equation or measured Earth |
| `DASHI/Physics/Closure/DiscreteEinsteinVacuumLimitSurface.agda` and `EinsteinEquationCandidate.agda` | Exact conditional flat-vacuum diagnostic and named missing nonflat W4 matter/Einstein primitives | Continuum nonflat Einstein/Ricci source |
| `DASHI/Physics/QFT/KacMoodyLevelReceipt.agda` | Explicitly separates a 2+1D CS level from affine/WZW level; SU2 weak candidate | A genuine 5D CS five-form or physical SM |
| `DASHI/Physics/QFT/CSLevelFlowFullReceipt.agda` | Conditional p2/p3/p5 CS level-flow and level-rank candidate | Bare/induced 5D SU3c×SU3L×SU3R×U1_B spin CS levels |
| `DASHI/Physics/QFT/FermionicLoopCSShiftReceipt.agda` | Candidate finite SU2 k=3→1 shift, conditional on fermion matter and sign choices | SU3^3 full 27 parity-odd eta determinant in 4+1D |
| `DASHI/Physics/QFT/BulkBoundarySU3Receipt.agda` | A 2+1D SU3_1 CS boundary candidate for a 3+1D topological bulk | 4+1D nonabelian colour/KK bulk or 5D large-gauge invariance |
| `DASHI/Physics/QFT/EWSBFromCSHiggsReceipt.agda` | Electroweak symmetry breaking as conditional CS/Higgs topological candidate | Physical Higgs VEV, W/Z masses, single photon, full anomaly |
| `DASHI/Physics/Gravity/KKE6TrinificationSourceConsumerBIDIExact.agda` (#1241) | Exact finite DOF, photon and spatial torque/fibre non-descent | A regulator-complete global quantum 5D functional |
| `DASHI/Physics/Closure/Ternary27Trinification...agda` (#1106) | Actual E6 cubic/SL3³ and E32/E33 two-VEV source, rank12 gauge breaking and 36-real local Higgs comparison | The full108-real Higgs potential, 5D local quantum stress, mass-sign spectrum |

**No missing prior art claim:** the CS and Minkowski research programs EXIST. The unfinished critical consumer is the *same actual five-dimensional action* in which source-selected E6 masses/charges, the 5D parity-odd regulator and 4D×S1 stress all appear.

**Original external scientific source roots, separate from DASHI code:** Federico Bonetti, Thomas Grimm and Stefan Hohenegger, *One-loop Chern-Simons terms in five dimensions*, JHEP 07 (2013) 043, DOI **10.1007/JHEP07(2013)043**, original calculation of 5D induced gauge/gravitational CS interactions; Christopher T. Hill, *Anomalies, Chern-Simons terms and chiral delocalization in extra dimensions*, Phys Rev D 73 (2006) 085001, DOI **10.1103/PhysRevD.73.085001**, 5D anomaly inflow/parity; *Comments on Global Symmetries and Anomalies of 5d SCFTs*, CMP 2024, DOI **10.1007/s00220-024-05139-8**, global forms, line/1-form and parity/CS. R. Slansky, *Group theory for unified model building*, Physics Reports 79 (1981), DOI **10.1016/0370-1573(81)90092-2**, original exceptional group branching. Sources are independent works with different target actions; no claim their abstracts establish our theory.

## Mathematical cut A: the CS FORM-DEGREE / same-source bridge

An intrinsic CS action in a 2+1D gauge theory is locally a degree-three form, schematically `A ∧ F`. A 4+1D gauge theory requires a degree-five form, e.g. Abelian `A ∧ F ∧ F` or a nonabelian five-form `tr(A F² − 1/2 A³ F + 1/10 A⁵)` with source-dependent normalization. Assigning the same label "Chern–Simons" or the same integer level cannot make the degree-three and degree-five actions *physically identical*. The affine/WZW boundary level additionally requires its own bulk/boundary descent and normalization.

**New source executable** `scripts/check_kk_minkowski_cs5_same_source.py`: a symbolic exterior-algebra wedge checker implements the exact selected mixed Abelian 5-form on `T5=S1×T2×T2` with connection `A_1=theta dx0`, curvature `F_2=2pi p dx1∧dx2`, `F_3=2pi q dx3∧dx4`, and integer fluxes p,q. In the **declared mixed U1^3 normalization**

`S5=(k/(2pi)^2) integral_(T5) A1 ∧ F2 ∧ F3 = k theta p q`.

One large-gauge winding `theta→theta+2pi` shifts `S5→S5+2pi k p q`, so `exp(iS5)` is invariant for integral k,p,q. This is a **fully checked example for this specific mixed Abelian product and normalization**, NOT a proof that an arbitrary `SU3³×U1_B` or `(SU3×U1)/Z3` global/spin CS functional has the right integral lattice or eta phase. (Nor does the result fix the bare k or fermion-induced shifts.)

**Agda owner:** `DASHI/Physics/Gravity/KKMinkowskiChernSimonsFiveDConsumerExact.agda`, importing old actual Minkowski/Kac-Moody/BulkBoundary/fermionicCS/LeviCivita source owners, gives finite exact degree (`1+2=3`, `1+2+2=5`) and the canonical `ClaimNonTransportWitness`: common CS keyword is insufficient to determine action dimension. This is a FINITE non-descent/provenance gate, **not** a kernel proof of differential-form integration (the symbolic exterior script supplies the latter computational case).

## Mathematical cut B: old flat Minkowski IS a valid prerequisite but not a KK solution

On the selected product `M^3,1 × S1` with constant radius b and metric components diag(-1,1,1,1,b²), Christoffels and Riemann/Ricci/Einstein tensors vanish. This is a valid *kinematic* 5D Ricci-flat background. Its physical validity with matter requires all source Einstein components, particularly `T55`, to vanish. The existing B4 signature/Levi-Civita receipts support the flat 4D prerequisite; they do not supply a 5D Einstein stress/action identification.

For the explicit one-loop radius potential `VE=c0/b0⁴[ell/x + W(x)/x⁶]`, `x=b/b0`, the same declared Jordan-frame 5D circle potential is `VJ=x²VE`. If the bulk Lambda is tuned `ell=−W(1)` to give zero 4D Minkowski vacuum energy, the fifth-pressure variation is

`p5(b0)= −(c0/(2pi b0⁵)) [W'(1)−5W(1)] =−c0 D/(2pi b0⁵)`.

**Crucial consequence:** for a FLAT gauge connection with arbitrary constant Wilson phase, `F=0`, and for the flat product Riemann curvature `R=0`. Both classical gauge `A∧F∧F` and mixed gauge–gravitational `A∧tr(R∧R)` vanish. Their classical metric-stress variations at fixed topological connection are zero on this background. Therefore adding a CS bare coefficient, or importing an unrelated 3D CS level, **CANNOT cancel an existing nonzero D and 5D internal pressure on this flat, zero-curvature vacuum**. This is a same-action **conditional no-go**, not a statement CS interactions are generally irrelevant: gauge flux, spacetime curvature, boundaries/anomaly inflow or charged quantum loops change the situation.

The previously source-tested eight-flavour paired QCD + first-Tits two-bifundamental Higgsed gauge sector + dynamical scalar mass spurion at b0=10^-24m has D≈+425 and analytically D>409 for all original neutral mass parameter z under the stated TeV masses. Classical flat-background CS cannot repair it. The old mass-sourced EFT is not an ultraviolet-complete quantum theory and the full E6 action can change the W determinant; don't universalize.

## Mathematical cut C: FULL-27 local parity shift is MASS-SIGN SENSITIVE

**New executable** `scripts/check_kk_e6_full27_5d_cs_mass_chambers.py`: for original Slansky trinification 27

`(3,bar3,1) ⊕ (bar3,1,3) ⊕ (1,3,bar3)`

with Dirac block mass signs `(sigmaA,sigmaB,sigmaC)∈{−1,+1}³`, and a **declared conventional local induced half-level** in fundamental cubic index normalization `A(3)=+1,A(bar3)=−1`:

`k_c=(3/2)(sigmaA−sigmaB)`;
`k_L=(3/2)(sigmaC−sigmaA)`;
`k_R=(3/2)(sigmaB−sigmaC)`.

The script checks all EIGHT sign chambers, integer local values in {−3,0,3}, and `k_c+k_L+k_R=0` in that selected basis. Common sign gives `(0,0,0)`; e.g. (+,−,+) gives `(+3,0,−3)`, **NOT zero**. Thus exact algebraic cancellation of the full 27 cubic *representation index* only automatically cancels the INDUCED PURE local SU3³ parity shift when its block masses use the corresponding common sign (with the declared regulator). The full source-selected E6/Higgs/spurion mass operator can split those signs. That is a new actionable discriminator absent from the earlier purely representation count.

**Not supplied:** mixed SU3²U1, U1³, gauge–gravitational terms, complete spin-CS integral lattice, APS eta phases, twisted bundles, chiral anomaly inflow, global quotient-group representations, or chiral low-energy Standard Model. Even an integer local coefficient in this normalized basis is only a *necessary* input. No global 5D parity/CS closure is claimed.

## Physically correct next Pareto cut / deliverables

1. **Common photon and matter:** identify the physical residual electromagnetic U1 from SU2L×U1Y or supply actual independent B-charged symmetry breaking. Keeping both independent U1_B and EW photon leaves two photons; invertible kinetic mixing is no repair. This is ALREADY verified in #1241, not new to this document.
2. **Actual full-27 action:** produce and diagonalize all SU3³ or E6 fermion/Higgs mass operators, including block sign/spectral flow and scalar quantum determinants, in the same 5D gauge action. Distinguish #1106 local two-bifundamental 36-real model from TWO FULL complex 27s (108 real).
3. **Parity / global CS:** use the existing 3D level/edge receipts as PRIOR MATH, but source an independent true 5D gauge+gravitational CS functional with selected spin/quotient global form, bare level, eta regulator and source-derived mass signs; test changes at thresholds. No automatic L/R 3D CS import.
4. **Full vacuum:** calculate regulator-consistent `W(b,theta_EM,theta_color,Higgs,...)`, run joint gradient/Hessian and global numerical/interval proof, with all physical field modes (massive 5D vectors have 4 polarizations) and correct T55.
5. **Sourced geometry/experiment:** only on a selected compatible 5D Einstein source compute nonlinear rotating Earth and held-out LARES-2/PPN observables. CS and Minkowski prerequisites never prove this by themselves.

**Evidence**: independent local symbolic wedge/large-gauge/flat-geometry/pressure tests PASS; 8 full-27 mass-chamber exact rational Python tests PASS; new GitHub files created on #1241 and source-reviewed. The Agda finite module is SOURCE-WRITTEN/EXACT-HEAD KERNEL UNVERIFIED. No synthetic experimental result, physical CS quantum functional, actual supersymmetry supercharge or completed TOE has been promoted.



## Additional RELEVANT nonflat Minkowski and SAME-METRIC stress donors (audited subsequently)

The Minkowski search is **not exhausted by** the 4D flat `MinkowskiLimitReceipt`. The real source-native nonflat E6 lane in [#1106](https://github.com/chboishabba/dashi_agda/pull/1106) includes:

- `DASHI/Physics/Closure/E6HyperformPoissonLorentzMetricExact.agda`: the original five-coordinate E6 mod-3 quotient's selected 3-axis quadratic-trit source on the existing periodic `C3³` graph, exact 27-point mean-zero Poisson potential, polynomial interpolation and conformal Lorentzian **4D** `g_μν=(1+φ)^2 diag(-1,1,1,1)`. Selected nonflat Einstein tensor checks exist; the source itself says **physical `T_μν` is not derived from this same-object gauge dynamics**. The 5-coordinate *ternary quotient* is not an actual five-dimensional Lorentzian KK metric.
- `E6HyperformIntrinsicRadiationVacuumStressExact.agda`: exact local origin Einstein-shape decomposes into a tracefree positive two-null-radiation-pair remainder plus a vacuum stress proportional to `−(α/3)g`. The source explicitly finds the radiation part FAILS the **single Maxwell Rainich condition**, so no single U1_B electromagnetic source is available by identification. Covariant conservation, calibrated stress and same-state trinification gauge matter remain OPEN.
- `E6HyperformPositiveGaugeVacuumNoGoExact.agda`: the different selected conformal geometry at the exceptional origin has G00=0 but nonzero traceless spatial Einstein tensor; standard compact positive-energy massless gauge stress alone cannot realize it, even with a cosmological term. This is an **additional conditional nonflat source no-go**, not a theorem against actual E6 Yang–Mills with massive, spinor, nonminimal, or quantum matter.

These genuine results create a **parallel physical candidate** to a strict product `Minkowski4×S1`. They cannot be fused automatically: the #1106 conformal metric is a four-dimensional Lorentzian interpolation of a C3³ Poisson graph, whereas #1241's KK vacuum metric is an independent five-dimensional continuous circle source. A concrete isometric/geometric-action mapping (or a new candidate) is needed before the E6 radiation stress could pay the KK internal `T55`. The already-owned prior E6 no-gos further motivate testing the ACTUAL gauge stress, not assigning an Einstein tensor to matter by definition.

**Actual metric-first-variation prior art** in [Casimir/GRQFT #1165](https://github.com/chboishabba/dashi_agda/pull/1165):
- `CasimirU1MetricVariationTransportExact.agda` proves an explicit conditional compiler: if two physically selected actions coincide **along the same entire metric path**, derivative congruence transports equality to first variations and then to a selected common stress readout. Equality at a single background is **not enough**.
- `CasimirU1ModeRenormalizedStressAttachmentExact.agda` records the further same-regulator/same-mode reference attachment obligation to a physical renormalized stress.
- `CasimirSetoidFullStressSameObjectExact.agda` formalises the source-bound Brown–Maclay **plate** stress on a setoid real carrier. Its four-dimensional plate boundary condition is **not** the periodic S1/E6 determinant; no silent stress promotion.

**Productive next bridge, sharper than 'derive CS' or 'derive Minkowski':** from one selected actual 5D full-27 action produce (i) gauge-invariant E6/Higgs/Dirac/CS terms and regulator-normalised quantum effective action **along all source metric/radion paths**, (ii) selected Yang–Mills/Higgs/Dirac first-variation stress on the same matter state, (iii) full \(T55\) and \(T_{\mu\nu}\) with 5D diffeo/gauge Ward identities. Then reuse the #1165 equality-to-variation compiler rather than writing another fake stress map. Compare the 4D GR observables and E6 hyperform stress only after a geometrically justified BIDI consumer correspondence. The present flat F=R=0 classical-CS no-go remains valid ONLY for its original flat product action.


## 2026-10-25 localized Green–Schwarz source is not a bulk CS coefficient

The previous flat F=R=0 classical CS source obstruction remains VALID for its declared smooth-S1 vacuum: classical topological CS does not cancel D>409. The new orbifold branch is a DIFFERENT source. Its 27-weight UV anomaly polynomial factors as (F_L−F_R) times a 4-form, pointing to a localized Green–Schwarz/Wess–Zumino **matter/phase** variation (von Gersdorff/Quirós 2003), not merely a choice of opposite-sign 5D bulk CS levels. Exact source scripts and proof-status report are `scripts/check_kk_e6_orbifold_gs_anomaly_factor.py`, `scripts/check_kk_e6_gs_photon_rank.py`, `scripts/check_kk_e6_27_axion_charge_lattice.py` and `Docs/physics/KKE6OrbifoldGreenSchwarzPhotonSourceMaxCut20261025.md`.

A single existing Chi33 Higgs phase shifts twice along the anomalous UL−UR direction; its halved phase is locally promising but can have a conditional mod-2 global WZ obstruction under unit instanton charge. This cannot be resolved by copying lower-dimensional CS coefficients. The global spin/quotient charge lattice, source action and 5D eta regulator are still actual missing objects. The original same-metric-path action→stress compiler #1165 becomes applicable only after that physically defined action is supplied. No source-specific observation or empirical anomaly is promoted.

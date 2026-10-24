# MMP S² fermion stress / three separately driven plasma regions — 2026-10-24 max-cut

## Status, attribution and no-promotion policy

This is a **scoped source-first calculation**, not a new traversable-wormhole discovery. Original mathematical and physical foundations remain attributed to their authors: Maldacena–Milekhin–Popov (MMP), arXiv:1807.04726, *Classical and Quantum Gravity* **40** (2023) 155016, DOI 10.1088/1361-6382/acde30, constructed the magnetically charged fermionic-Casimir wormhole; standard spin-c sphere Dirac spectral/index theory gives the transverse zero modes and towers; Polyakov/anomaly and Schwinger response are classical 2D QFT results. Sadhukhan's arXiv:2609.33511 (2026-09-27) and arXiv:2610.09847 (2026-10-07) cover complementary first-order fermion anomaly, Hall and Schwinger/polarization responses in the MMP background. Do **not** promote their first-order l≥2 mode results to full nonlinear stability.

Published mathematical existence, authored theorem, finite computational fixture, same-object bridge, kernel-certified theorem, calibrated experiment and a working device are **different evidentiary levels**.

## Reused repo owners, not reinvented

- PR #1165: `CasimirBrownMaclayEnergyConditionExact`, `CasimirGRNullFocusingBridgeExact`, selected QFT stress and Casimir source-native outstanding same-object obligations. Plate stress is NOT automatically spherical Dirac stress.
- PR #1163: `QuantumStressEnergyEngineeringBridgeExact`, `QuantumStressEnergySourceWeldExact`. Strict separation of source-level QFT, QEI, controllability, gravitational magnitude and warp/wormhole capability.
- PR #701: `ZeroPointModeHyperfabricExact` and canonical Casimir mode/renormalisation machinery.
- PR #1215: `CMP119ClassicalCurvatureSpatialC3CovarianceExact` and actual side-four C3 SU2 field covariance. A spatial C3 theorem is not a physical plasma Floquet stress.
- PR #1239: twelve-step three-strand braid; `docs/c3-puncture-pin-monodromy-kk-maxcut-20261023.md` shows its actual strands hit the selected central puncture. Puncture, Pin/Spin, physical magnetic monopole flux and KK horizontal connection require separate identified carrier maps.
- PR #1241: physical KK/radion source and stabilization, including model-specific unbroken-U1 obstruction. Optional donor only; no automatic KK completion.
- PRs #1120/#1045: superconducting source-vs-constitutive gravitational response, historical anomaly/null-replication provenance, and conditional antigravity theorem.

No sibling branch is assumed merged merely because its files have been inspected.

## Calculated physical reduction

Assume an actual magnetically charged background `F_{theta phi}=Q sin(theta)`. For fermion charge e, its **spherical index** is `q=2eQ ∈ Z` (normalisation fixed by `e/(2pi) integral F`). A generic plasma ball without magnetic monopoles has zero net magnetic flux through its enclosing sphere; three rotating dipoles or 2D AB holonomies do NOT imply q≠0.

For a conventional round spin-c S² Dirac operator, the chiral zero-sector has `|q|` modes. Nonzero eigenvalues are `±sqrt(n(n+|q|))/r`, n≥1, with `|q|+2n` states per sign. This calculation uses the established spectrum and a **truncated adiabatic** nonzero-mode NS-circle Casimir energy, not the complete curved 4D determinant.

For the local effective potential from the finite massive tower, `W_KK = - integral sqrt(-h) V_KK(r)`, derive stress from **the same variation**:
- `rho4=V_KK/(4pi r²)`
- `pr4=-V_KK/(4pi r²)`
- `pt4=-V_KK'(r)/(8pi r)`.

This KK local-potential sector alone saturates radial NEC; the massless LLL/Polyakov state supplies candidate negative radial null energy. In spherical proper-radial geometry `ds²=-N²dt²+dx²+r²dOmega²`, with the standard Polyakov state and radial Maxwell field, the Einstein radial constraint

`C=r'²-1+2rr'Phi'+Q²/r²-2(P_Polyakov-V_KK)`

obeys exactly `C'=-Phi' C` when the sourced tt/theta equations are used. The 4D Ward conservation relation also closes by the derived transverse pressure. See committed symbolic acceptance script `scripts/check_mmp_s2_fermion_source_weld_20261024.py`.

## Independently executed local numerical extension — bounded model, not repository CI

A companion local Python study used `e=1`, NS state `t=-pi*|q|/(12L²)`, L=20, finite n≤4 spectral tower and solved the throat constraint with `Q=q/2`.

| q | symmetric throat a | r''(0) | interpretation |
|---:|---:|---:|---|
| 3 | 1.505925 | -0.01855394 | not a flaring throat |
| 12 | 6.096519 | +0.00382519 | local flaring throat; finite x≤45 constraint residual ≈9.4e-12 |
| 24 | 12.394416 | +0.00477549 | local flaring throat; finite x≤45 constraint residual ≈5.5e-12 |

At q=12,24 the radial effective pressure crosses zero at approximately x=33.12,41.67, respectively. This is at most a necessary **radial-extrinsic-curvature** matching indicator for a source-free RN exterior; it is NOT completion of global fermion state transition or smooth physical mouth matching. The quantum mode state and its transverse response do not automatically cease at those points. A 15-case q∈{10,11,12,13,24}, L∈{18,20,22} sweep yields local positive flaring for all listed cases. Thus **no special 12/24 numerological effect** is supported by these model equations.

Further local finite Wilson-Dirac Hamiltonian calculations show explicit local U(1) gauge covariance to ≈1e-15, gauge-invariant spectrum to ≈2e-15, and discrete static persistent-current continuity to ≈7e-10. The link-current and radius-response both derive from the **same finite regulated sea**; neither a renormalized 4D quantum state nor the dynamic Hall/Wen–Zee or Schwinger polarization current is thereby constructed.

## Three plasma balls are not a rotating disk

Use three separately time-dependent electromagnetic/plasma field regions `(E_i(x,t),B_i(x,t))`, potentially with internal field rotation, changing boundaries and mutual coupling. A minimal three-site driven Hermitian Floquet toy verifies combined C3 permutation/time-shift covariance and unitary monodromy, but supplies **no** quantum gravity source. Spatial permutation C3 need not be preserved at each instant if only spatiotemporal symmetry is present.

For three excluded 3D balls, H1(exterior)=0, H2(exterior)=Z³; for a punctured 2D cross-section, H1=Z³ and AB loop phases may be nonzero. With Maxwell div B=0 and no monopoles, each enclosing 3D sphere carries zero magnetic flux. Cross-section winding, C3 modes, Pin lift, and actual q-index on S² are different consumers. The repository 12-step braid actually hits its centre puncture; a physical spin/framing interpretation requires new clearance and bundle-identification proofs.

The user's 12/24 prior art includes the actual 12-step braid and other finite mathematics such as ternary length-12/binary length-24 Golay objects. No theorem identifies these numbers with monopole charge, LLL multiplicity, or a physical number of plasma modes. Do not substitute numerology for physical state construction.

## What still has to be proved / implemented

1. A **single covariantly renormalized curved-space charged-fermion generating functional** `W_ren[g_ab,r,A_ab; spin structure, state, flux]`, not a stitched finite NS potential plus separately asserted Schwinger and Hall terms.
2. Variations of that *same* W with respect to the 2D metric, spherical radius and both gauge sectors, including dilaton/spin-connection, trace anomaly, induced transverse Hall current and time-dependent polarization; gauge, diffeo and Bianchi Ward identities must close with no missing source.
3. Full nonlinear Einstein–Maxwell–fermion boundary-value solve through throat and **two physical magnetic mouths**, with charge quantization and verified C1 matching/no undeclared shells, quantum state transition and asymptotic conserved observables.
4. Mode convergence, QEI, stability and transmission from the **same** physical solution; transient driven-plasma boundary conditions rather than ideal stationary plates or a rotating disk.
5. Only then consider whether C3/Floquet/Pin/puncture and optional KK lift provide a physically derived coupling or a distinct experimental discriminator.

## Acceptance / provenance

Run `python3 scripts/check_mmp_s2_fermion_source_weld_20261024.py` to check the symbolic finite-spectrum / Ward / Einstein-constraint assertions. Code has been committed as *source-written*, not certified by a GitHub workflow. Separate local scripts and numerical JSON receipts are supplied in the chat and are not claimed as repository CI or Agda kernel receipts. No empirical evidence of a plasma-ball gravitational device or MH370 teleportation follows from these mathematical models.


## 2026-10-24 round two: JMD GF(27)/GF(2^12), pointed, BVP and exact mass/Israel matching

**Provenance correction.** JMD's visual input in `JMDFrobeniusThreeTateTraceCrossPollinationExact.agda` is GF(27): 27=3 fixed points+8 Frobenius 3-cycles (3×8=24 nonfixed ELEMENTS, not a 24-dimensional field); also GF(2^12) with 2/1/2/3/9/335 Frobenius cycles of lengths 1/2/3/4/6/12. The associated Monster two-local 4096×24 branching factor is separately sourced; an actual representation intertwiner is NOT established. The order-12 Hadamard mod 3 → ternary Golay [12,6,6] has 24 FULL-WEIGHT codewords out of 729; original coding/math belongs to Elkies, MacWilliams et al., not JMD. Witten/SUSY index owner `DASHI/Physics/QFT/WittenIndexSUSYBoundarySurface.agda` is a target surface only: no SUSY physical sector, index, or 12/24 flux selection is proved.

**Pointed, not Pin.** `Base369PointedAppraisalFibreExact.agda` and pointed 729 corner owners are marked-position/address mathematics. An actually physical geometric bridge uses north/south *pointed gauge patches* on S² with A_N=(q/2)(1-cos θ)dφ, A_S=-(q/2)(1+cos θ)dφ, overlap e^{iqφ}, and first Chern number (1/2π)∫F=q (charge normalization set to 1). Standard spin-c Dirac index produces q lowest-Landau-level zero modes; this is original differential geometry/index theory, not a new discovery or an automatic realization by the finite pointed cube. C3 rotation changes patch transition phase by e^{2πiq/3}, selecting q modulo 3: q=3,12,24 all have trivial phase, so no 12/24 privilege. Pin refers separately to O(p,q) reflection lifts, not pointed choice. The 12-step repo braid literally hits the designated centre puncture until a new detour is justified.

**Flux topology:** In ordinary R³ with three smooth plasma balls, no enclosed smooth magnetic monopole source means ∫S² B·dS=0 for each enclosing sphere. A punctured 2D cross-section has nontrivial H1/AB loops but that does not give S² Chern flux. However an EXISTING two-ended wormhole has a nonbounding throat S², so source-free Maxwell may thread it with quantized nonzero flux, the Misner–Wheeler 'charge without charge' mechanism. It does not show how three plasma balls create such topology.

**Exact pressure-zero backpropagation result.** For ds²=-N(x)²dt²+dx²+r(x)²dΩ² and magnetic geometric charge Q, let v=r', F=Φ' and E=4πr²ρ_QFT, P=4πr²p_{r,QFT}, with the Maxwell contribution separate. Define the radial constraint
`C=v²-1+2rvF+Q²/r²-2P`.
At any junction with r>0, v>0, set the exterior Reissner–Nordström mass
`M=r/2(1+Q²/r²-v²)`.
Then the induced metric's spatial coefficient is matched exactly, `f_RN(r)=v²`, and the time-extrinsic-curvature mismatch on C=0 is
`K^t_t(in)-K^t_t(out)=F-(M/r²-Q²/r³)/v=P/(rv)`.
Thus P=0 closes the **Israel surface-shell** matching at that radius, with constant time-scale N/sqrt(f), without assuming a thin matter shell. From the tt Einstein equation the exterior mass parameter satisfies `M'=v E`, so it can be integrated from the throat. Symbolic receipts: `scripts/check_mmp_israel_rn_junction_20261024.py`; do not mistake a C1 metric for a smooth fermionic quantum state.

**Local finite-domain numeric two-end effective solutions** (companion Python in conversation, NOT committed to GitHub by this branch): q=10/11/12/13/24, L=20, four massive spherical levels, prescribed Polyakov static state. These all reach an outward P=0 surface, have regular N>0 interior and regular magnetic RN external metric, and all satisfy the two Israel K-continuity conditions with mismatch <5e-13 and constraint <6e-12 (illustrative solver tolerances). At q=12, junction x≈33.121658, r≈11.683162, M≈5.997338, throat r≈6.096519 and the two-sided interior null travel coordinate t≈20.810488. Radial affine ANEC for the glued effective stress is ≈-0.00051116 (normalization E_Killing=1, N_throat=1). These are **dimensionless regulated model results**; not global MMP physical solutions, no proof of state extension.

**New finite *same-source* static Dirac response:** a position-dependent-lapse and spherical-radius one-dimensional Wilson–Dirac lattice Hamiltonian with explicit gauge link phases supplies finite vacuum-energy derivatives w.r.t. N(x), r(x), and link A_x from one regulated spectral functional. Local Python tests: U1 gauge covariance error ≈4.4e-16, link-current conservation ≈4.5e-9, mixed radius-current Hessian reciprocity error ≈4.5e-6. The absolute PV-subtracted vacuum energy changes radically when the heavy reference mass goes from 5 to 10; it is therefore **not a covariantly renormalized 4D determinant** and cannot replace the anomaly+state source in the Einstein solver without further work. No induced Hall curvature term or real-time Schwinger polarization was paid. Full source-level global QFT fixed point remains OPEN.

**Critical physical normalization guard:** Original MMP Eq. (5.31) gives an asymptotic throat length ell=16 r_e³/(G q), r_e=sqrt(pi) q l_p/g4, which scales q² at fixed physical coupling. Our Q=q/(2e) and circle L=20 are deliberately independent dimensionless model choices. The scan CANNOT be equated to MMP scales without fixing Einstein–Maxwell normalization, q≫1 regime, physical spin structure and state-dependent circumference. A constant 20 in toy units must not be sold as the paper's ell.

**State transition gate:** Switching off the constant 2D Casimir parameter t at the match is not dictated by the Dirac equation. Letting t=t(x) while holding the other Polyakov formulas fixed adds `2 t'(x)/N²` to the radial quantum Ward balance; an additional induced stress/current or a genuinely globally defined nonlocal effective action is needed to restore conservation. An effective piecewise fluid can be distributionally conserved with zero normal pressure and no thin shell while failing this physical quantum-state test.

**Current highest-leverage kernel/physics leaf:** A common Hadamard/heat-kernel-subtracted, gauge/diffeomorphism-covariant curved-space spin-c Dirac functional W_ren[g,A;state] across BOTH mouths. Derive T_ab, angular/dilaton response, Aμ current, Hall/Euler/Schwinger contributions and trace anomaly from its SINGLE variation, then solve its nonlocal Einstein–Maxwell–Dirac BVP. Jochen Zahn, *The renormalized locally covariant Dirac field*, Reviews in Mathematical Physics 26 (2014), DOI 10.1142/S0129055X13300124, is appropriate primary field-renormalization authority. The Sadhukhan 2026 perturbation papers are first-order response donors, not nonlinear global source receipts.

**Acceptance:** `python3 scripts/check_mmp_israel_rn_junction_20261024.py`; `python3 scripts/check_pointed_monopole_c3_roles_20261024.py`; previous source checker. Nothing here asserts kernel certification or experimental realization.


## Exact prior-art bridge actually present in recent sibling PRs (2026-10-24 review)

- **PR #1235**: `DASHI/Mathematics/Topology/HopfU1TransitionCocycleExact.agda` has an actual algebraic U1 transition cocycle, and `HopfU1PrincipalBundleObligationsExact.agda` states smooth local-triviality, curvature, Chern integrality and principal action requirements. The latter does not universally inhabit them: a U1 subgroup is not a fully sourced Dirac monopole field.
- **PR #1239**: `DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda` proves local additive gauge invariance of dy+κA. This is a mathematical connection donor, not the required sourced physical Maxwell/Dirac action.
- **PR #1215**: actual finite SU2 curvature/stress spatial C3 covariance; this must be distinguished from a moving three-region plasma *spatiotemporal* C3-symmetric source.
- **The new classical two-mouth junction identity** is stronger than generic stress-matching, but does not import these sibling donors into one compiled proof or pay the global fermion-state continuity.

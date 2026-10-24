# Actual E6/trinification 5D gauge/Higgs source versus KK/QED/QCD
Date 2026-10-24. **Owner**: [KK PR #1241](https://github.com/chboishabba/dashi_agda/pull/1241). **SAME-OBJECT DONOR (UNMERGED)**: [Albert/F4/E6 PR #1106](https://github.com/chboishabba/dashi_agda/pull/1106), head 10262c0a888521e3e045d6bcede54c72182acc74 at audit time. **Additional donors**: [SO3 torque PR #1164](https://github.com/chboishabba/dashi_agda/pull/1164), [Hopf principal U1 PR #1235](https://github.com/chboishabba/dashi_agda/pull/1235), [Casimir source-native #1165](https://github.com/chboishabba/dashi_agda/pull/1165), [TOE #1217](https://github.com/chboishabba/dashi_agda/pull/1217) and [Lean TOE #80](https://github.com/chboishabba/dashi_lean4/pull/80).

## Attribution and exact previous owners

**Classical original science**:
- Classical trinification E6⊃SU3c×SU3L×SU3R, decompositions of 27 and 78: R. Slansky, *Group theory for unified model building*, *Physics Reports* 79 (1981), 1–128, DOI 10.1016/0370-1573(81)90092-2. The DASHI 27 first-Tits action is a **specific repo construction**, not original discovery of E6.
- Five-dimensional gauge/Higgs degrees and original local quantum potentials: Marti–Pomarol, *Supersymmetric theories with compact extra dimensions in N=1 superfields*, *Phys Rev D* 64 (2001) 105025, DOI 10.1103/PhysRevD.64.105025; Abe, Inami, Kawamura, Koyama, *Radion stabilization in the presence of Wilson line phase*, *PTEP* (2014) 073B04, DOI 10.1093/ptep/ptu097.
- 5D parity/Chern–Simons and their dependence on actual regulator, matter and global gauge structure: *Comments on Global Symmetries and Anomalies of 5d SCFTs*, *Communications in Mathematical Physics* (2024), DOI 10.1007/s00220-024-05139-8; Christopher T. Hill, *Anomalies, Chern–Simons terms and chiral delocalization in extra dimensions*, *Phys Rev D* 73 (2006), 085001, DOI 10.1103/PhysRevD.73.085001. Neither publication supplies a complete source-specific 5D SU3³×U1_B action in our repo.
- Our earlier SO3/C3 spatial torque/Hodge identity in #1164 is mathematically useful for finite stress/rotating geometry, but SO3 has no nontrivial Lie algebra homomorphism onto the abelian KK fibre U1. A fifth-coordinate Lorentzian metric and field-dependent torques need their own connection and metric variation. #1235 Hopf bundle topology does not prove radion dynamics or the electromagnetic photon.

**#1106 ACTUAL paid source data**:
1. Literal first-Tits M3^3/27 carrier, norm-preserving SL3^3 action and exact E6 root-weight recovery, separately limited by proof-relevant global Albert recognition.
2. Two scalar 3×3 bifundamentals Phi and Chi with E32 and E33 vacuum, same six-invariant locally nonnegative potential selecting the gauge orbit. THESE are **36 real field coordinates**, not two full 27-dimensional complex scalar multiplets.
3. 16 L/R gauge generators; at the selected vacuum 4 unbroken SU2L×U1Y directions and 12 broken modes. Their conditional local Gram eigenvalues at equal-unit parameters: 0^4, (1/4)^4, (1/2)^7, (5/6)^1. General eigenvalues depend on (gL,gR,v32,v33), including a nontrivial neutral quadratic.
4. Real scalar Hessian in the 36-dimensional local model: 0^12, 4^6, 6^8, 8^10. The 12 zero modes are the actual gauge-orbit tangent, leaving **24 positive transverse real Higgs modes**, not 36 physical Higgs bosons in addition to the massive vector longitudinal modes. Coefficients and physical VEV scale are not derived from experiment.
5. A complete pair of complex 27 Higgs multiplets would have **108 real coordinates**, of which 96 would remain after the SAME 12 Goldstones, assuming all additional modes are stable and the rest of E6 is consistently gauged/broken. #1106 does NOT contain the required full-108-dimensional positive Hessian, E6-invariant potential, or experimental spectrum.

## Genuine interacting 5D local EFT candidate, but not a physical completion

One local five-dimensional action under the **declared** gauge group G5 = SU3c×SU3L×SU3R×U1_B may be explicitly specified. In a locally trivial KK chart (metric/density included in covariant contractions), choose

S5 = ∫ d⁵x sqrt(-G) { (M5³/2) R5 - Λ5 - 1/4 Σ_G F^a_MN F^{a MN} - 1/4 B_MN B^{MN}
+ Tr|D_M Phi|² + Tr|D_M Chi|² - V6(Phi,Chi)
+ 1/2 (∂X)² - λ_X,5 (X²-w5²)²
+ Σ_i [barPsi_i(i Gamma^M D_M - M_i - y_i,5 X) Psi_i]
+ Σ_j [|D_M S_j|² - (μ_j²+κ_j,5 X²)|S_j|²] + other gauge-invariant local interactions }.

Here Phi,Chi each transform (1,3L,bar3R), and V6 is the #1106 six-invariant nonnegative comparison potential with selected positive coefficients and **physical dimensionful kinetic normalization**. X is a propagating, gauge-singlet real scalar; each 5D Psi_j and scalar S_j is charged as in the selected SU3c×U1_B vectorlike QCD sector. A soft-split source is thereby an **interacting field theory**, not a list of arbitrary particle masses: take the stable classical X=w5, Phi=v E32, Chi=v E33 and S_j=0 backgrounds. Set M_i+y_i,5 w5=m_i, μ_j²+κ_j,5 w5²=(3 TeV)², and source adjoint masses from analogous local covariant terms. All μ_j² may be positive so no scalar tachyon is needed to write the *tree-level* action.

VERY IMPORTANT 5D field dimensions: [X_5]=3/2, [Psi_5]=2, [g5]=−1/2, [y5]=−1/2, [κ5]=−1. For reference circumference L0=2πb0, canonical 4D X4=sqrt(L0) X5 and w4=1TeV give w5=w4/sqrt(L0), y5=y4 sqrt(L0), κ5=κ4 L0, λ_X,5=λ_X,4 L0. Taking y4=κ4=1, λ_X,4=0.4 gives mX= sqrt(8 λ_X,4)w4≈1.788854TeV. The dynamical X fluctuation is **ANOTHER PHYSICAL BOSONIC ONE-LOOP DETERMINANT** absent from the previous split-spectrum script.

**Actual limitation:** these terms define an interacting classical 5D gauge-covariant effective action whose parameters can produce the selected masses at a tree-level homogeneous extremum. They do NOT exhibit a UV-renormalized supercharge, a fully specified E6 gauge/Higgs representation (rather than this SU3³ truncation), a regulated quantum stress tensor, anomaly-free quotient-group quantum functional integral, a quantum-corrected vacuum or a phenomenologically realistic Standard Model. The scalar/electroweak sector and the old independent Maxwell U1_B need further same-action identification.

## Decisive full-mode Casimir source obstruction

The old E6-inspired **gauge-only** test included 16 extra massless L/R vectors = 16×3 = **48** 5D free boson degrees. An actual two-VEV Higgsed L/R source instead has:

| 5D physical mode | Count |
|---|---:|
| 4 remaining massless L/R vectors | 4×3=12 |
| 12 broken massive L/R vectors | 12×4=48 |
| 24 transverse physical Higgs scalars | 24×1=24 |
| **total actual L/R + two bifundamental sector** | **84** |

Equivalently, unbroken count **16×3+36=84**. This is a proper spectral / longitudinal-Goldstone compensation and avoids double counting. Since all selected masses are TeV scale versus 1/b0≈1.973×10⁸GeV, their *periodic S1* free determinants are very nearly massless and add **36** Casimir polarization units vs gauge-only. Thus in the **original** E6 gauge-only 6-quark reference, D=W'(1)−5W(1) gains approximately **+180**. With selected g=.65, v=10TeV and physical Hessian mass-scale parameter λ=.1, a stronger analytic bound gives **D>164** for all original neutral fermion stabilizer masses z>0. A cosmological counterterm cannot fix both vacuum energy and radius.

More importantly, adding this same L/R Higgs/gauge sector to the **later eight-flavour soft-paired SU3c×U1_B source** produces L/R contribution approximately **+420** to D, while dynamical mass-producing X contributes approximately **+5**. The older tuned paired QCD source had D=0. The true combined candidate at the former neutral root is **D≈+424.9999986** and a conservative general bound is **D>409** for any neutral-stabilizer mass z>0. This uses the original TeV soft masses and the physical 36-dimensional Higgs *truncation*, not the full E6 108-real Higgs sector.

Reason: define h(s)=f(s)−s f'(s)/5, where f is the periodic Casimir kernel and 0<h(s)≤1 decreases for s≥0. The paired QCD contribution obeys D_paired≥−15−360(1−h(zS)) for zS=2π(3TeV)b0; its adjoint and heavier-exotic terms are nonnegative. L/R adds D_LR=60+20Σ_12 h(zV)+5Σ_24 h(zH); spurion adds 5h(zXspur). All selected LR masses <30TeV and h(2π(30TeV)b0)>0.999999894. Consequently

D_joint ≥ −15 − 360(1−h(zS)) +60+360 h(2π(30TeV)b0)+5h(zXspur) > 409.

No value of the old tunable neutral-fermion mass z can satisfy D_joint=0 within this selected one-loop source. This is a **source-specific no-go for the literal candidate action and selected radius/spectra**; it does not exclude different E6 field content, unbroken SUSY, massive KK holonomy effects, different radius or strongly coupled compactification mechanisms. The 5D internal pressure is p5=−[c0/(2πb0⁵)]D_joint after 4D Minkowski counterterm tuning; nonzero p5 violates a flat 4D×S1 product Einstein source.

Executable numerical / analytic bounds:
- \`scripts/check_kk_trinification_higgs_5d_mode_budget.py\`
- \`scripts/check_kk_joint_e6_qcd_spurion_radion_pressure.py\`
- \`scripts/check_kk_5d_spurion_parity_cs_source.py\`

## Single-photon / parity / torque consumers

The independent U1_B Maxwell vector in #1241 is a 5D gauge group **independent** of SU3L×SU3R. The #1106 Higgs vacuum retains SU2L×U1Y. A later standard electroweak neutral Higgs condensate breaks SU2L×U1Y to one electromagnetism U1_EM. If the independent U1_B remains massless, there are GENERICALLY **TWO** U1 vector zero modes. The simplest electroweak doublet is B-neutral and its neutral mass Gram has two zero directions (old B plus EW photon). The repair is an actual gauge identification/mixing or additional B-charged breaking, *which changes the Wilson determinant and photon consumer*. Do not call the original U1_B "the photon" and the E6 U1Y photon identical by declaration. The mounted independent symbolic check \`/mnt/data/kk_trinification/check_kk_e6_two_vev_source.py\` verifies the rank-1 Gram and two zero vectors.

The eight SU3c fundamental Dirac fields have integral U1_B charges in **minimum q_EM=1/3 units** [2,−1,−1,2,−1,2,2,−1], hence each satisfies (triality + charge) mod 3=0 for one selected diagonal quotient generator of (SU3c×U1)/Z3. For positive mass-sign convention, the elementary half cubic/parity moments give SU3^3: 4; SU3²U1: 2; U1³: 42 including colour degeneracy and cancelling ±3 singlet Dirac species; U1-gravitational: 6. These are integers **only in a conditional local basis/regulator convention**, not a proof of global spin-Chern–Simons quantisation or invariance under all large quotient-gauge transformations. Even eight Dirac flavours do not make a 5D reflection/parity symmetry true when all masses have the same sign; orientation reflection flips the relevant parity-odd mass/regularisation contribution. For a 5D full 27=(3,bar3,1)+(bar3,1,3)+(1,3,bar3) Dirac under SU3³, each SU3 factor sees 3 fundamentals and 3 antifundamentals; its *pure local cubic index* cancels at common mass sign. A single (3,bar3) Dirac would instead produce half-integer ±3/2 pure SU3L/R shifts. None of this settles mixed/global CS or a chiral 4D Standard Model. Original source: DOI 10.1007/s00220-024-05139-8 and Hill 2006.

Finally, spatial SO3 torque \`tau=r×F\` belongs to a nonabelian SO3 Lie action; compact KK fifth translation belongs to abelian U1. Since [so3,so3]=so3 and the U1 Lie bracket vanishes, any Lie-algebra homomorphism so3→u1 is ZERO. Hence the existing #1164 Hodge/torque constructions are valid **spatial orientation donors**, NOT a derived KK fibre gauge interaction or a radion stabilizer. The #1235 Hopf U1 geometry remains a different bundle topology/source contract; no unlicensed equality of fibre U1, physical U1_B and spatial torque group is introduced.

## Better Pareto donor: full E6 27 hyper and source-selected soft splitting

A direct field-count consequence of the **full** 27 carrier is more promising than adding arbitrary compensator scalar fields:
- Two full complex 27 Higgs multiplets contain 108 real scalar coordinates. With 12 Goldstones consumed, the same 16 LR gauge bosons + scalar source has 4×3 +12×4 +96 = **156** physical bosonic degrees.
- A candidate 5D vector multiplet supplies 16 additional adjoint real scalars and 16 symplectic Majorana gauginos (16×4=64 fermionic), while one 5D hypermultiplet in the 27 contains two complex 27 scalars and one Dirac 27 (27×4=108 fermionic). Total **172 bosonic = 172 fermionic** physical free-field units.
- A FULL 27 Dirac under the usual three-trinification-bifundamental decomposition has SU3³ *pure local cubic index zero* under a uniform fermion mass sign, unlike just one bifundamental Dirac. (The full 5D global parity, mixed anomalies and quotient action still need examination.)
- With actual supercharges and mass/gauge/Wilson **operator-by-operator** pairing, these sectors could have cancellations of the entire one-loop winding determinant at any radius, not just a coincidental 48 count. None of the operator pairs or positive full-108 Higgs Hessian has yet been constructed; actual SUSY breaking to produce 3/4/9 TeV splits reopens the determinant. The old #1106 36-real scalar comparison is NOT a full E6 hypermultiplet potential and cannot be promoted to one.

This is the appropriate conditional research direction: bring full 27 representations, specified gauge/spurion couplings, actual symmetry breaking, spin-CS/anomaly, and full radius/electromagnetic/colour/EW holonomies into **one selected source action** before running a global vacuum solver. E6 representation arithmetic alone is not an observed or viable model.

## Evidence and commands

- Analytic source/spectrum algebra, exact 84/156/172 DOF counts, and z-independent positivity bounds: new repo math, source-authored.
- Independent local mpmath/SymPy reproduction of earlier Higgs/extra-photon/torque/charge checks PASSED; the new scripts are COMMITTED and their GitHub blobs fetched, but exact-head byte execution and Agda kernel compilation are not attested.
- \`DASHI/Physics/Gravity/KKTrinificationFullSpectrumBIDIExact.agda\` is finite exact arithmetic + canonical source-observer non-descent; **SOURCE-WRITTEN/KERNEL UNVERIFIED**, does not import unmerged #1106 theorems.
- Concrete code for full 27 dimensional/anomaly count: \`scripts/check_kk_e6_full27_hyper_cs_supertrace.py\`. It does not produce supercharges, full action interactions or anomaly cancellation.
- Commands:
\`python3 scripts/check_kk_trinification_higgs_5d_mode_budget.py\`
\`python3 scripts/check_kk_joint_e6_qcd_spurion_radion_pressure.py\`
\`python3 scripts/check_kk_5d_spurion_parity_cs_source.py\`
\`python3 scripts/check_kk_e6_full27_hyper_cs_supertrace.py\`
\`agda -i . DASHI/Physics/Gravity/KKTrinificationFullSpectrumBIDIExact.agda\`.

**Max-cut verdict:** the existing E6 two-VEV donor IS relevant and makes the earlier missing-Higgs+extra-photon inconsistency exact. A gauge-invariant tree-level 5D interacting spurion EFT can be written, but the old one-loop stable vacuum FAILS for its actual additional field content; parity/global CS and a fully realised chiral SM remain OPEN. The more promising full-27 vector/hyper route remains conditional on genuine same-operator interactions, eigenmasses, UV and empirical gates, NOT just 172=172.



## 2026-10-24 final CS/Minkowski PRIOR ART RECONCILIATION

**Supersedes the inaccurate shorthand "CS and Minkowski missing":** the source-first audit \`Docs/physics/KKMinkowskiCSFiveDSameSourceMaxCut20261024.md\` maps actual existing owners \`MinkowskiLimitReceipt\`, \`GRConcreteLeviCivita\`, \`CSLevelFlowFullReceipt\`, \`FermionicLoopCSShiftReceipt\`, \`BulkBoundarySU3Receipt\`, and \`KacMoodyLevelReceipt\`. Flat 4D Lorentzian geometry and conditional 3D CS/affine/level-flow proofs DO exist. The precise unpaid five-dimensional consumer is the physical **top-degree CS five-form + spin/quotient action + regulator-defined massive-fermion eta contribution**, on the SAME selected 5D \(E6/SU3³\) matter and metric field path. Distinguishing source ownership is not dismissing that prior art.

**New positive five-form computation** \`scripts/check_kk_minkowski_cs5_same_source.py\`: on \(T5=S1×T2×T2\), a selected mixed U1 CS action \(S5=k/(2π)^2 ∫ A_1∧F_2∧F_3=k θ p q\) undergoes one large gauge winding \(ΔS=2π k p q\), giving an invariant phase for integer fluxes and k in the declared normalization. This is a TRUE selected **five-dimensional** quantization example, NOT the entire nonabelian E6/global spin CS action. Agda owner \`KKMinkowskiChernSimonsFiveDConsumerExact.agda\` formally blocks an unlicensed 3-form/5-form and 4D/5D claim transport.

**New negative five-dimensional stress result:** on flat \(M^{3,1}×S1\) with constant radius, F=0 (even at nonzero flat Wilson A5) and R=0, so classical gauge \(A∧F∧F\) and mixed gravitational \(A∧tr(R²)\) vanish and have zero classical metric stress. The flat KK sourced Einstein requirement remains \(D=W'(1)-5W(1)=0\) after 4D vacuum-energy retuning, with \(p5=-c0D/(2πb0⁵)\). Hence a new CS bare coefficient CANNOT pay the old source's \(D>409\) on the FLAT zero-curvature candidate. It may matter off-flat/flux/boundary or through actual quantum spectrum corrections. No no-go for generic nonflat E6 CS fields is claimed.

**New full-27 local parity CHAMBER audit** \`scripts/check_kk_e6_full27_5d_cs_mass_chambers.py\` and \`KKE6Full27CSMassSignConsumerExact.agda\`: under the declared 5D Dirac local cubic-index convention and \((3,\bar3,1)⊕(\bar3,1,3)⊕(1,3,\bar3)\), with independent mass signs \(s_A,s_B,s_C\), the induced pure SU3 shifts are \((3/2)(s_A-s_B,s_C-s_A,s_B-s_C)\). All 8 sign chambers are checked. A COMMON full27 sign gives (0,0,0), but (+,-,+) gives (+3,0,-3). Thus the FULL27 representation cubic-index cancellation remains genuine **representation theory**, but it cannot pay parity-CS on a Higgs/spurion source with sign-split masses unless their physical mass operators are audited. Integer local shifts do not settle global quotient CS/APS η/regulator/mixed anomalies.

**Other prior nonflat source owners** in original E6 #1106: \`E6HyperformPoissonLorentzMetricExact\` (nonflat 4D Lorentzian CONFORMAL metric from periodic C3³ Poisson/interpolation, not literal 5D S1), \`E6HyperformIntrinsicRadiationVacuumStressExact\` (positive local radiation/vacuum shape but **fails single Maxwell Rainich**, no gauge-source equality), \`E6HyperformPositiveGaugeVacuumNoGoExact\` (no positive massless-gauge-only source for its selected nonflat Einstein tensor). The **reusable same-metric stress compiler** is source-owned by QFT/Casimir PR #1165 \`CasimirU1MetricVariationTransportExact\`: equality of actual physical action values ALONG ENTIRE selected metric path transports to first-variation equality; value equality at one point does not. The periodic circle determinant must supply its own regulator, mode and physical stress inputs, not inherit Brown–Maclay parallel plates.

**Next owner / max-cut**: select physical U1 photon *once*, build the full27 Higgs/Dirac mass operator, determine parity-odd sign-chamber flow and integral CS counterterms in the chosen global spin gauge group, compile the renormalized periodic \`W(b,holonomies,Higgs)\` including source-dependent masses and its metric path, and prove both \(T55\) and \(\nabla_MT^{MN}=0\) for the chosen 5D action. Then test joint global stability and physical rotating Earth. Full E6, chiral SM, regulator/global CS, quantum-corrected Minkowski/source Einstein, and empirical LARES remain OPEN.

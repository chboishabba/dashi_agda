# KSW668 F8 geometry and dual-Weyl roadmap — max-cut XXVIII (2026-11-17)

**Status:** Agda source-written, pinned Agda 2.9 kernel NOT run; no curvature-convergence or physical signal acceptance.

## Provenance / reuse before construction

- Original original-model owners: `scripts/ksw668_f8_tt_multipole.py`, `ksw668_f8_fv_source_flux.py` and their KSW668/AdS5 physics owners. Preserve author attribution and original references (Caldwell–Langlois, Thorne, SBP/SAT, numerical wave-method papers). New algebraic cut is separate from original inventions.
- `DASHI/Physics/GR/RiemannTensor.agda` provides Riemann/Ricci/Bianchi **interfaces**, but its canonical model explicitly has a zero-table non-flat blocker.
- `DASHI/Geometry/LeviCivitaBridge.agda` provides the DCHoTT G-structure socket, not proved non-flat Levi-Civita uniqueness.
- `DASHI/Physics/Closure/ContinuumCurvatureSourceSpinTwo.agda` provides the **actual convergence, gauge and curvature-authority record** to instantiate.
- Reuse `KSW668AdS5TTFiniteVolumeFirstCellRationalExact.agda` and `KSW668AdS5MovingNeumannFluxRationalExact.agda`; do not duplicate the effective radial d=3,7,11 or wall-flux lemmas.
- `CMP119CosmologyFiniteWeylConventionFirewallExact.agda` concerns metric/partition Weyl rescaling, NOT the electric Weyl tensor.
- `EverythingTOESymmetryResolved369.agda` uses many ternary/369 carriers; F8 indexing q=0,1,2 for ell=0,2,4 is legitimate, but no Monster/369 geometric equivalence is known.

## New finite readout theorem, not a geometrical promotion

`DASHI/Physics/Gravity/KSW668F8DualElectricWeylReadoutAlgebraExact.agda` reproduces the original algebraic F8 receiver readouts with external rational input `scale=1/t²`, `etaeta=H_etaeta`, `eta=H_eta`, `rr=H_rr`, `lap=Delta3 H`.
Its `dualReadoutCancellation` and `dualReadoutReconstruction` prove the exact finite identity

```
E4 = -(H_etaeta + H_rr)/(4 t²)
E5 = -(H_etaeta + 2 H_eta - Delta3 H)/(2 t²)
E5 - 2 E4 = (Delta3 H + H_rr - 2 H_eta)/(2 t²)
```

These are ring identities. They do not establish 5D covariant Weyl curvature, gauge, Israel coupling, source-to-Weyl continuity or convergence. Independent SymPy algebra check PASS. Pinned Agda kernel OPEN.

## Measured fixed-dr normal/time factorial (max-cut XXVII)

Original TT source, dr=.008 fixed, normal_order=3, t=12:

| Run | dy | actual dt (approx) | E4 | E5 |
|---|---:|---:|---:|---:|
| R0 | .012 | .00179891 | -2.805311616714e-5 | -2.326215693090e-6 |
| RT | .012 | .00089975 | -2.757731022864e-5 | -2.272291814876e-6 |
| RY | .006 | .00089975 | -2.583942604706e-5 | -2.113092373841e-6 |
| RY4 | .003 | .00044995 | -2.537138442114e-5 | -2.061390601964e-6 |

The 32/32 preexisting regression tests passed. R0 to RY4: E4 magnitude -9.56%, E5 -11.38%. Time-only is ~2%, first normal-only relative RT ~6–7%. This does not isolate SAT from the normal bulk stencil and does not prove its convergence order. The separate dr=.004 same-original forward/adjoint outputs E4=-4.85860e-4 and E5=-8.42226e-5 remain strongly grid-sensitive.

## Pareto ordered gates

1. **G0 finite dual-Weyl readout cancellation:** code added and symbolic proof PASS; Agda kernel verification pending.
2. **G1 same-object AdS5 geometry adapter:** original Poincare metric, moving brane normal and induced metric, linearized Riemann/Ricci/Weyl electric projection, 3D TT tensor/gauge and sign conventions; instantiate existing spin-two curvature records with actual witnesses rather than Riemann zero tables.
3. **G2 joint (P,M,U) Israel wall:** same physical source, stage-resolved SAT target, boundary energy and physical trace; a nonzero pointwise SAT mismatch is not itself a continuum boundary error.
4. **G3 fully discrete moving SSPRK3 energy:** z^-3 norm, radial SBP FV, normal SBP2 SAT, time dependence and outer closures, explicit uniform CFL.
5. **G4 higher-Sobolev both-Weyl boundary trace:** H^(4+eps) regularity and bounded source-to-two-Weyl mapping; H1 energy is provably insufficient.
6. **G5 independent dr/dy/dt curvature convergence:** original TT field, intrinsic and projected Weyl, outside-cone negative control. Use 76-interval common seed-mass source carrier; piecewise-constant transfer does not commute with TT differentiation.
7. **G6 original FIO, matter action and detector:** remain OPEN; no physical graviton evidence or superluminal inference.

**Firewall:** source-written ≠ kernel accepted ≠ analytical physical theorem ≠ detected signal. No modification to ESD code or other external attribution owners.


## XXIX same-object maximum-cut — 2026-11-17

This round **did not close G1--G6 as physical/continuum theorems**. It added and independently tested concrete original-geometry algebra, isolated exact SAT source coefficients and a stability negative control, and made required cross-programme witnesses explicit. Neither the Agda kernel nor a full new moving PDE evolution was run here.

**G1 concrete advance:** For original Poincare AdS5 g=z^-2 diag(-1,1,1,1,1), original z=1/t and T'(t)=sqrt(1+t²)/t², the induced metric is exactly -dt²+t² dX². At t=4/3: z=3/4, z'=-9/16, T'=15/16, induced proper-time metric=-1. A direct, independent SymPy calculation constructed all 13 nonzero Christoffel entries and checked all 625 Riemann components against constant sectional curvature -1; Ricci=-4g, scalar=-20, unperturbed Weyl=0 (all 625 components). The *linearised* Weyl of original sourced H and its moving-normal electric projection are **not** obtained by the background Weyl=0 result. Agda source owner `KSW668F8OriginalAdS5EmbeddingSliceExact.agda` proves just the rational proper-time/scale factors and a scalar trace algebra at original t=4/3; kernel OPEN.

**G2 concrete advance:** Original `normal_order=3` SAT at t=4/3, v=-3/5 and dy=3/250:
`target = -5 amp S/4 + P/4` and `SAT_M= -1000 amp S/3 + 200 P/3 - 800 M/3`. This expands the ACTUAL original boundary correction, including the TT source coefficient. `KSW668F8WeakIsraelSATSliceExact.agda` has finite rational proofs, while the non-SAT normal derivative and coupled radial/warp terms still need the joint energy theorem.

**G3 concrete advance:** For `R(z)=1+z+z²/2+z³/6`, the scalar dissipative mode at `z=-3` has `R(-3)=-2`, `|R(-3)|²=4`. Thus even scalar damping is not unconditionally SSPRK3 stable. `KSW668F8SSPRK3FullStabilityPrerequisiteExact.agda` is a finite rational counterexample. It supplies no coupled admissible CFL.

**G4 OPEN:** Existing `scripts/test_ksw668_f8_original_energy_weyl_trace_no_go.py` and source-derived H1→pointwise second-derivative no-go exclude promotion from a first-order energy bound; high-order Sobolev estimate with uniform constants for the actual moving domain / SAT / observer is missing. General Sobolev embedding alone does not give a PDE solution bound.

**G5 OPEN:** Replayed XXVII `factorial_summary.json` data, 6/6 local checks: fixed original source norms across R0/RT/RY/RY4, independent normal/time variation, exact numerical curvature recomposition; R0→RY4 changes E4=9.56%, E5=11.38% in magnitude, but not independently radial/normal/time convergent. Original dr=.004 outputs still differ strongly from dr=.008 even though an independent forward–adjoint parity check passed.

**G6 OPEN:** No same-source physical matter action, signal source/receiver coupling, original retarded FIO nonzero witness, actual calibrated detector or observed graviton was newly derived. Do not promote scalar-probe bulk-shortcut examples into a sourced tensor gravitational wave. Keep original Caldwell--Langlois and related citations and DASHI original author attribution.

**Reused authority seam:** `KSW668F8SameObjectWeylAuthorityBoundary.agda` imports the existing `ContinuumCurvatureSourceSpinTwo.DiscreteCurvatureApproximation` type and concrete original KSW algebra owners; its G1--G6 proof fields are **not instantiated**. This is typed accounting, not a completed physical theorem.

**Acceptance:** independent local SymPy passes all 625 AdS curvature component equalities, 25 Ricci equations, 625 vanishing background Weyl equations, proper-time embedding, SAT identity, readout cancellation and SSPRK3 negative control. New Agda owners are source-written; pinned Agda kernel **OPEN**. The local verification is saved in an XXIX reproducibility bundle. No ESD surfaces edited, and no claim of 369/Monster gravity equivalence.


### XXIX G1 high-alpha addendum — actual *linearized* electric-Weyl slice

Using the ORIGINAL Poincare AdS5 metric, exploit the conformal covariance of the 5D Weyl tensor and examine one local transverse traceless Cartesian polarization of the conformal metric `h_yy=H(T,x,z), h_ww=-H(T,x,z)`. An independent exact SymPy derivation gives `boxFlat H=-H_TT+H_xx+H_zz` and flat linearized curvature
```
delta C_yTyT = -H_TT/2 - boxFlat H/6
delta C_yzyz = -H_zz/2 + boxFlat H/6
delta C_yTyz = -H_Tz/2
```
The actual original moving brane at t=4/3 has orthonormal unit normal `(n^T,n^z)=(-9/16,15/16)` (in 5D Poincare coordinate basis), with `g(n,n)=1`. After the spatial orthonormal factor cancels the conformal lower-index Weyl factor, the resulting normal electric projection is
```
(delta E5_y y)_orthonormal =
  -129/512 H_TT + 3/32 H_xx - 177/512 H_zz + 135/256 H_Tz .
```
This has been verified exactly as a SymPy linearized Weyl / frame-projection identity and as an Agda rational contraction **source** in `KSW668F8LinearElectricWeylPolarizationSliceExact.agda` (kernel pending). It is a **single TT Cartesian polarization at the rational slice**, not yet the original three-harmonic fully moving tensor and not automatically the solver's SMS `E5`. The missing, sharply identifiable G1 weld is: original bulk linearized wave + original moving Neumann/Israel source + gauge and brane tangential/normal derivatives -> equality of this curvature projection to the original on-brane SMS readout `-(H_etaeta+2H_eta-Delta3 H)/(2t²)` in the source-free receiver region. **This equality is OPEN and cannot be inferred from background Weyl=0.**


### XXIX G1 exact source-free Weyl reduction — stronger result

The previous G1 diagnostic with normal derivatives has now been **reduced exactly** under (i) the original bulk TT equation `-H_TT+H_xx+H_zz-(3/z) H_z=0`; (ii) the original source-free moving-Neumann wall `n^A partial_A H=0`, differentiated in brane proper time; and (iii) the same Cartesian TT polarization/gauge. Write `E=dH/dt`, `A=H_TT`, `B=H_xx`. The Neumann constraint gives `H_z=E, H_T=sqrt(1+t²) E`; bulk PDE gives `H_zz=A-B+3tE`. The differentiated boundary condition fixes `H_Tz`, and the brane proper acceleration is
```
H_ddot = (t² A + B - (t³+3t) E)/(t²(t²+2)).
```
The **actual linearized 5D electric Weyl normal projection** and the solver's **SMS** projected readout both reduce, for every real t>0, to
```
Eelectric = E_SMS =
 -(t² A + (2t³+3t) E - (t²+1) B)/(2t²(t²+2)).
```
Independently checked by SymPy on the unperturbed AdS5 geometry with the TT first variation and the original source-free Israel/Neumann boundary. At original t=4/3 the exact rational identity is
```
Eelectric = E_SMS = -9 A/68 + 225 B/1088 - 177 E/272.
```
This particular same-object G1 *mathematical identification for the local source-free Cartesian polarization* is now closed symbolically. An Agda rational-slice source owner `KSW668F8SourceFreeElectricWeylSMSSliceWeldExact.agda` proves the finite wave, differentiated wall and electric/SMS arithmetic, with pinned Agda kernel **not yet run**. The full three angular multipoles, 5D perturbed Einstein–Israel gauge and independent curvature variation proof in Agda remain OPEN; do not promote the restricted equality to full G1.

The prior text calling the source-free normal/SMS identification wholly OPEN applies to the full original solver and general Agda proof, not to this newly verified restricted source-free polarisation computation.


### XXIX G2/G4 further precise cuts

**G2 arbitrary rational source transport:** `KSW668F8WeakIsraelSATGeneralPolynomialTransportExact.agda` reuses the actual original moving wall target relation `(v-1)target=2 amp S-(1+v)P`. It proves, without dividing by `v-1` or `dy`, the polynomial identity
```
dy * SAT_M = 2(1-v)(target-M)
           = -4 amp S +2(1+v)P -2(1-v)M.
```
This is genuinely general in rational v and physical amplitude, with the original target equation supplied as a hypothesis. It is not the fully coupled (U,P,M) moving-wall energy estimate or a strong boundary enforcement result. Pinned kernel open.

**G4 fixed-time whole-space Sobolev trace precursor:** Independent exact SymPy integration gives, in spatial dimension four,
```
int_{R4} |k|^4/(1+|k|²)^5 d^4k = pi²/4,
sup_x |partial_i partial_j H(x)| <= ||H||_{H^5(R4)}/(8pi),
```
with Fourier convention `Hhat(k)=int exp(-ikx)H(x)dx` and Plancherel-normalized inhomogeneous `H^5`. Derivation: polar volume `2pi²` times radial beta integral `int_0^infty r^7/(1+r²)^5 dr=1/8`. This gives an explicit second-derivative **whole-space at fixed time** continuity constant, not the original moving AdS5 boundary trace: the variable warp, half-space extension, time derivatives, compatible Israel boundary and **uniform source-to-H5 evolution estimate** remain entirely OPEN. No assertion that a smooth compact source automatically bounds the solution in the required norm.

**No full-G1..G6 promotion:** The source-free polarized G1 geometric-to-SMS identity and G2 finite SAT lemma close actual mathematical subgates. G3 whole-coupled SSPRK3, G4 time-dependent boundary high-energy, G5 joint mesh convergence, and G6 physical source/receiver are not solved. Existing GR geometry sources are reused with attribution. The PR remains draft for pinned Agda kernel acceptance.


### XXIX central same-object defect theorem (G1/G2 weld)

For the original Poincare AdS5 moving a=t brane, one Cartesian TT polarization, and **arbitrary first/second perturbation jets**, the independent symbolic 5D-curvature calculation and the implemented on-brane SMS readout obey the exact identity
```
E_electric - E_SMS
  = -[(2t²+1)/(2t sqrt(1+t²))] R_N - R_bulk/(3t²),
R_N = (-H_T+sqrt(1+t²) H_z)/t²,
R_bulk = -H_TT + H_xx + H_zz - 3t H_z .
```
Unlike the earlier source-free theorem, this does **not** assume the boundary or bulk equations hold: the two residual terms quantify precisely why the two curvature expressions can differ for an approximate field. The earlier source-free equality is its R_N=R_bulk=0 corollary. These are *continuum geometric differential-jet identities*, not a discrete uniform convergence theorem.

At the original t=4/3 rational slice, an explicit Agda rational-source theorem in `KSW668F8OriginalElectricWeylDefectSliceExact.agda` proves
```
E_electric-E_SMS = -41/40 R_N -3/16 R_bulk .
```
Use original characteristic variables `P=H_T+H_z, M=H_T-H_z` and the actual weak-Israel target `M_target=-5 amp S/4 + P/4`. The exact rational identity becomes
```
E_electric-E_SMS
  = -123/128 amp*S +123/160 (M-M_target) -3/16 R_bulk .
```
At a **source-free receiver** the `amp*S` term vanishes. A pointwise triangle estimate follows with coefficients 123/160 for the characteristic SAT mismatch and 3/16 for the bulk PDE residual. To apply to the computed receiver, however, one still needs a rigorous identification of discrete characteristic variables with the original Cartesian normal jets, plus high-Sobolev/pointwise trace control. Prior XXVI wall residuals were time-integrated shell-weighted L2 and **cannot** be inserted directly into this pointwise identity.

The full arbitrary-positive-t source-jet identity was checked in independent SymPy without imposing the field equations; the t=4/3 contraction/reconstruction is source-written Agda with kernel acceptance pending. The remaining G1 full angular multipoles/TT gauge/covariant linearization and G2 joint energy are **OPEN** despite this much stronger local weld.


## Maximum-cut XXX — original three-channel radial-geometry transport (2026-11-17)

**Goal:** avoid dead-reckoning geometry. Transport the existing XXIX geometric curvature/SMS defect to the ACTUAL original F8 \(H_{\ell}=(r/\epsilon)^\ell V_\ell\) angular decomposition, not an invented extra dimension or independent source.

**New exact rational Agda source** `KSW668F8OriginalThreeMultipoleRadialJetWeldExact.agda`: for ell=0,2,4, write \(c_\ell=\epsilon^{-\ell}\). The angular Laplacian term cancels exactly in
```
r² Delta3 (c_l r^ell V_l Y_l)
  = c_l r^ell [r² V_l'' +(2ell+2)r V_l'] Y_l .
```
The cancellation is encoded in polynomial r² jets, avoiding division by r and using the existing native `KSW668AdS5TTMultipoleAngularRationalExact.agda` owner for d_eff=3,7,11. The exact radial part of the E5-2E4 combination, \(r²(Delta3 H + H_{rr})\), equals
```
ell=2: c2 [2r⁴ V2''+10r³ V2'+2r² V2]
ell=4: c4 [2r⁶ V4''+18r⁵ V4'+12r⁴ V4].
```
These identities are algebraic for the analytic tensor decomposition and for the **same interpolated radial V** under analytic product differentiation; they do NOT imply exact discrete tensor transversality or continuum convergence.

**New guarded three-channel transport** `KSW668F8ThreeChannelElectricWeylDefectTransportExact.agda`: if each corresponding TT *tensor* component satisfies the original t=4/3 same-object electric-vs-SMS residual identity, the common receiver sum obeys
```
Sum_l(Eelectric_l)-Sum_l(ESMS_l)
 = -(41/40) Sum_l(RN_l) -(3/16) Sum_l(Rbulk_l).
```
The record **requires** the channelwise tensor/gauge hypothesis; the three scalar multipoles of a single `yy` component are not independently TT tensors. This is the exact missing hypothesis for the full G1 formal promotion, not evidence it has been fulfilled.

**Independent local verification:** `scripts/test_ksw668_f8_three_harmonic_weyl_transport.py` verifies all three ell radial identities, the original arbitrary-jet electric-Weyl/SMS residual, the actual fourth-order tensor-TT projector and the three-way linear sum (6 mathematical checks). The existing XXVI saved `h=.004` forward wall state was independently inspected, using the original four-node cubic interpolation and its derivatives: **15/15 checks** of Hrr, Lap3H, r² polynomial bridge, and E5-2E4 by channel PASS. Max absolute radial bridge residual 1.11e-16; dual readout residual 2.17e-19. NO new wave evolution or numerical convergence was claimed.

**Updated remaining maximum cut:**
- G1: show the *full original* `PQP-(1/2)P tr(PQ)` source, bulk tensor field, and three angular `H_l` reconstruction commute with discrete TT divergence, trace, gauge and normal projection at the receiver; extend rational polarization slice to all-t Agda geometry. **OPEN**.
- G2: use the defect theorem to define stage-resolved original Neumann/SAT and bulk residuals, and prove a meaningful pointwise boundary trace from a norm measured by the solver. **OPEN**.
- G3: coupled moving `(U,P,M)` energy and SSPRK3 CFL with outer-wall flux. **OPEN**.
- G4: uniform source-to-H5/higher Sobolev estimate on the moving warped half-space to bound both pointwise Weyl readouts. **OPEN**.
- G5: independent `dr,dy,dt` convergence for H, E4, E5 and outside-cone null; no convergence claim from r² jet identities. **OPEN**.
- G6: same-object matter action, retarded tensor FIO, detector calibration/observation. **OPEN**.

**Acceptance/attribution firewall:** source-written Agda; pinned Agda kernel NOT RUN. Original KSW model/TT source, Caldwell–Langlois, Thorne and other cited mathematics retain credit. The user-directed maximum-cut and newly derived conditional algebra are recorded separately; no ESD edits, no unrelated Monster/369 physical correspondence.


## Maximum-cut XXXI — full original tensor TT symbol versus discrete derivative mismatch

The original TT differential operator is NOT merely the scalar yy channel. For every 3-vector frequency `k=(a,b,c)`, `P_ij=|k|² delta_ij-k_i k_j`, and `Q=diag(0,1,-1)`, the **original** fourth-order generator is
```
T_ij(k) = (P Q P)_ij -(1/2) P_ij trace(P Q).
```
With precisely the **same derivative symbol** in both `P` and the divergence, exact rational polynomial identities prove:
```
k_i T_ij(k) = 0 (all three components), trace(T)=0,
T_ij=T_ji, P(k)k=0, P(k)^2=|k|² P(k).
```
These remain algebraically true if the same `k` is replaced by a common discrete Fourier derivative symbol, such as a compatible central difference `sin(k_i h)/h`. This does NOT show that the existing radial finite-volume scalar reduction has this exact tensor-compatible symbol.

**Crucial exact negative control:** Construct `T` with original symbol `k=(1,2,3)` and test divergence with a distinct symbol `k_tilde=(1,1,2)`. The resulting exact divergence is
```
T(1,2,3)*(1,1,2) = (-3/2, -24, 33/2),
```
even though `T(1,2,3)*(1,2,3)=0` and `trace T=0`. Thus source shell-mass coarsening, a noncommuting interpolation, or a mismatched radial operator **cannot be promoted automatically to discrete tensor TT conservation**. The earlier six-grid common source-mass additivity does not establish this claim.

**New source-owner:** `DASHI/Physics/Gravity/KSW668F8TTSymbolDiscreteCompatibilityExact.agda` proves the six polynomial statements for exact rational symbols, with four general identities (all transverse components and trace) and three specific incompatible-symbol counterexample values. New Python test `scripts/test_ksw668_f8_tt_symbol_discrete_compatibility.py` independently checks the full original 3x3 Fourier projector, all three constraints and the exact negative control (7/7 pass). All work is source-written, with Agda kernel **not run**.

**Next formal producer G1:** Construct the actual Cartesian discretization/transfer operators and their commuting diagram to the existing `d=3,7,11` radial FV carriers. Need an explicit map from the full tensor angular decomposition to all componentwise radial discretizations, not just `H_yy`. Then prove or measure discrete divergence/trace defects at the original receiver and source, with boundary and smoothness control. The new finite symbol theorem is a reusable prerequisite, not a replacement for the original simulation.

**Gate accounting:** G1 full original tensor discrete commutation OPEN; G2 original joint weak Israel SAT energy OPEN; G3 coupled SSPRK3 stability OPEN; G4 moving-domain high-Sobolev both-Weyl trace OPEN; G5 independent three-axis convergence OPEN; G6 original matter/FIO/detector OPEN. Original source and paper attributions remain in owners; new mathematics/negative controls remain separately documented. No ESD code changed.


### XXXI exact derivative-symbol mismatch defect and next G1 max-cut

For the same original 3-by-3 fourth-order tensor source symbol `T(k)`, and ANY independent rational discrete divergence symbol `q`, the newly source-written Agda owner proves three componentwise polynomial identities
```
q_i T_ij(k) = (q_i-k_i) T_ij(k),    j=x,y,z.
```
Thus pointwise symbol consistency yields a quantitative norm estimate
```
|T(k) q|_2 <= ||T(k)||_F |q-k|_2,
```
by ordinary Cauchy--Schwarz (the norm inequality is independently mathematical, NOT new Agda-checked code). This isolates the discrete TT leakage producer `q-k`. At matched symbols `q=k`, the divergence is algebraically zero; at original source `k=(1,2,3)` and mismatched `q=(1,1,2)`, leakage is `(-3/2,-24,33/2)`. Original scalar shell-mass coarsening does not give the requisite matching-symbol property.

**Next priority:** identify and prove the full tensor-to-existing F8 radial FV comparison map, then bound its symbol/commutator defect under nonperiodic origin and wall closures; this cannot be inferred from the periodic/constant-coefficient symbol alone. Only after that pursue a coupled G2/G3 stability estimate plus G4 high-regularity trace to promote these finite identities to G5 convergence. G6 remains physical and evidence-dependent.


### XXXI manufactured centered-difference symbol diagnostic (nonphysical)
For fixed `k=(1,2,3)` and mismatched centered-derivative symbol `q_i(h)=sin(k_i h)/h`, exact Taylor algebra gives `T(k)q(h)=(-105,21,21)h²+O(h⁴)` as `h→0`. The independent audit found Euclidean norm `4.2638967157, 1.0848419878, 0.2724004105, 0.0681746399` at `h=.2,.1,.05,.025`. This illustrates the quantitative symbol-defect criterion, **not** the nonuniform radial FV/SAT scheme or a physical Weyl convergence rate. The actual original operator's boundary-compatible symbol/commutator still requires proof.


## Maximum-cut XXXII — ORIGINAL radial shell FV exact Green proof and conjugation no-go

**Source reuse:** Read and matched `scripts/ksw668_f8_tt_multipole.py`, `scripts/ksw668_f8_fv_source_flux.py`, and `KSW668AdS5TTFiniteVolumeFirstCellRationalExact.agda` before adding any owner. The original F8 solver evolves *regularized scalar* `V_l` for `d=3,7,11` with exact radial shell weights, not independent discretized Cartesian TT components. Keep original source authorship and Caldwell–Langlois/Thorne attribution.

### G1/G3 actual finite shell Green algebra

On `r_j=j h`, effective `d=3+2ell`, let
```
W_j = ((j+1/2)^d - max(j-1/2,0)^d) h^d/d,
A_(j+1/2) = (j+1/2)^(d-1) h^(d-2).
W_j (L_d,h V)_j = A_(j+1/2)(V_(j+1)-V_j)
                   - A_(j-1/2)(V_j-V_(j-1)).
```
For `j=0`, `W0*2d/h²=A_(1/2)`. For the actual d=3,7,11 first interior coefficients reuse original `FV.d3Plus/d3Minus`, etc. This exact first-row mass/face identity is now source-written in `KSW668F8RadialFVGreenAndQuarticConsistencyExact.agda`. The module proves algebraically, for any finite list of face traces,
```
Sum_faces A[(u_L)(v_R-v_L) + (u_R)(v_L-v_R)]
 = -Sum_faces A (u_R-u_L)(v_R-v_L).
```
With zero final Dirichlet endpoint, it assembles to the **original** interior weighted Green identity:
```
Sum_{j=0}^{N-2} W_j u_j (L_d,h v)_j
 = -Sum_{j=0}^{N-2} A_(j+1/2)
                 (u_(j+1)-u_j)(v_(j+1)-v_j).
```
The facewise finite-list theorem and concrete first-shell weights are source-written; the assembly of the face traces with all original `j` shell coefficients is **not separately proven for arbitrary N in Agda**. An independent exact Fraction regression tested 12 arbitrary vector pairs per dimension with zero Dirichlet last node, and all three d passed. Nonpositive radial self-energy is thus true for that scalar operator; fully coupled y/r/warp/SSPRK3 energy still OPEN.

### G1/G5 manufactured original-operator consistency

The original FV is exactly quadratic: `L_d,h(r²)=2d` for all interior radial rows and at origin. The first nonzero `r⁴` truncation is
```
L_d,h(r⁴) - 4(d+2)r² = h² e_(d,j)
origin: e_(3,0)=6, e_(7,0)=14, e_(11,0)=22;
j=1:   e_(3,1)=142/13,
       e_(7,1)=37190/1093,
       e_(11,1)=5137278/88573.
```
Exact rational first-interior and origin cases implemented in the new FV owner and checked independently; finite regularity/local consistency does NOT imply mesh-uniform solution/readout convergence.

### Exact negative control — no naive discrete radial conjugation

Continuum `H_l=r^ell V_l` conjugates the 3D spherical Laplacian to effective `d=3+2ell` scalar radial operator. That identity **does not commute** with the naive alternative "FV d=3 on H, subtract ell(ell+1)H/r²". At `h=eps=1`, `j=1`:
- ell=2, V=r², H=r⁴: naive d3 FV minus centrifugal, compared with actual d7 FV of V, differs by exactly `142/13`.
- ell=4, V=1, H=r⁴: naive d3 FV minus centrifugal, compared with actual d11 FV of V, differs by exactly `142/13`.
New `KSW668F8RadialConjugationNoncommutationExact.agda` contains both exact rational negative controls. This does **not** show a bug in the original F8 solver: it never evolves H under the naive alternative. It shows that a new Cartesian tensor-to-existing-radial-FV commuting map must incorporate the correct discrete projection/transfer; the continuum `r^ell` identity and shell mass conservation are insufficient.

### Verification and priority

`scripts/test_ksw668_f8_radial_fv_green_and_conjugation.py` evaluates exact Fractions, 47/47 tests (three dimensions × [quadratic, quartic, face mass, 12 random Green vectors], plus two mismatch controls). All pass in independent local equivalent. The new Agda owner contains a generic finite-face Green telescope but **pinned Agda kernel NOT RUN**; all analytic, physical and higher-Sobolev kernel gates remain open.

**Priority ordering:** G1 full tensor-to-original-scalar-radial-FV compatible projection (including origin and normal SAT); G2 joint Israel/SAT/wall residual trace; G3 coupled moving-domain and SSPRK3 stability; G4 original boundary high-Sobolev both-Weyl trace; G5 independent three-axis convergence; G6 same source/retarded FIO/matter/detector. Continue reuse before construction and attach via existing KSW authority + TOE graph. Preserve attribution and no ESD edits.


### XXXII second positive G1 bridge: original angular Gram explains d=3,7,11

The original scalar yy multipole fields use `H_l(r,mu)= (r/eps)^l V_l(r) P_l(mu)` with only `l=0,2,4`. Reuse the existing exact Legendre owner; integrate against the actual angular measure `dmu` on `[-1,1]`. An exact rational even-moment calculation `int mu^(2n)dmu=2/(2n+1)` yields the entire 3-by-3 Gram matrix
```
G_(l,m) = int_-1^1 P_l(mu)P_m(mu)dmu
        = diag(2, 2/5, 2/9)_(l,m).
```
Thus the **original yy scalar** angular L2 norm with ordinary physical 3D radial measure `r² dr dmu` is
```
Sum_l 2/(2l+1) eps^(-2l)
    int_0^R r^(2+2l) |V_l(r)|² dr.
```
This explains precisely why the solver evolves modes in effective scalar radial measures `d=3+2l=3,7,11`, rather than inventing new physical bulk dimensions. New owner `KSW668F8ThreeAngularGramRadialMeasureExact.agda` proves all six distinct exact rational Gram entries. `scripts/test_ksw668_f8_angular_gram_effective_radial.py` independently checked all 9 Gram entries and 3 radial-measure identities (12/12 PASS). **Important scope:** this is the yy scalar angular norm, not the full TT Cartesian 3-by-3 tensor norm (which requires other angular tensor components and their contractions). The actual FV shell quadrature also requires a separate angular-to-cell-average norm/isometry or stability map. This owner is attached to existing F8 authority / KSW/TOE import graph; pinned Agda kernel NOT RUN.

This newly proven Gram relation plus the exact radial-shell Green telescope is a legitimate *positive scalar operator* reuse path for G1 and G3. The explicit noncommutation counterexample means the positive scalar result still does not establish the full tensor-TT commuting diagram. Prioritize full tensor angular Gram + discrete projection matching and origin/SAT boundary as the next original-object weld.


## Maximum-cut XXXIII — ORIGINAL full tensor TT Fourier angular norm and fourfold mode

**Direct source provenance:** Reused `KSW668F8TTSymbolDiscreteCompatibilityExact.agda`, `KSW668AdS5TTMultipoleAngularRationalExact.agda`, `KSW668F8ThreeAngularGramRadialMeasureExact.agda` and `scripts/ksw668_f8_prepotential_commutation.py`. These define the original fourth-order Fourier polynomial
```
P(k)=|k|² I-kkᵀ, Q=diag(0,1,-1),
T(k)=PQP-(1/2)P tr(PQ).
```
A new original full tensor norm owner, `KSW668F8FullTensorAngularNormExact.agda`, proves for **arbitrary rational** Cartesian k=(x,y,z) the exact six-component Frobenius identity
```
||T(k)||_F² =
  (|k|⁴/2) * [(2x²+y²+z²)² - 4y²z²].
```
This is a **tensor**, not the original `yy` component. Consequently it is not axisymmetric pointwise even when the yy scalar axisymmetric readout uses only P0/P2/P4.

On the unit wavevector sphere parameterize x=mu, y=sqrt(1-mu²) cos(phi), z=sqrt(1-mu²) sin(phi). Independently symbolically checked:
```
||T||_F² = (mu⁴+6mu²+1)/4
            + (1-mu²)² cos(4phi)/4 .
```
Therefore azimuthal averaging (uniform dphi/(2pi)) removes an **m=4** term and gives
```
<||T||_F²>_phi = (mu⁴+6mu²+1)/4
               = 2 originalTTYYAngular(mu)
               = (4/5) P0(mu)+(8/7) P2(mu)+(2/35) P4(mu).
int_-1^1 <||T||_F²>_phi dmu = 8/5
```
(with the 2pi azimuth factor omitted). The equality `<||T||²> = 2 T_yy,average` compares the **squared full tensor** and **linear yy component** for this specially chosen Q; do not misread it as a norm equality for arbitrary yy scalar fields or as a tensor isometry. It is an exact Fourier angular identity for the ORIGINAL generator.

**Sharp nonaxisymmetry negative control:** Two rational unit vectors have the same mu=kx=0:
```
k=(0,1,0): ||T||²=1/2
k=(0,3/5,4/5): ||T||²=49/1250.
```
Thus the axisymmetric yy `l=0,2,4` information alone cannot specify the full tensor's pointwise angular energy. A concrete m=4 azimuthal sector survives in the full norm, although its phi integral is zero. The negative control does **not** show that original radial yy observables are wrong: they only represent the selected component and observation axis.

**Implementation / validation:** new original `KSW668F8FullTensorAngularNormExact.agda` rational polynomial norm factorization, normalized angular average, Legendre expansion, integrated moment, exact azimuth-difference control; and `scripts/test_ksw668_f8_full_tensor_angular_norm.py` independently checks 12 full symbolic conditions. Code attached to existing G1--G6 authority, canonical KSW/TOE import graph. Pinned Agda kernel **not run**, and its rational azimuth-moment assumptions need a separately formalized actual integral carrier.

**Updated Pareto gates:**
- G1 next: construct the **complete original tensor spherical-harmonic/angular component reconstruction**, retaining m!=0 and index/polarization structure, and identify precisely which part is needed for the yy receiver vs tensor energy. Prove angular projection/commutator with the ORIGINAL effective radial FV and origin/outer closures. Full tensor-to-radial FV energy isometry remains OPEN.
- G2: joint moving original Israel/SAT boundary energy and trace OPEN.
- G3: full coupled moving weighted SSPRK3 stability OPEN.
- G4: actual 5D-to-brane higher-Sobolev source-to-both-Weyl trace OPEN.
- G5: independently certified dr/dy/dt convergence OPEN.
- G6: same matter, retarded FIO and calibrated detector OPEN.

Original KSW/Thorne/Caldwell--Langlois source attribution and user-directed research programme preserved. No ESD edit, no unrelated Monster/369 geometric equivalence, no physical detector claim.


## Maximum-cut XXXIV (2026-11-17) — complete original Fourier tensor atlas and exact rational axial angular projection

**Priority:** reuse the original fourth-order KSW F8 Fourier-space TT generator `T=PQP-P tr(PQ)/2` and existing `KSW668AdS5TTMultipoleAngularRationalExact.agda`, rather than infer geometry from receiver data. This does not alter the original F8 solver, ESD or other owners.

### G1 original full 3×3 tensor solid-spherical-harmonic atlas

For longitudinal Fourier coordinate `x=kx`, transverse `y=ky, z=kz`, `K=x²+y²+z²`, six polynomial component identities expand the **complete** original TT tensor on real (Condon–Shortley) solid harmonics `H_lm^(cos/sin)` of homogeneous degree four. The modes present are:
```
Txx : (ell,m)=(2,2)c,(4,2)c
Txy : (2,1)c,(4,1)c,(4,3)c
Txz : (2,1)s,(4,1)s,(4,3)s
Tyy : (0,0),(2,0),(4,0),(2,2)c,(4,2)c,(4,4)c
Tyz : (4,4)s
Tzz : (0,0),(2,0),(4,0),(2,2)c,(4,2)c,(4,4)c
```
(There are no odd ell sectors, but there ARE odd azimuth m=1,3 sectors in the off-diagonal tensor components.)

Using `K P_l^m` for l=2 and `P_l^m` for l=4, the exact coefficients in `KSW668F8FullTensorSolidHarmonicAtlasExact.agda` are:
```
Txx = (4/21) H22c +(1/105) H42c
Txy = (2/7) H21c +(1/70) H41c -(1/420) H43c
Txz = -(2/7) H21s -(1/70) H41s -(1/420) H43s
Tyy = (2/5) H00 +(4/7) H20 +(1/35) H40
      -(2/21) H22c -(1/210) H42c +(1/840) H44c
Tyz = (1/840) H44s
Tzz = -(2/5) H00 -(4/7) H20 -(1/35) H40
      -(2/21) H22c -(1/210) H42c -(1/840) H44c.
```
Six exact SymPy polynomial residuals vanish identically; original trace and all three divergence constraints also checked. **These are Fourier tensor identities, not a rebuilt real-space 3×3 tensor evolution or the Agda-pinned source-to-Weyl theorem.**

### New exact *finite* rational projector for the original axial receiver

Construct a 12-node positive-weight rational circle cubature:

- Four cardinal nodes `(±1,0),(0,±1)` with weight `527/4608` **each**
- Eight nodes `(±3/5,±4/5),(±4/5,±3/5)` with weight `625/9216` **each**

The weights are positive and sum to one. Direct exact rational evaluation reproduces all 15 uniform-circle monomial moments `y^i z^j` for `i+j<=4`. In particular `<y²>=<z²>=1/2`, `<y⁴>=<z⁴>=3/8`, `<y²z²>=1/8`, and odd moments vanish.

For ANY rational longitudinal `x` and transverse radius `rho`, applying this angular projector to all six original tensor components `T(x,rho y,rho z)` gives exactly
```
Proj_angular T = diag(0, A(x,rho), -A(x,rho)),
A(x,rho)=[(x²+rho²)²+6(x²+rho²)x²+x⁴]/8.
```
At `x²+rho²=1`, `A=(x⁴+6x²+1)/8`, exactly the original F8 `yy` P0/P2/P4 angular source polynomial. The original receiver lies on the x axis and the Fourier factor `exp(i kx receiver_x)` is independent of azimuth, so the projector is exact on the fourth-order tensor multiplier **at each Fourier momentum for this axial geometry**. It is not an exact cubature for generic off-axis wave factors or full inverse Fourier transforms without integrability/commutation arguments.

**Adversarial 4-node control:** averaging only the four cardinal directions aliases the `m=4` original `yy` tensor contribution and yields `A(x,rho)+rho⁴/8`, a nonzero defect for `rho≠0`. This is a concrete reason not to use coarse azimuth sampling in any future tensor-to-FV adapter.

New Agda rational source owner `KSW668F8RationalAxialTTCubatureExact.agda` states exact finite angular moments, all six projected tensor components and the four-cardinal alias identity. New independent SymPy scripts `test_ksw668_f8_full_tensor_solid_harmonic_atlas.py` and `test_ksw668_f8_rational_axial_tt_cubature.py` check all six atlas identities and **21/21** cubature tensor/moment checks. This cut creates no new physical run and no source reconstruction of the full real-space tensor.

### Refined G1–G6 cut-set (Pareto)

- **G1 Fourier angular subgate:** full six-component angular atlas and constructive rational axial projector source-written and independently symbolically verified. **Next G1 physical operator weld:** original radial inverse-transform/projection to exact conservative d=3,7,11 source and finite-volume solver, including axis/origin stencil and P/M/U moving SAT; prove a discrete tensor divergence/trace defect bound or compatible commuting diagram. General 3×3 tensor energy remains OPEN.
- **G2:** use original SAT Neumann and PDE residual equations to control a pointwise *tensor* electric-Weyl/SMS discrepancy, not just an integrated scalar wall norm; joint energy OPEN.
- **G3:** fully coupled moving warp/FV/SBP2 SAT SSPRK3 stability and admissible CFL OPEN.
- **G4:** uniform moving-domain Sobolev source-to-two-Weyl receiver trace OPEN.
- **G5:** independent dr/dy/dt receiver and outside-cone convergence certificates OPEN.
- **G6:** original matter action, retarded tensor FIO, physical detector and independent replenishment/evidence OPEN.

**Acceptance/provenance:** exact SymPy polynomial and rational finite cubature checks PASS; pinned Agda kernel NOT RUN. User-directed maximum-cut continuation and original mathematical derivations separated from original DASHI/Caldwell–Langlois/Thorne prior art. No ESD modifications; no Monster/369 physical equivalence; no detected graviton claim.


## Maximum-cut XXXV — original angular source projection and conservative radial cell carrier (2026-11-17)

**Reused original same-object source code:** `scripts/ksw668_f8_tt_multipole.py` (three regularized sources `G_l=S_l/u^l`, effective `d=3+2l`, normal_order=3) and `scripts/ksw668_f8_fv_source_flux.py` (original endpoint primitives `p0,p2,p4`, smooth l4 rest integral, finite source cell mass) plus the XXXIV 12-node exact rational tensor axial projector. Original source/papers/attribution intact.

**Positive finite commuting result (G1 source angular stage):** the **original** 12-node angular operator `A_12` is linear for arbitrary rational angular samples. For every source shell mass `M` and full original tensor Fourier polynomial `T(k)` at fixed longitudinal x and transverse rho,
```
A_12[M T_yy(x,rho y,rho z)] = M A(x,rho);
A_12[M T_zz(x,rho y,rho z)] = - M A(x,rho).
```
The other projected tensor components vanish as already proved in XXXIV. This ensures that **multiplication by an already-computed scalar source mass** can be performed before or after the finite angular projector. It is an exact discrete angular/source scalar-multiplication relation, NOT an integral interchanger for an arbitrary radial tensor field or the complete tensor-to-FV commuting diagram.

**Original source-cell mass carrier:** for each ell=0,2,4, `d=3+2ell`, and `u=r/eps`, the original solver computes
```
M_(ell,j) = eps^d * integral_(u_a)^(u_b) u^(d-1) G_ell(u) du;
W_(ell,j) = (r_hi^d-r_lo^d)/d;
source_(ell,j) = M_(ell,j)/W_(ell,j).
```
Source code `cell_mass` uses endpoint derivatives `p_ell(u_b)-p_ell(u_a)`; for ell=4 it also adds the `27 integral u² f(u) du` rest term. The new `KSW668F8AxialProjectionSourceShellTransferExact.agda` proves the algebraic finite telescope of arbitrary endpoint primitives and finite angular scaling/additivity. It does NOT prove that the analytic compact bump derivatives admit these primitives, which remains original SymPy/analytic source ownership.

**Critical origin counterexample for any naive alternative transfer:** the physical `yy` source before regularization is `S_ell(u)=u^ell G_ell(u)`. Averaging it with ordinary 3D volume `u²du` is not the same as taking the original effective-dimensional average of `G_ell` then multiplying by `u_center^ell`. Take manufactured `G_ell(u)=1` and the actual original resolution ratio `h/eps=.008/.04=1/5`, first half-cell `[0,h/(2eps)]=[0,1/10]`. Then
```
ordinary 3D first-cell mean of S_0 = 1,
ordinary 3D first-cell mean of S_2 = 3/500,
ordinary 3D first-cell mean of S_4 = 3/70000;
centre-evaluated u_center^ell * mean_eff G_ell = 0 (ell>0).
```
The original code does **NOT** perform that naive centre reconstruction as its source integration. Thus this is a guardrail for future tensor/real-space source transfer, not a detected bug. The finite source-cell weighted masses are additive over arbitrary subdivisions; a local exact-Fraction randomized partition audit found **63/63** passing controls. The committed combined regression `scripts/test_ksw668_f8_source_shell_projection_transfer.py` additionally checks the angular tensor/mass multiplier for both yy and zz.

**Next max-cut G1:** a **nontrivial tensor-mode-to-source FV map** must compare the projected full 3D Cartesian TT differential source before radial averaging with the original exact `G_l` primitives under proper `r^{2+2l}` measure, prove the requisite differential projection/integration commutators and handle r=0 plus moving characteristic SAT. The existing algebraic angular/mass commutation only covers multiplying a precomputed shell mass by an angle-independent tensor multiplier. Do not claim all-dimensional tensor evolution or electric-Weyl convergence from this. G2 joint SAT energy, G3 moving SSPRK3, G4 moving high-Sobolev both-Weyl trace, G5 independent three-axis convergence, G6 physical FIO/matter/detector remain OPEN. Pinned Agda 2.9 kernel NOT RUN. No ESD edits, no false Monster/369 geometry promotion.


### XXXV second source weld — original fourth-order TT profiles vs original finite-volume primitives

This round additionally verified the **actual differential identities** in `scripts/ksw668_f8_fv_source_flux.py` against the original fourth-order profiles of `scripts/ksw668_f8_tt_multipole.py`. Let `f_n=d^n f/du^n` and `G_ell=S_ell/u^ell`, `d=3+2ell`. The original weighted source densities are
```
u² G0   = (2/5)(u² f4 +4u f3)
u^6 G2  = (4/7)(u⁴ f4+u³ f3-6u² f2+6u f1)
u^10 G4 = (u⁶ f4-6u⁵ f3+15u⁴ f2-15u³ f1)/35.
```
The unchanged original primitive formulas are
```
P0=(2/5)(u² f3+2u f2-2f1)
P2=(4/7)(u⁴ f3-3u³ f2+3u² f1)
P4=(u⁶ f3-12u⁵ f2+75u⁴ f1-315u³ f0)/35.
```
Direct exact symbolic differentiation proves **for arbitrary smooth f**, not only the compact exponential bump:
```
dP0/du=u² G0;
dP2/du=u^6 G2;
dP4/du+27u²f=u^10 G4.
```
The **l4 residual is essential**. Removing its `27 integral u² f(u) du` term from original FV would be a source-changing error, not a cleaner zero-mean TT construction.

New `KSW668F8OriginalTTSourcePrimitiveJetExact.agda` contains explicit original-product-rule formal-jet identities for all three channels (source-written, pinned kernel pending); new `scripts/test_ksw668_f8_original_tt_source_primitive_jet.py` proves the calculus identities independently with SymPy for a symbolic differentiable function (3/3 PASS). The Agda formal-jet ring proof is **not** a separately kernel-checked theorem about actual smooth-function differentiation; retaining that distinction is required.

**Progress:** XXXIV exact full-tensor rational axial projector -> XXXV exact commutation with a scalar source shell mass -> actual three original TT source weighted primitive differentiation -> conserved effective-d source cell averages. This closes the algebra of the existing source handoff locally but does **not** commute angular tensor differential operators with independent radial FV evolution or prove tensor TT conservation for discrete source/receiver. The full G1 Cartesian tensor differential/source-to-effective-FV diagram with origin closure, G2 stage SAT, G3 coupled SSPRK3, G4 higher-Sobolev moving-brane trace, G5 independent mesh limit and G6 calibrated physical action/FIO/detector remain OPEN.


## Maximum-cut XXXVI — original fourth-order Cartesian TT → exact three radial source profiles (2026-11-17)

### Reuse and scope
Reuse the existing same original 5D tensor generator `T(k)=P(k)Q P(k)-P(k)tr(P(k)Q)/2`, `Q=diag(0,1,-1)`, the XXIV–XXXV original full tensor angular atlas and exact axial azimuth projector, and **unchanged** source owners `scripts/ksw668_f8_tt_multipole.py:profiles()` and `scripts/ksw668_f8_fv_source_flux.py:primitives()`. This round does not introduce another geometry implementation, scalar source or incompatible radial FV definition.

### New nontrivial differential source weld (G1)

From the **actual** fourth-order Cartesian operator (the yy symbol written as `kx⁴+(1/2)kx²ky²+(3/2)kx²kz²-(1/2)ky²kz²+(1/2)kz⁴`) and a smooth radial prepotential `f(r)`, let `D=(1/r)∂r`. The fourth-derivative tensor chain rule and the original azimuthal moments yield, for `r>0`,
```
< T_yy(∂) f >_phi
 = 6 D² f + (2+6μ²) r² D³ f
   + [(μ⁴+6μ²+1)/8] r⁴ D⁴ f.
```
Because `2+6μ²=4P0+4P2` and `(μ⁴+6μ²+1)/8=(2/5)P0+(4/7)P2+(1/35)P4`, the three original projected source modes are EXACTLY
```
f_0 = 6 D² f +4r²D³ f +(2/5)r⁴D⁴ f
f_2 = 4r²D³ f +(4/7)r⁴D⁴ f
f_4 = (1/35)r⁴D⁴ f.
```
With formal derivative jets `f1=f',f2=f'',f3=f''',f4=f''''`, multiply by `r⁴` to avoid any division at the axis:
```
J2=r⁴D²f = r² f2-r f1
J3=r⁶D³f = r³ f3-3r² f2+3r f1
J4=r⁸D⁴f = r⁴ f4-6r³ f3+15r² f2-15r f1.
```
Then `r⁴ f_0=6J2+4J3+(2/5)J4`, `r⁴ f_2=4J3+(4/7)J4`, `r⁴ f_4=(1/35)J4`. The polynomial identities simplify EXACTLY to the **actual original `profiles()` source formulas**:
```
r⁴ f_0=(2/5)(r⁴ f4+4r³ f3)
r⁴ f_2=(4/7)(r⁴ f4+r³ f3-6r² f2+6r f1)
r⁴ f_4=(1/35)(r⁴ f4-6r³ f3+15r² f2-15r f1).
```

### Exact interface to the EXISTING conservative source primitives
Reuse `KSW668F8OriginalTTSourcePrimitiveJetExact.agda` (source-written earlier) and the primitive identities already checked in XXXV. With `G_l=f_l/r^ell`, the actual weighted source densities are `W_0=r²G0`, `W_2=r^6G2`, `W_4=r^10G4`. The new origin-safe finite algebra proves
```
r² W_0=r⁴ f_0,       W_2=r⁴ f_2,       W_4=r²(r⁴ f_4).
```
The original primitive integration identities are `P0'=W0`, `P2'=W2`, and **`P4'+27r²f=W4`**. Together, these give a concrete source-level chain from original Cartesian TT differentiations to the original finite-volume source integral, including the indispensable ell4 rest term. They DO NOT assert that radial multiplication commutes with a separately chosen finite-difference tensor derivative, nor license division by r at r=0 without smoothness/limit witnesses.

### Implementation, verification and interpretation
New `DASHI/Physics/Gravity/KSW668F8CartesianTTToOriginalRadialSourceJetsExact.agda` implements the original Cartesian yy tensor polynomial, second angular chain-rule factor, Legendre decomposition, regularity-safe polynomial jet identities, comparison to all three unchanged source profiles, and direct weighted-source identities importing the original primitive owner. Imported into existing `KSW668F8SameObjectWeylAuthorityBoundary.agda` and thus original KSW/TOE graph.

`scripts/test_ksw668_f8_cartesian_tt_radial_differential_weld.py` independently differentiates an arbitrary symbolic radial `F((x²+y²+z²)/2)` four times using the true Cartesian TT polynomial, azimuthally averages, derives all three profiles, crosschecks actual original source primitive derivatives (including ell4 remainder) and confirms all three no-division weighted transfers. **16/16** independent local symbolic checks PASS; additionally two negative controls confirm that omitting the `D²`/`D³` terms falsely changes ell0/ell2.

**G1 status:** the original smooth Fourier/real-space **source handoff** from the fourth-order TT yy generator to exact effective-shell FV source inputs is now verified at the symbolic differential/algebra level for radial smooth f. The Agda theorem is finite rational jet algebra, **not** a pinned-kernel smooth-calculus theorem. The actual full Cartesian tensor-to-scalar-FV **evolution** commuting diagram, discrete TT preservation through radial shell projection/axis closures, weak-Israel `P,M,U` wall/gauge and electric-Weyl pointwise error estimate remain OPEN.

**G2–G6:** G2 joint SAT boundary energy OPEN; G3 moving warp/normal/radial SSPRK3 + uniform CFL OPEN; G4 moving-domain high Sobolev to both-Weyl trace OPEN; G5 independently convergent dr,dy,dt full receiver and outside-cone controls OPEN; G6 same original matter source, retarded tensor FIO and physically calibrated detector OPEN. Keep source authorship, Caldwell–Langlois/Thorne prior art and user-directed max-cut distinct. No ESD edits or Monster/369 gravity theorem claims.


## Maximum-cut XXXVII — exact original FV reconstruction **with origin trace** and SSPRK3 stage naturality

**Most significant new cut:** The XXXVI smooth Cartesian TT → actual three source modes/finite-volume masses is not yet an operator-level discrete evolution theorem. Inspecting the ORIGINAL `scripts/ksw668_f8_tt_multipole.py:stage` radial stencil identified an exact and previously hidden requirement: **the full regularized origin trace V0 is indispensable** for reconstructing the original evolved `H_l=(r/eps)^l V_l`, for ell=2,4.

The original effective-dimensional FV operator at first interior index j=1 in grid units is
```
(L_d V)_1 = cp_(d,1)*(V_2-V_1) - cm_(d,1)*(V_1-V_0),
d=3+2ell.
```
Write `lambda=(h/eps)^ell`, `H_1=lambda V_1`, `H_2=2^ell lambda V_2`. Its **exact induced physical radial operator**, including the origin, is
```
lambda (L_d V)_1 =
  cp_(d,1)*(H_2/2^ell-H_1)
  -cm_(d,1)*(H_1-lambda V_0).
```
This is source-written in new `KSW668F8AugmentedOriginRadialFVIntertwinerExact.agda` and independently verified with exact Fractions across all three original d=3,7,11 dimensions and every numerical row. For j>=2, the induced physical stencil is
```
(jh/eps)^ell (L_d V)_j =
   cp_(d,j)*[(j/(j+1))^ell H_(j+1)-H_j]
  -cm_(d,j)*[H_j-(j/(j-1))^ell H_(j-1)].
```
This is a **positive EXACT discrete operator-level commuting diagram** between original regularized FV and its induced physical harmonic radial lift, but only when the regularized origin state is retained. The physical `1/h²` factor is common to both sides. It does not assert that an independently chosen Cartesian 3D tensor FV operator agrees with the induced one.

**Sharp same-reconstructed-field negative control:** For ell>0, changing `V_0` does not change ANY physical node `H_j` when `V_j=0` for j>=1; `H_0=0` regardless of `V_0`. Yet if `V0=1` and all later V_j=0, at grid h=eps=1 the original induced radial force at j=1 is
```
ell=2, d=7:  cm_(7,1)=7/1093;
ell=4, d=11: cm_(11,1)=11/88573.
```
Thus there is **no closed local FV operator on these H samples alone** reproducing the original solver; it must carry V0 or an equivalent origin derivative jet. More generally the exact first-shell defect from using an incorrect origin trace is
```
delta radial force = [cm_(d,1)/h²] * lambda * (V0-V0_assumed).
```
A separate arbitrary-interior ratio theorem gives the exact defect as two face-weighted reconstruction ratio errors. This supplies a concrete, numerical-source-independent G1/G5 error target.

**Stage and time-step compatibility:** The original normal_order=3 semidiscrete U/P/M formulas are linear in their fields and SAT target when geometry `b(T),v(T)`, source amplitude and mesh are fixed per RK stage. New exact rational lemmas prove homogeneous lifting of `dU`, `dP`, `dM`, warp force `-3(P-M)/(2z)`, lower weak-Israel M SAT `2(1-v)(target-M)/dy`, and upper P SAT `-2(1+v)P/dy`, given the SAME spatial multiplier on fields, radial force and source. The separately new `KSW668F8SSPRK3RadialLiftNaturalityExact.agda` proves homogeneous scalar linear-source Shu-Osher SSPRK3 for **time-varying** stage coefficients `a0,a1,a2`. It does **not** prove the entire original coupled matrix intertwines without its original source, boundary and origin conditions, and gives **no stability/CFL theorem**.

**Local checks:** independently executed **1,232/1,232** exact rational radial/FV/stage-reconstruction checks plus **250/250** exact SSPRK3 stage-composition checks (1,482 total). Committed `scripts/test_ksw668_f8_augmented_origin_fv_intertwiner.py` and `scripts/test_ksw668_f8_ssprk3_radial_lift.py` cover these aspects. The exact first-shell origin coefficients are recomputed from the *same original* `FV.d7Minus, FV.d11Minus` and analytic shell volumes; no alternative FV scheme was introduced. Both modules imported by `KSW668F8SameObjectWeylAuthorityBoundary.agda` through original KSW/TOE graph. **Agda pinned kernel NOT RUN**, so rational source-written theorems await typechecking.

**Gate reassessment:**
- **G1:** Original radial-harmonic *discrete induced operator* with augmented origin trace now **closed at exact rational-algebra level** for radial rows. The missing full 3x3 tensor-Cartesian projector/induced-FV/gauge and original moving physical Weyl receiver identification remain **OPEN**. Unlike the XXXII naive d=3 radial FV counterexample, this new scheme is precisely the conjugate of the ORIGINAL effective-dimensional FV and carries V0 explicitly.
- **G2:** Original semidiscrete weak-Israel SAT **linear scaling** established algebraically; coupled moving boundary energy, source dependence and pointwise geometric defect remain OPEN.
- **G3:** Scalar time-varying SSPRK3 **reconstruction naturality** established algebraically; fully discrete weighted stability/CFL/outer closure still OPEN.
- **G4:** Moving warped-boundary high-Sobolev original source-to-both-electric-Weyl trace estimate OPEN.
- **G5:** Exact origin and interior reconstruction defects identified; uniform dr/dy/dt and receiver convergence/open-cone negative control remain OPEN.
- **G6:** Actual Einstein–matter source/retarded FIO/calibrated detector evidence OPEN.

**Next highest-alpha step:** use the *actual original* `(V0,U,P,M)` augmented radial state, the conserved finite-volume shell/Green form, and the moving SAT stage operator to prove a **coupled weighted semidiscrete radial/normal energy bound including the origin trace**, then a quantitative high-derivative receiver estimate. Do not substitute unrelated geometric metrics or a source-changing FV reinterpretation. Preserve original DASHI/Caldwell–Langlois/Thorne attribution and user-directed research distinction. No ESD edits, no Monster/369 physical equivalence, no graviton detection claim.


## Maximum-cut XXXVIII — actual normal_order=3 SBP2 moving weak-Israel boundary energy (2026-11-17)

**Original owner inspected:** `scripts/ksw668_f8_tt_multipole.py:stage()`. For `normal_order=3`, the normal derivative of both `P,M` is forward one-sided at lower y, backward one-sided at upper y, centered interior. The characteristic normal principal equations have coefficients `a=1+v`, `-b=v-1` where `b=1-v`. The lower M SAT is `+2b(target-M0)/dy`; upper P SAT is `-2a PN/dy`. The exact diagonal SBP2 quadrature is `H_y=dy diag(1/2,1,...,1,1/2)` (for at least two y nodes).

### G2: genuinely exact finite normal-energy boundary result

For the `normal-only` characteristic energy `E_char=1/2 Σ_i H_i(P_i²+M_i²)`, the original SBP2 derivative and both original SATs give precisely the following **boundary contribution** to its time derivative, for arbitrary rational `v,P0,M0,PN,MN,target`:
```
B = -a/2*(P0²+PN²)
    -b/2*(MN²+(M0-target)²)
    +b/2*target².
```
This is an exact sum-of-squares identity. If `-1<v<1`, then `a,b>0` and the first two terms dissipate, while the final term supplies the boundary source injection. The inequality follows from the square signs; it is **not an Agda order theorem**. No continuum or infinite-grid limit is assumed for this finite SBP2 algebra.

At the ORIGINAL `t=4/3` rational slice, `v=-3/5`, `target=P0/4-5S/4` with `S=amp*source`, an exact second square-completion gives
```
B = -(4/5)(M0-target)²
    -(3/20)(P0+5S/3)²
    +(5/3)S²
    -(1/5)PN² -(4/5)MN².
```
In particular **`B <= (5/3) S²`** at this slice. This cap uses the actual weak-Israel source coefficient, not a source-free or strongly enforced wall. The general real moving-wall `v(t)` source cap, once `v<0` and the exact Israel `target=((1+v)P0-2S)/(1-v)` is supplied, has the formal completed-square form
```
B = [v(1+v)/(1-v)]*(P0-S/v)²
    -(1-v)/2*(M0-target)² - S²/v
    -(1+v)/2*PN² -(1-v)/2*MN².
```
An Agda real/rational order proof with bounded v(t), nonzero denominators and normalization of source to the actual geometry is STILL OPEN. In particular the factor `-1/v` requires a lower bound for `|v|` over the simulation time range. The formula has been derived algebraically but is NOT a new Agda theorem.

The finite SBP2 face sum telescope and general boundary algebra are implemented in `KSW668F8MovingSBP2SATBoundaryEnergyExact.agda`, reusing the original moving Neumann/SBP owners. The slice source cap has separate exact rational proofs there.

### G3: actual bulk terms that prevent premature global energy closure

The original radial FV Green identity cancels the radial force against the radial gradient energy only when the **moving shift** is accounted for. Since `Udot=(P+M)/2+v(P-M)/2`, the residual per radial face is exactly
```
A_face * v * delta_r U * delta_r(P-M).
```
The original warp force `F_warp=-3(P-M)/(2z)` also has nonzero characteristic-power contribution in conventional `(P²+M²)/4` energy:
```
(P+M)/2 * F_warp = -(3/4) z^-1 (P²-M²).
```
Both are source-written Agda exact polynomial identities in the same module and **cannot be discarded**. The first suggests a mixed/shifted moving-energy symmetrizer; the second requires the actual `z^-3` bulk norm and its time/space-varying Jacobian, rather than freezing the warp factor. Additional original outer radial Dirichlet/normal closure and stagewise geometric coefficient changes require inclusion. Hence the present finite normal boundary SOS **does not close G3 or the joint radial-normal G2 stability**.

### Verification and provenance

Exact-Fraction regression `scripts/test_ksw668_f8_moving_sbp2_sat_energy.py` checks original one-sided/centered SBP2 operators with 2,3,4,6,12 normal nodes at arbitrary dy/v, lower/upper exact SATs, source square completion, radial shift and warp identities. **1,500/1,500 independent exact-rational checks PASS**. New module imported through `KSW668F8SameObjectWeylAuthorityBoundary.agda` into the original KSW/TOE graph. **Pinned Agda kernel NOT RUN; source-written proofs still require typechecking.**

**Updated gate priorities:** G2 original SBP2/SAT normal boundary source cap is **closed as finite algebra**, but full coupled moving radial/normal boundary energy still OPEN. G3 **next cut**: construct the time-dependent `z^-3` weighted radial+normal symmetrizer including the origin-augmented V0 state, shift, warp, SAT source and time-varying geometry; then prove a mesh-uniform semidiscrete bound before any SSPRK3 CFL acceptance. G4 higher Sobolev dual Weyl trace, G5 independent three-axis convergence and G6 physical matter/FIO/detector remain OPEN. Original sources, Caldwell–Langlois/Thorne and relevant SBP prior art retain attribution; no ESD edits, no unrelated physics identification or graviton detection.


### XXXVIII continued — ACTUAL z^-3 weighted SBP2 + source SAT composed identity

The earlier XXXVIII normal energy identity used the unweighted diagonal SBP2 norm. This is a correct discrete principal-boundary identity but **not** the full original AdS5 energy, whose spatial normal measure includes the changing original warp weight `w_i=(b+i*dy)^(-3)`. Directly deriving the weighted original endpoint/centered stencil yields, for every finite node list,
```
Σ_i H_i w_i x_i (D_y x)_i
 = [w_N x_N² -w_0 x_0²]/2
   + (1/2) Σ_{i=0}^{N-1}(w_i-w_(i+1)) x_i x_(i+1).
```
The last term is an exact **bulk weight commutator**; no assumption of constant w is permitted. Even with descending positive weights, it is sign-indefinite (two exact examples +1/2 and -1/2).

For the original P/M characteristic speeds `a=1+v`, `v-1`, define
```
C_P=(1/2)Σ_faces (w_i-w_(i+1)) P_i P_(i+1),
C_M=(1/2)Σ_faces (w_i-w_(i+1)) M_i M_(i+1).
```
The exact **warp-weighted normal principal+SAT** balance is
```
B_w = w0[-a/2 P0² -b/2(M0-target)²+b/2 target²]
      +wN[-a/2 PN² -b/2 MN²]
      +a C_P +(v-1) C_M,     b=1-v.
```
At original `v=-3/5`, `target=P0/4-5S/4`, this becomes
```
B_w = w0[-4(M0-target)²/5 -3(P0+5S/3)²/20 +5S²/3]
      +wN[-PN²/5 -4MN²/5]
      +(2/5) C_P -(8/5) C_M.
```
**This is the correct G2/G3 seam for the weighted NORMAL operator.** The signed source cap by itself has an interior weight-commutator remainder; controlling it requires an estimate on weight variation, original radial/normal energy, the moving z^-3 Jacobian/time derivative, and warp/shift power. No uniform all-grid SSPRK3 energy or both-Weyl estimate has been established.

New `DASHI/Physics/Gravity/KSW668F8WarpWeightedSBP2CommutatorExact.agda` contains the exact face formula, arbitrary finite-list telescope, signed negative control, composed full weighted SAT completed square and original t=4/3 source slice. It imports and reuses the prior XXXVIII boundary-energy owner, and is attached through the existing F8/KSW/TOE authority. Independent `scripts/test_ksw668_f8_warp_weighted_sbp2_commutator.py` verifies the actual rational warp weights for multiple normal-grid lengths and arbitrary original b,dy. **320/320 full-grid exact-Fraction checks and 300/300 additional weighted-source-composition checks passed locally**, plus sign controls. Pinned Agda kernel still not run.

**Immediate next mathematical priority G3:** establish a mesh-independent bound on `C_P,C_M` in terms of weighted bulk energy, including the first/last half-weights; explicitly account for `w_T` when b(T) moves and the original `-3(P-M)/(2z)` force and `v Δ_r U Δ_r(P-M)` transport. The current result is an exact signed ledger, not unconditional dissipation. G4–G6 remain unchanged OPEN. Source and mathematical attributions preserved.


## Maximum-cut XXXIX — true moving-weight/warp cancellation and mesh-independent normal-energy precursor (2026-11-17)

**Reuse and correction:** Inspected the original `scripts/ksw668_f8_tt_multipole.py:stage()`, the actual warp `-3(P-M)/(2z)`, the centered/endpoint `normal_order=3` SBP2, the existing XXXVIII `z^-3` commutator, and the moving brane `b(T)=1/t, v=b_T=-1/sqrt(1+t²)`. **Keep one energy normalization throughout:** `E_char=(1/2)sum_i H_i w_i(P_i²+M_i²)` with `w_i=(b+i*dy)^(-3)`. An earlier local warp-power formula `-3(P²-M²)/(4z)` was for a **quarter-normalized energy**. For THIS half-normalized energy used in XXXVIII, its actual power is **`-3(P²-M²)/(2z)`**; using the quarter coefficient in the coupled energy ledger would be an erroneous factor of two. The correction does not change the previous finite normal SBP boundary/SAT squares.

### Exact cancellation: geometry determines the symmetrizer
With `a=1+v, c=1-v`, the continuous-weight bulk-normal terms are
```
normal weight gradient:  +(3/(2z)) [a P²-c M²]
warp forcing power:    -(3/(2z)) [P²-M²]
moving weight d/dT:    -(3v/(2z)) [P²+M²]
SUM:                    0.
```
The cancellation is **exact for arbitrary rational P,M,v,1/z**, provided the original moving-geometry derivative `b_T=v` and the formal `w_T=-3v w/z` chain rule hold. The existing original slice `t=4/3` has `db/dt=-9/16`, `dT/dt=15/16`, `v=-3/5`, verifying `db/dt=v(dT/dt)` in exact rationals. The full all-t smooth calculus equality `b_T=v` is independently elementary from `T'(t)=sqrt(1+t²)/t²`, and is not a newly Agda-kernel-checked analytic derivative theorem.

### Exact original DISCRETE remaining defect

Define `C_X=(1/2)sum_faces (w_i-w_(i+1)) X_i X_(i+1)` and `J_X=dy sum_nodes nu_i w_i/z_i X_i²`, with endpoint SBP weights `nu_0=nu_N=1/2`, `nu_i=1` interior. The actual original weighted normal principal + original SAT + warp forcing + moving weight power satisfies the exact semidiscrete ledger
```
E_char' |_(normal+warp+moving weight)
 = B_source_diss
   + (1+v)*(C_P-(3/2)J_P)
   -(1-v)*(C_M-(3/2)J_M).
```
`B_source_diss` is the XXXVIII original weighted completed-square boundary expression. Hence **all smooth bulk warp terms cancel**, leaving only a precisely named discrete normal product-rule/quadrature defect. A finite face identity proves
```
(1/2)(w_i-w_(i+1)) X_i X_(i+1)
 =(1/4)(w_i-w_(i+1))(X_i²+X_(i+1)²)
  -(1/4)(w_i-w_(i+1))(X_(i+1)-X_i)².
```
This isolates the derivative-square term (sign depends on characteristic speed) and quadrature mismatch.

### New mesh-independent estimate (conditional; analytic/order proof not yet in Agda)

Let `beta=b(T)>0`, `h=dy`, and `0<h<=beta`. The actual solver enforces `dy<=.03`, `final_t<=20`, and `beta=1/t>=.05` throughout its original interval, so this geometric mesh condition holds. Exact rational polynomial certificate for `s=h/z_i in [0,1]`:
```
9(1+s)^3-(3+3s+s²)^2
 =s(9+12s+2s²+s²(1-s)) >= 0.
```
Consequently for the actual descending warp weights `w_i=z_i^-3`,
```
(w_i-w_(i+1))² beta² <= 9h² w_i w_(i+1).
```
By `2|ab|<=a²+b²`, summing edges against the SBP half-weight endpoints yields
```
|C_X| <= (3/beta) E_X,
E_X=(h/2)sum_i nu_i w_i X_i².
```
Also `0<=J_X<= (2/beta) E_X`. Thus for `-1<v<0`,
```
|(1+v)(C_P-3J_P/2)-(1-v)(C_M-3J_M/2)|
 <= (12/beta)(E_P+E_M).
```
This is an **actual mesh-independent semidiscrete estimate for the normal + warp subsystem**, but it does not control the retained original **radial FV force, moving radial shift, radial outer closure, source-to-trace higher derivatives or SSPRK3 amplification**. It is deliberately a conservative bound; the exact defect offers a possible sharper smooth-field/truncation route.

### General original Israel source cap, not restricted to t=4/3

For any rational `v`, let `a=1+v, c=1-v`, `S=amp*source`, and `target` obey the exact original source equation `c*target=a*P0-2S`. The new **division-free polynomial** identity in `KSW668F8MovingWarpEnergyCancellationDefectExact.agda` factors the general lower-wall source:
```
c*v*B_lower
 =a(v P0-S)²-c S²-(c² v/2)(M0-target)²
 +(v/2)(c target-a P0+2S)(c target+a P0-2S).
```
The last term vanishes for the original target. When `-1<v<0`, this is equivalent to the signed completed square
```
B_lower = a*v/c*(P0-S/v)²
          -c/2*(M0-target)² -S²/v
       <= -S²/v.
```
The weighted lower-wall source cap is therefore `w0*(-S²/v)`; with the original `v=-1/sqrt(1+t²)` and `w0=t³`, this is `t³ sqrt(1+t²) S²`. An Agda rational **order** proof of the inequality and an analytic all-t smooth brane-parameter proof are still OPEN, although the unconditional polynomial certificate is source-written.

Combining these ingredients gives the finite normal/warp **conditional** differential inequality
```
dE_char/dT |_(normal+warp) <= 12 E_char/beta + w0*(-S²/v)
```
for `-1<v<0,0<dy<=beta`, with the original source target, before adding radial forcing and stage stepping.

### New source/code acceptance

- New `DASHI/Physics/Gravity/KSW668F8MovingWarpEnergyCancellationDefectExact.agda`: exact original continuum-term cancellation, true half-energy normalization, discrete residual factorization, face product-rule defect, envelope polynomial, all-v source SOS polynomial, and rational `b_T=v` slice check. Reuses XXXVIII weighted SBP2/SAT owners and is imported through `KSW668F8SameObjectWeylAuthorityBoundary.agda` into the canonical KSW/TOE graph.
- `scripts/test_ksw668_f8_moving_warp_energy_defect.py`: **3,124/3,124** exact Fraction checks across 2,3,4,7,13 normal nodes, original `z=b+i dy`, true warp/time/source SAT, operator residual, mesh-independent commutator bound and face polynomial envelope.
- `scripts/test_ksw668_f8_moving_israel_source_cap.py`: **1,500/1,500** exact Fraction general-v source certificate and completed-square inequality checks.

**Pinned Agda kernel NOT RUN** (the model environment has no pinned Agda executable); arithmetic proof source and mathematical order bounds must not be conflated with kernel acceptance. Existing original source, DASHI and external Caldwell–Langlois/Thorne/SBP attributions retained. No ESD edits or spurious physical equivalence.

### Updated G1–G6 blockers

G1 original finite source, origin-augmented radial lift and restricted geometry-to-Weyl weld retained; full tensor-gauge discrete compatibility OPEN. **G2** all-v original moving-Israel normal-source cap locally closed algebraically, but full radial+normal energy OPEN. **G3** normal+warp **mesh-independent** semidiscrete energy precursor established under the solver's mesh/geometry domain; fully coupled moving-radial FV energy, SSPRK3 time-discrete CFL and outer closure OPEN. **G4** moving high-Sobolev both-Weyl trace OPEN. **G5** independent dr/dy/dt convergence and outside-cone control OPEN. **G6** Einstein-matter/retarded physical FIO/calibrated detector OPEN.

**Next max-cut:** include radial first/outer-cell face energy, original `U_T=(1+v)P/2+(1-v)M/2`, moving (v,\Delta_rU\,\Delta_r(P-M)) shift and radial+normal cross terms in a single weight norm. The origin-augmented V0 carrier and actual 3/7/11 shell weights must remain attached. Only then attempt an energy-driven SSPRK3 CFL and higher-Weyl estimates.

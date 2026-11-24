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


### XXXIX second high-alpha cut — normal-gradient constraint is SAT-driven, not bulk-generated

Reusing the SAME original `stage(U,P,M,...normal_order=3)` (not an assumed continuum wave system), define `W=(P-M)/2` and the discrete geometric compatibility defect `Q=W-D_y U`. The original stage equations are
```
Udot=(1+v)P/2 +(1-v)M/2,
Pdot=(1+v)D_y P + F +SAT_P,
Mdot=(v-1)D_y M + F +SAT_M,
F=L_r U-3(P-M)/(2z).
```
Because `v=v(T)` is independent of the normal grid coordinate and the exact **same** centered/endpoint SBP2 `D_y` is used for both characteristic derivatives, `D_y Udot=[(1+v)D_y P+(1-v)D_y M]/2`. The common bulk force `F` cancels from `(Pdot-Mdot)/2`. Therefore
```
Qdot=(SAT_P-SAT_M)/2,
interior: Qdot=0,
lower boundary: Qdot=-(1-v)(target-M_0)/dy,
upper boundary: Qdot=-(1+v)P_N/dy.
```
This is an **exact pointwise semidiscrete constraint propagation theorem** in original stage algebra. It implies that if `Q=0` initially on interior nodes and the same operator is used throughout the stage, the bulk evolution does not independently generate new `Q` there. It does **not** mean that the SAT boundaries enforce `Q=0`, and it is not a fully discrete nonlinear/time-dependent propagation or Weyl tensor gauge theorem. A nontrivial source can generate boundary constraint residuals which must be controlled by the coupled energy and trace estimate.

The XXXVIII original radial shift term admits the exact decomposition
```
v A_face Δ_r U Δ_r(P-M)
 =2v A_face Δ_r U D_y(Δ_r U)
  +2v A_face Δ_r U Δ_r Q.
```
Here `D_y Δ_r U=Δ_r D_y U` holds for the tensor-product first differences at each four-corner cell (a new rational theorem). The first contribution is an **SBP2-normal weighted radial-gradient face flux/commutator**, not an uncontrolled second radial derivative; the second is precisely the SAT-driven normal-gradient constraint error. This offers a stronger coupled symmetrizer route than a naive inverse-estimate of `Δ_r(P-M)`, which could introduce a divergent `1/dr` constant.

**Implementation:** new `KSW668F8NormalGradientConstraintSATPropagationExact.agda` supplies all three original stage identities, interior and lower/upper SAT production, tensor-product four-corner commutation, and exact shift decomposition; imported by the existing `KSW668F8SameObjectWeylAuthorityBoundary.agda` in the KSW/TOE graph. `scripts/test_ksw668_f8_normal_gradient_constraint.py` validates the native SBP2 full-grid algebra, actual SAT locations, and signed shift decomposition in **2,500/2,500** independent Fraction checks. This arithmetic result is **source-written Agda, pinned Agda kernel NOT RUN**.

**Next highest-alpha coupled G3:** assemble `E_char +E_radial` with the original effective-d shell volumes and `z^-3` normal weight; apply the exact `Q` identity to the radial-shift term and the XXXVIII/XXXIX weighted normal SBP2 results to the derivative of every radial-face gradient. Prove nonpositive/controlled radial-origin and outer-face terms with the unchanged native Dirichlet closure. Derive a trace estimate for SAT-driven `Q` at both normal endpoints without an inverse power of `dr`, then a uniform coupled semidiscrete Gronwall bound. A fully time-discrete SSPRK3 CFL, higher-Sobolev dual-Weyl trace and independent dr/dy/dt convergence remain open; no physical G6 detector witness introduced.


## Maximum-cut XL (2026-11-18) — YM S³ vs S3/C3 cross-pollination, positive normal donor and original radial obstruction

**Source readback:** `DASHI/Physics/YangMills/YMClayRationalS3DegreeFifteenInvariantCertificateExact.agda` (independent YM branch; 11 degree-15 quaternion-sphere invariant moment certificates); default-branch `DASHI/Foundations/TernaryPermutationS3LawsExact.agda`, `DASHI/Foundations/PolynomialC3S3OrbitSamplingProjectionExact.agda`, `scripts/check_polynomial_c3_s3_reynolds_character_exact.py` and `Docs/research/zipf_ternary27_s3_c3_orbit_heaps_crosspollination_20261028.md`; plus original F8 `scripts/ksw668_f8_tt_multipole.py`, d3/d7/d11 radial FV and XXXIX normal energy. **Do not identify** SU2 unit quaternion S³, finite permutation group S3, C3 cyclic subgroup or physical F8 angular S²/S¹.

**Real positive reuse (G2/G3):** the original moving normal/warp/SAT block is mode-independent as a formula once radial source and source amplitude are supplied. Reuse one universal generic `map3 f` theorem for all six source-owned S3 mode relabelings, and a C3 rational Reynolds projector `(x0,x2,x4)↦(mean,mean,mean)`, idempotent. Apply XXXIX single-mode `|R_ell,j|<=12 E_ell,j/b` with each mode's OWN positive radial FV shell volume `W_(3+2ell,j)`. Sum to obtain
```
|Σ_(ell,j) W_(3+2ell,j) R_(ell,j)|
 <=12/b Σ_(ell,j) W_(3+2ell,j) E_(ell,j),
ell=0,2,4, 0<dy<=b(T), -1<v<0.
```
This extends the normal+warp bound to the original **entire three-mode, all-radial-node direct sum** while deliberately EXCLUDING radial forcing, moving radial shift and normal-gradient SAT constraint coupling. Agda source-written algebraic weighted aggregation/positive shell mass is NOT an Agda kernel-checked inequality. There is proof-schema compression (three otherwise duplicated normal-block proofs → one generic mode-index proof), not a reduction of the actual simulation's three radial operations.

**Exact symmetry BREAKING (mandatory acceptance firewall):** the original radial origin stencil in grid units is `diag(6,14,22)`. Its C3-Reynolds invariant mean coefficient is 14, and its irreducible deviations are `diag(-8,0,8)`. Under mode-label cycle R,
```
[L_origin,R](x0,x2,x4)=(-8 x2,-8 x4,16 x0) !=0
mean(L_origin x)=14 mean(x)+(8/3)(x4-x0).
```
The true first-shell mass triple at h=1 is `(1/24,1/896,1/22528)`: rotating the physical F8 fields **without** the dimension-dependent masses does not preserve their weighted energy. The actual first interior radial coefficients also differ: (27/13,3/13), (5103/1093,7/1093), (649539/88573,11/88573). Hence C3/S3 is a mode-*relabeling* symmetry of the COMMON normal formula, not a symmetry of the FULL physical evolution; source physics must retain distinct effective dimensions and original FV coefficients.

**YM S³ relevance:** signed-permutation orbit averaging can compress a genuinely invariant polynomial proof (as in YM degree15's 11 invariants); it cannot establish pointwise F8 quadratic-form positivity from its average. The rational unit S³ polynomial `q0²-q1²` already has both +1/-1 witnesses. A later energy SOS/invariant cut may use YM's *certificate pattern* only after verifying a true invariance of the native weighted state. Do NOT import YM's quaternion measure as the F8 angular measure.

**New committed source:** `KSW668F8C3S3ModeReynoldsRadialObstructionExact.agda`, `KSW668F8ThreeModeWeightedNormalEnergyReynoldsExact.agda`, `scripts/test_ksw668_f8_c3_s3_mode_reynolds.py`, canonical F8 authority imports, and [full source crosswalk](KSW668F8C3S3YMReynoldsCrosswalkMaxCutXL20261118.md). Independent local exact-rational regression **4,556/4,556 PASS**; pinned Agda kernel **NOT RUN**.

**Next concrete G3 theorem:** assemble original **radial-gradient + characteristic** full time-dependent weighted energy, not merely the normal direct sum. Use source XXXIX normal-gradient constraint `Q=(P-M)/2-D_yU` to rewrite moving radial shift as normal SBP2 face + Q defect; include exact origin V0, radial outer Dirichlet, all-mode unequal shell volumes and original lower weak-Israel source cap. Prove the Q boundary trace bound with no growing inverse mesh constants; then uniform semidiscrete Gronwall, then SSPRK3 CFL, then G4/G5 receiver derivatives and both-Weyl convergence. G1 physical tensor-gauge evolution, full G2/G3, G4, G5 and G6 remain OPEN. Keep original DASHI/YM/C3 authorship, no ESD edits, no unrelated physical group identification.


## XLI reconciliation — native discrete-to-wave / geometry owners (2026-11-20)

Recovered #1520 original coupled symmetrizer owner unchanged (commit 671517442bf7); imported into F8 authority in 55feb68bd01e. Do not reopen the radial-shift trace as prerequisite to basic energy: a=(1+v)/2,c=(1-v)/2, Udot=aP+cM gives exact radial Green cancellation. Mode4 weighted split has the donor semidiscrete homogeneous E'<=5E and characteristic source lift; mode3 retains its own normal derivative and has additional a(1+v)(CP-3JP/2)+c(v-1)(CM-3JM/2), bounded by 12E/b under the earlier mesh condition. Thus mode3 homogeneous E'<=(5+12/b)E by the donor algebra and existing commutator bound; combined executable regression still pending. Do not apply the half-energy source-only cap to this different symmetrizer: use donor lift and volume source budget. Mode4 receiver convergence previously failed.

Source-read native owners: Docs/WaveAlgorithmFormalism.md, WaveAlgorithmLift, ShiftDiscreteWaveEnergy, ShiftSpatialLaplacian, ShiftWaveRefinementSeam, Core/SymmetryResolvedFibreExact, Mathematics/LinearAlgebra/FiniteHodgeEnergyExact and Physics/Closure/FiniteHodgePhysicsCrossPollinationExact. Reuse their separation of norm, evolution, observation and refinement; integer-pair Euler and reflected three-point Laplacian are not F8 dynamics. Hodge finite adjoint pattern: native radial incidence B, positive shell mass W and face conductance A give -L=W^-1 B^T A B with outer fixed-zero node retained in B. This is the required native metric adjoint instantiation, not a new continuum Hodge assertion. ReopenableObserver is the correct interface for ell>0 physical nodal reconstruction with retained V0; full instance with nonzero scaling inverse and actual grid still pending. Preserve unequal mode masses; no C3 physical radial symmetry.

Next: exact assembled mode3 energy/source-lift audit on actual stage; then moving metric SSPRK3 matrix M_n^T H_(n+1) M_n <= (1+C dt) H_n using #1519 matrix-energy donor, with actual frozen-stage geometry chronology checked before claiming nonautonomous order. Higher Sobolev and full tensor observation/refinement defects remain open. #1512 original FIO geometric preflight retained; #1444 finite Hodge/covariance donor not a physical Weyl proof. Agda kernel NOT RUN; no new numerical convergence or physical claim.


## Maximum-cut XLII/XLIII — prior-art reconciliation and exact joint SAT discriminator (2026-11-20)

Reuse before construction: #1520 at ad109a01d80855bd20eca1efaa23d2a38343afad already supplies original mode-3 coupled semidiscrete E' <= (5+16t)E (dy<=b/4), sourced lift, interior physical constraint, all-order radial Sobolev hierarchy; mode-4 weighted split has separate constraint defect. XXXII already owns radial FV Green telescope, native shell weights, origin/outer Dirichlet and quadratic/quartic consistency; XXXVII owns augmented-origin induced FV and SSPRK3 naturality. Do not duplicate these. Original active radial matrix excludes fixed final node, as implemented by scripts/ksw668_f8_c3_weighted_operator_no_go.py. A1-A6 existing at construction level; arbitrary-N formal assembly, fresh full donor replay and canonical integration remain pending. Local SymPy is working verification per user instruction, not pinned Agda kernel acceptance.

### XLIII joint SAT discriminator

Reuse XXXIX Q=(P-M)/2-D_y U, Q_T=(SAT_P-SAT_M)/2 and #1520 XI left-null obstruction to U_T-only repair. With a=1+v,c=1-v, fixed U_T, equal characteristic SAT increments preserve Q. In the coupled characteristic energy, write k for the common increment multiplied by endpoint quadrature mass (positive warp weight suppressed). Lower flux F=(c²M²-a²P²)/4 factors as (cM-aP)(aP+cM)/4. Choosing k=(aP-cM)/2-beta(aP+cM), beta>0, yields F+(aP+cM)k/2=-beta(aP+cM)²/2; upper flux has opposite sign and k=-(aP-cM)/2-beta(aP+cM). This is a boundary energy/constraint algebra construction, NOT an accepted physical SAT replacement: on P=c,M=-a its dissipative square vanishes but original Israel residual aP-cM-2G=2ac-2G can be nonzero. Original source condition and outer incoming condition must remain independently controlled; no claim of consistent boundary PDE or convergence.

Local SymPy script scripts/check_f8_xliii_joint_sat_sympy.py: 49/49 assertions PASS (44 finite-grid SBP/nullspace/constraint checks n=3..13, of which 11 are elementary equal-increment checks, plus five symbolic boundary identities). No full donor replay, Agda kernel or physical convergence run in this round. Preserve original source ownership and prior negative controls.

### Updated priority and strict gates

1. G2: reconcile #1520 full coupled energy/source lift with canonical XXXII/XXXVII active domain and existing imports; replay original tests, avoid redundant construction.
2. G3: actual coupled moving-metric SSPRK3 CFL; joint SAT repair must preserve Q, original Israel/outer data and energy simultaneously, or provide quantitative residual bound. Common SAT candidate above is not sufficient.
3. G1/G5: use existing full tensor atlas and source projection; correct intrinsic E4 receiver to full spatial Laplacian (not axial second derivative alone); isolate source-cell, radial dispersion and receiver differentiation, then independent dr/dy/dt refinement and fine-box parity.
4. G4: mesh-uniform source and normal/time/radial high-Sobolev dual-Weyl trace, not merely radial powers.
5. G6: independent original t2 FIO theorem acceptance, same-action matter/backreaction and calibrated detector. All full-scope G1-G6 and pinned kernel remain OPEN. Prior three-grid receiver failed; no physical signal promotion.


## Maximum-cut XLIV — KKT cross-programme boundary projection (2026-11-20)

User prompted comparison with P/NP and 3-SAT. Distinguish Boolean satisfiability from numerical simultaneous approximation terms (SBP-SAT). The actual repair is continuous constrained quadratic algebra, not a 3-SAT instance. Reused proof pattern from BalabanKKTGramPseudoinversePositiveExact (Penrose/finite Gram) and FiniteRationalQuadraticDominationExact; Karp21SignedFrustrationBidiExact is relevant only to a future finite stencil-selection encoding, not a physical identification. No P=NP claim.

Original mode-3 Q=(P-M)/2-D_y U, wall aP0-cM0=2G, far P_N=0 define C(T)X=g(T). On the active positive-energy domain H, define J=H^-1 C^T (C H^-1 C^T)^-1 and Pi=I-JC. For full row rank C, C J=I; Pi is H-selfadjoint idempotent and Pi^T H Pi<=H. The projected RHS Xdot=Pi F+J(gdot-Cdot X) satisfies derivative(CX-g)=0. For homogeneous constrained X, correction has zero instantaneous H-work because X^T H J=0. Thus any original homogeneous semidiscrete bound on the same constrained domain transfers to the corrected RHS. Affine source work requires independent control.

scripts/check_f8_xliv_projection.py committed at 86f4149392f7e1a397677a2bfa97fc519f8b32c0: 114/114 grouped exact SymPy checks locally passed at t=4/3, v=-3/5,b=3/4, dy=1/16, n=3..8, radial spectral parameters lambda=1,22. Tests cover rank, right inverse, kernel projection, idempotence, H adjoint, Pythagorean decomposition, moving tangent and homogeneous zero-work, affine source. One further geometry assertion checked. These are finite normal slices with positive radial spectral parameters, NOT full original radial solver execution. Projection is a candidate nonlocal modified evolution, not the original weak SAT scheme or proven consistent continuum boundary enforcement. No Agda or physical convergence claim.

Next: arbitrary-grid rank and uniform Schur/trace source-lift bounds on native radial spectrum; quantify correction consistency/locality and compare to donor weak-SAT residual; incorporate time-dependent projector into actual SSPRK3 stage chronology with endpoint metric and source work; independently refine corrected full-Laplacian E4 and E5. All full G1-G6 remain open. SymPy is the working exact arithmetic verification method.


## Maximum-cut XLV — boundary-only Schur lift bound and nonlocality (2026-11-20)

Reuse XLIV KKT energy projection and Bałaban Gram positivity pattern; no new Booleans or physical identification. On original active normal/radial spectral carrier H=diag(lambda W,aW/2,cW/2), W_j=H_SBP,j z_j^-3, a=1+v,c=1-v, let E inject two boundary residuals into C=(Q,Israel,far). An explicit endpoint-supported right lift L has U=0, P0=M0=r0/(2v), PN=MN=rN, other entries zero. Thus C L=E exactly for v nonzero. This also proves full row rank for C: arbitrary Q can first be realized by P=Q,M=-Q,U=0, then repair its two boundary entries with L. J E is the H-minimum-norm lift; L^T H L-(JE)^T H(JE)=(L-JE)^T H(L-JE) PSD. Hence ||JE r||_H² <= h r0²/(8 b³ v²)+h rN²/(2 zN³), independent of lambda>0 and normal node count. On fixed finite original geometry interval this is uniform; radial spectral summation extends the algebra to native positive radial stiffness with weights. Not a high-Sobolev bound.

Moving C_T X has only wall component v_T(P0+M0). Weighted Cauchy-Schwarz gives |P0+M0|² <= (4b³/h)(1/a+1/c)||X||_H²; cancellation with lift bound yields ||J C_T X||_H² <= [v_T²/(2v²)](1/a+1/c)||X||_H². Original v=-1/sqrt(1+t²), v_T=t³/(1+t²)² gives coefficient t⁴/(1+t²)²<1. Analytic derivation; local matrix tests exercise constituent identities, not arbitrary moving-time integrations.

scripts/check_f8_xlv_schur.py committed f7ba7177f411de63812477d6d7c3231ac0af67ff; locally executed 104/104 exact SymPy assertions for n=3,4,5,8, h=1/16,1/32, lambda=1,22, original t=4/3. All 16 combinations show nonzero remote U_N response to lower-only KKT lift: discrete nonlocality, NOT proof of continuum acausality. Do not replace original hyperbolic solver on the strength of projection energy alone. Endpoint-local lift is feasible, but arbitrary use is not guaranteed energy-neutral; joint local energy-consistent boundary repair remains OPEN. No full native solver, Agda kernel, SSPRK3 or physical refinement executed this round.

Next priority: quantify local repair relative to original weak SAT and continuum boundary consistency; derive affine source work separately; retain global projection as certificate/comparator rather than causal propagation engine unless its remote effects are controlled. Then coupled moving-metric SSPRK3 CFL and corrected dual-Weyl independent refinement. All full G1-G6 remain open.


## Maximum-cut XLVI — reuse original affine source lift, preserve physical Q (2026-11-20)

Recovered actual source owners scripts/ksw668_f8_full_coupled_source_lift.py (mode 4), scripts/ksw668_f8_characteristic_constraint_maxcut.py (mode 3), Docs/physics/KSW668F8PhysicalConstraintRadialSobolevMaxCut20261115.md (section C), and DASHI/Mathematics/LinearAlgebra/AffineSpectralIndependenceQuadraticExact.agda (Bansal–Jiang quadratic-domination interface, not a solved gravitational SDP). Original nonhomogeneous mode-3 energy estimate already exists: Etilde' <= (6+16t) Etilde + ||F||_E²/2, dy<=b/4. Do not reopen this generic affine estimate as greenfield. The existing M-only lift homogenizes weak Israel but has Q(Lambda)=G chi/(1-v), not zero.

New candidate compact lift on same mode-3 equations: Lambda_U=0, Lambda_P=Lambda_M=L=(G/v)chi(y), chi(0)=1, chi(y_N)=0, v nonzero. Then Q(Lambda)=0, (1+v)L-(1-v)L=2G at wall, far P=0. On substituting X=Y+Lambda, homogeneous weak SAT and affine forcing F=(L,(1+v)D_y L-L_T,(v-1)D_y L-L_T). Radial force of Lambda_U zero; warp P-M cancels. Q(F)=0 for any common fixed D_y. Thus affine shift transports physical constraint exactly and is compactly supportable, without global KKT projection. Original homogeneous weak-SAT endpoint defect remains unchanged.

Fixed physical cutoff, bounded chi and derivative, and finite time interval with |v| bounded below supply a uniform normal forcing norm conditional on radial weighted G, G_T and first radial energy norm of G. This follows directly by triangle/Cauchy-Schwarz and native radial Green form; no high-order source proof implied. Do not confuse this with endpoint-only lift (whose derivative may scale as inverse h). Use original energy normalization from donor (a=(1+v)/2,c=(1-v)/2 in characteristic terms, full radial stiffness term); XLIV-XLV spectral surrogate metric used a different radial relative normalization and is not independently certified as donor energy.

scripts/check_f8_xlvi_affine.py at 3c81f4f60734d36cff7f038bcca1d99c47e2adf1: actually executed identical local SymPy source, 24/24 assertions PASS, n=3,5,8,13 on unit interval polynomial chi=(1-y)^4, t=4/3, rational sources. Not full original Numba stage replay or original compact TT source execution. Next: integrate same donor compact profile and actual radial source, measure parity against original stage, derive quantitative endpoint constraint residual bound or local energy-compatible weak SAT; coupled moving SSPRK3 and full Weyl convergence remain open. No Agda kernel claim.


## Maximum-cut XLVII — compact TT and dual-Weyl same-object audit (2026-11-20)

Existing compact TT producer scripts/ksw668_f8_fv_source_flux.py and original CartesianTTToOriginalRadialSourceJetsExact, OriginalTTSourcePrimitiveJetExact, angular atlas and conservative shell transfer already own source construction. Existing KSW668F8DualElectricWeylReadoutAlgebraExact owns legacy axial E4 and E5 arithmetic, and KSW668F8SameObjectWeylAuthorityBoundary imports these alongside geometry and stability owners. No new source generator needed.

Actual solver scripts/ksw668_f8_tt_multipole.py at ba8bd202 computed both derivxx and lapieces but E4 and tangent E4 consumed derivxx. For full spatial TT on flat conformal FRW, linear R_y0y0=-H_yy,etaeta/2 and Ric_yy=(H_yy,etaeta-Delta3 H_yy)/2 give E4=-(H_yy,etaeta+Delta3 H_yy)/(4t²). Existing E5 SMS formula unchanged (its separate source-free identification assumptions still apply). Corrected cancellation E5-2E4=(Delta3 H-H_eta)/t². Legacy axial cancellation remains valid only for its input formula. Commit e74a0c8fbd45e1eb3b2a74a9af0c45fb4c061d2d switches both intrinsic readouts to existing lapieces and preserves explicit legacy axial diagnostics at near and far receivers. No stage/source change.

Local SymPy executed 11 assertion checks: TT polynomial tensors, exact linear curvature arithmetic, corrected cancellation, axial discrepancy, three native multipole Laplacian identities. Negative control diag(-z²,z²,0) is TT with Hyy,xx=0 and Delta3 Hyy=2. This is general TT counterexample, not a claim this polynomial is the compact emitter. Actual edited solver not executed here, downstream legacy diagnostic consumers and Agda arithmetic owner not yet migrated. Preserve prior numerical receipts as legacy, do not relabel as corrected convergence. Next: audit downstream per-mode/readout consumers, run original source/solver with corrected E4, weld XLVI affine lift to actual mode3 source, and independently refine dr/dy/dT. G1 full geometric identification, G2 global boundary consistency, G3 CFL, G4 regularity, G5 convergence and G6 physical gates remain open.


## Maximum-cut XLVIII — per-channel full-spatial Weyl receiver integration (2026-11-20)

Default-branch solver blob 323954f2094da93a0d53acc4e831510f69faed52 already owns per-mode finite-difference/tangent temporal diagnostics, signed channel attribution and mode sum guards; current #1527 solver blob ab036497b281e361ce2e533b67453e03eb63f47c lacks that block. Default-branch consumers scripts/ksw668_f8_ternary_channel_drift.py, scripts/ksw668_f8_threegrid_signed_failclosed.py and scripts/test_ksw668_f8_ternary_receiver_weyl.py returned 404 on starting head 5a3f8a7a939f8ec3c4ca6c1d0bb567eb8599422f. Port ONLY the existing receiver diagnostic block and output keys, without replacing propagation, clock, radial/source or normal operators. Both per-mode intrinsic E4 routes now use lapieces, matching XLVII aggregate correction. Keep explicit axial legacy fields, including far receiver; add full-spatial operator provenance and second-temporal-derivative cancellation diagnostic. E5 unchanged. Existing mode-sum and temporal discrepancy guards retained.

Local scripts/check_f8_xlviii_modes.py: 22/22 exact SymPy assertions actually executed (both temporal readouts, all three channel cancellation and axial-delta identities, aggregate sums, per-channel temporal differences). This is symbolic receiver algebra, not an executed solver or convergence receipt. Direct local git ls-remote failed DNS; branch files retrieved via GitHub connector. No full solver replay or downstream integration test run. No Agda kernel claim. Prior results remain legacy; default-branch consumer port/replay, actual compact TT affine source integration, independent dr/dy/dT convergence and coupled CFL remain OPEN. Never mix legacy and corrected readouts in a refinement comparison. Code, test and this roadmap committed together.


## Maximum-cut XLIX — corrected refinement consumer provenance (2026-11-20)

Port default-branch existing signed channel and nine-grid factorial consumers and two regression owners, retaining their original parameters. Corrected receipt names are distinct (XLIX_corrected), and every new comparison must carry intrinsic_4D_weyl_spatial_operator=full_reconstructed_Delta3. Reject missing/legacy provenance, malformed/nonfinite channels and inconsistent sums at BOTH grids. Historical verify() remains explicitly legacy, not a corrected acceptance check; historical artifact presence not established on branch. Actual solver regression includes original per-mode legacy-to-corrected spatial difference and provenance checks. All physical acceptance flags remain false. No solver or source changes this cut.

Local Python execution: 8/8 synthetic guard tests passed against a locally extracted equivalent inspect/guard implementation (not byte-identical full committed consumer). Direct git ls-remote failed DNS again; NumPy, SciPy, SymPy 1.14 and Numba 0.65.1 import locally. Full actual solver and existing donor test execution not performed. Next run original nine named configurations with corrected provenance; compare time-halving and factorial signed per-channel changes, keep legacy data immutable. Integrate XLVI compact affine lift and bound endpoint residual, coupled SSPRK3 and G1-G6 remain open.


## Maximum-cut L — lossless corrected replay receipt (2026-11-20)

XLIX already landed at b566eb7; do not duplicate consumer ports. The corrected replay exporter still discarded most of the actual solver receipt, including near/far legacy axial fields, full spatial derivative components, both aggregate temporal routes, source and boundary geometry. Commit 93683c67f24af00683c89566dc6c8922ca2ede50 preserves the complete solver dictionary, validates the previously required keys, records requested mesh separately from realized step sizes, and adds receiver_receipt_schema=XLIX-full-spatial-v2. Existing corrected provenance guard and fail-closed physical acceptance remain unchanged. No solver/source/clock change and no historical receipt promotion. This is a source-level integration change; no new local numerical replay or regression receipt obtained this round. Actual nine-grid execution, checkpoint integration for native SSPRK3, affine source lift, independent convergence and G1-G6 remain open. Continue geometry-first; timeout must trigger bounded checkpointed execution rather than a mathematical failure claim.

### L follow-up — compilation and legacy-key regression (2026-11-20)

Concurrent lossless receipt changes at bc2e015e09a2f69eb3f80b39db72cb445a069d8d retained. Reinspection of solver blob 6f75288d6fdb1c1cb2b40096fd4bd5e78aa18238 confirms mode_E4_legacy and E4_legacy are distinct keys (likewise tangent); initial suspected duplicate was a misreading. Do not attach detached erroneous patch 9d599a1570292e5babafed46923486854c00507e. Add compile/AST regression against actual solver preserving all four keys. No solver modification. Direct git ls-remote locally failed DNS; actual solver compile regression and full numerical replay not executed in this turn. Temporal-pair and factorial gates remain open.


## Maximum-cut LI — native SSPRK3 resumable execution (2026-11-20)

Starting head 4b610016 already owns receiver compilation regression; retained. Native checkpoint helper f8f7d839, actual propagation integration 1ec26c31, nine-grid CLI wiring d40a2583. Preserve U/P/M at complete SSPRK3 step boundaries, exact next step cursor, four terminal wall/history arrays (including stage-derived derivatives), original realized mesh/time/source configuration, source/coefficient array hashes and solver/helper/source-file fingerprints. Atomic temp-file/fsync/replace; single writer. Original extra endpoint step for centered temporal receiver retained. CLI example: timeout 90s python -u scripts/ksw668_f8_threegrid_signed_failclosed.py --run-grid coarse --checkpoint .local-f8/coarse.npz --budget 75 --checkpoint-every 8 ; repeat on cooperative exit 75 or external timeout, until completed receipt. Internal deadline starts after setup and is checked at completed steps; allow headroom for compilation and I/O. Do not combine different grid labels into one checkpoint. No change to original stage, enforcement, source, radial or receiver formulas. Physical acceptance stays false. Source-level implementation committed, not locally executed: git ls-remote failed DNS, actual native donor files absent in local runtime. Need byte-exact local source recovery, full uninterrupted/resumed parity including split immediately before terminal-history captures, mismatch negative controls, then nine actual corrected executions and signed factorial analysis. Checkpoint implementation present; integrity execution OPEN, not PASS. XLVI affine lift, coupled CFL, independent convergence and G1-G6 remain open. No Agda or physical promotion.

### LI follow-up — exact moving affine SSPRK3 translation (2026-11-20)

Preserve concurrent checkpoint integration at 7de095a1ff7db85deae3d5eb09ebab1f82d03089. Connector-only repository access; no CI or direct checkout. Literal mode-3 stage and Shu-Osher time loop inspected in pre-checkpoint solver blob 6f75288d6fdb1c1cb2b40096fd4bd5e78aa18238. New scripts/check_f8_li_affine_stage.py executed locally: 17/17 exact SymPy assertions PASS (three normal-grid sizes, literal common force and SAT algebra on XLVI lift, polynomial time shift quadrature, three exact affine stage identities). The source profile is a polynomial test, not actual compact radial source integration or full numerical propagation. Time-dependent continuous affine forcing alone does not give exact RK conjugacy: on X'=0, Lambda=T^5, reconstructed defect = -k^5/24. Exact translated stages with original sourceful F evaluated on X=Y+Lambda: Y1=Y0+kF0+L0-L1; Y2=3Y0/4+(Y1+kF1)/4+3L0/4+L1/4-Lh; Ynext=Y0/3+2(Y2+kFh)/3+L0/3+2Lh/3-L1. Outer radial enforcement commutes if lift vanishes there. This is algebraic stage equivalence, not stability or continuum convergence. No production solver change. Next integrate exact translation into checkpointed original compact TT stage replay, compare numerical parity and execute original temporal pair/factorial; G1-G6 remain open.

## Maximum-cut LII — opt-in physical-state affine stage integration (2026-11-20)

Retain native checkpointed solver at 3ccfec7d487fa04d88054726f448594185c97e93. Add affine_mode3_stage, selected by affine_stage=False default. During nonzero source evaluate original homogeneous mode-3 stage on (U,P-L,M-L), L=(amp/v)src chi, chi=max(1-y/.12,0)^4, zero at far and outer radial nodes. Add (L,(1+v)D L,(v-1)D L) to homogeneous derivative. This reconstructs the physical stage derivative, so existing physical-state SSPRK3 updates implement LI exact stage conjugacy without accumulating translated coordinates or independently approximating Lambda_T. Checkpoint config includes affine_stage; solver-file fingerprint already covers inline implementation. CLI --affine-stage uses distinct receipt suffix; default untouched. Fixed-width polynomial cutoff chosen C3, not claimed high-Sobolev smooth. Local SymPy 5/5 and numerical component comparisons 27/27 (max absolute 1.71e-13) actually executed against independent vectorized mode-3 transcription using common surrogate radial force, random radial source, not native Numba stage/compact TT. Native test scripts/test_f8_lii_native_affine.py added (not executed here), requiring actual compact TT cell producer and literal stage. No full solver execution, checkpoint parity, energy/CFL or convergence claim. Next execute native test, uninterrupted vs resumed affine/native physical states, then original nine meshes. No CI.

## Maximum-cut LIII — actual compact TT stage and small-box pulse parity (2026-11-20)

Starting head 1d1410c185ea23fedf6a506c388aa8b4bf6d08be, solver blob 26f089b2aea202a82f19db7faa6c0e3eaa4554c5. Connector-only retrieval, no CI. Local source producer reconstructed and git hash-object confirmed exact blob dec4e79e3a4899952a5deceb786324bc0745982c. Literal stage/enforce/affine wrapper extracted into local module, compiled by Numba 0.65.1; not full byte-identical solver module. Original LII fixture executed with 18 configurations (ny=8,17,31; v=-.7,-.6,-.09; amp=0,.7), 54/54 derivative component comparisons PASS at atol 1e-8 rtol 1e-11; maximum absolute 1.1641532182693481e-10. Source moments 0,0,2.5761698809461424 versus independent quadrature 2.5761698809461127. Small-box 17x17 radial/normal, dr=.008 dy=.02 dt=.0005, original moving clock and .065 pulse, 160/160 full physical-state SSPRK3 step comparisons PASS at atol 1e-9 rtol 1e-10, max absolute 2.4556356947869062e-11, max state 6129.12204428115. Local extracted functions and transcribed time loop, not native propagate() or full receiver run. New reproducible regression scripts/check_f8_liii_pulse_parity.py imports actual owners; committed import variant not replayed. No production changes. Checkpoint resume parity, nine-grid full receiver, stability, high regularity and G1-G6 remain OPEN. Small box intentionally not causal receiver geometry.

## Maximum-cut LIV — compact TT checkpoint roundtrip and terminal history parity (2026-11-20)

Starting head 6eb7897694a1850db4ed12b1497e6d16aefea4db. Local checkpoint helper and compact source verified by git hash-object against blobs 4e319596d9064e7c9238b4a6570401e94df8a521 and dec4e79e3a4899952a5deceb786324bc0745982c. Numba 0.65.1, NumPy 2.3.5, SymPy 1.14.0. Actual native checkpoint helper executed with literal extracted stage functions, original compact source and small-box transcribed RK harness. nt=160 plus original extra endpoint step. Six save/reload schedules per native/affine route: (1), (65,130), (159), (160), (161), (1,65,130,159,160,161). 108/108 array comparisons bitwise identical (U/P/M and six wall/tangent arrays); cross-route identity mismatch rejected. Cursor checked after each load. This is in-process serialization/restoration, not process interruption or actual propagate() resume; the loop continues with restored arrays but uses its loop index, so production cursor-driven restart and full receiver remain OPEN. Local solver fingerprint is extracted module, not full production file. New regression scripts/check_f8_liv_checkpoint_parity.py reproduces harness with actual imports; committed import variant not executed here. No solver change, no CI or direct checkout. Next full native propagate checkpoint/restart and original refinement, stability and G1-G6 remain open.


## Maximum-cut LV — full original coarse receiver and resume acceptance (2026-11-20)

Standing user instruction: use GitHub connector for repository source and commits, local SymPy for exact maths and local NumPy/Numba for numerical execution. No GitHub CI dependency, and no direct checkout prerequisite. Reconstruct exact source from connector and check git blob hashes; use bounded checkpoint chunks for long jobs. Retain concurrent LIV small-box regression. Actual complete production solver (not extracted stage or substitute) reconstructed locally and verified blob 26f089b2aea202a82f19db7faa6c0e3eaa4554c5, helper 4e319596d9064e7c9238b4a6570401e94df8a521, compact source dec4e79e3a4899952a5deceb786324bc0745982c. Local SymPy 1.14.0, Numba 0.65.1. No CI calls. New regression scripts/check_f8_lv_full_checkpoint_parity.py at c37998078f9948ac87cb13be91824441f616f98d, executed local blob 1e5d683fc78bc05a599d7c89f14225ba822fc9bf matches commit readback; local file had earlier name before parallel LIV conflict, same bytes.

Exact SymPy: hold spatial Laplacian and next wall/next tangent fixed; map (Hprev,Hnow,HTprev,HTnow) to (E4,E5,E4tangent,E5tangent) has determinant S^6/(32 h^4 t^8), nonzero for physical S,h,t>0, independent of H_T coefficient (actual negative). Thus no independent history coordinate can simply be dropped from unrestricted receiver input; not a lower bound on checkpoint compression or reachable-state dimension. Both dual-Weyl identities checked. 2205 cursor cases nt=2..64 establish equivalence of captured-history conditions and stored-slot checks.

Actual full propagate() for original coarse grid, dr=.012,dy=.016,requested dt=.0025, realized dt=.0024992243525406577, nt=1084 plus original one-step lookahead, t=12, eps=.04, pulse=.065, inside_chord=.012, r_outer=3.01,y_outer=2.01, mode3, conservative exact source. 252 radial x127 normal nodes x3 multipoles. For EACH native and affine mode, reference run uses only terminal checkpoint, resume run deliberately raises InterruptedError AFTER the actual production atomic save at cursor 13,1083,1084 and resumes via actual propagate() load cursor. History counts at these cuts (0,0,0,0),(0,0,0,0),(756,0,756,0). After cursor1085 all four captured arrays present. All nine NPZ entries (identity,cursor,U,P,M,w0..w3) byte-identical between reference/resume; complete JSON receiver dictionaries identical; reopening completed checkpoint identical; cross-affine checkpoint rejection PASS. In-process exception/reentry, not separate-process or hard-kill test. Exact simulation step/source and readout unchanged. Both routes actual full-duration 1085 steps reference and resumed (4340 completed SSPRK3 steps total, excluding endpoint readouts). No physical convergence certification.

Cross-route final state relative Frobenius norms U=1.5644016961558904e-13,P=1.5412506032577618e-14,M=8.290111763655995e-14. Max absolute 2.2894013074203912e-14,1.0720313525780512e-12,2.9467539519600905e-12. Max relative saved wall-array norm 5.680922828678976e-13. Native corrected aggregate H=-5.139787590641485e-6, E4=-6.686964284549739e-5, E4tangent=-6.684435301889459e-5, E5=-2.93029492369092e-6,E5tangent=-2.8779206210907818e-6; affine aggregate differences absolute respectively 2.795208725939191e-19,3.686287386450715e-18,2.995108501491206e-18,2.2048267617029438e-18,7.707999820014133e-19. Native near E4 ell0/2/4 =(-6.873148224322227e-5,2.083009645683312e-6,-2.2117024795841358e-7); E5=(-2.9631294232594324e-6,3.36584409818217e-8,-8.239414133138939e-10). Far E4=3.918419037078271e-6, far E5=1.1916836588674088e-7, nonzero far-control diagnostic not acceptance; discrete support photon margin .006459111173937387. Full corrected receipts retained locally, no legacy reinterpretation.

Gate update: LI.4 and LI.5 actual cursor-driven propagation parity PASS on coarse native and affine; LI.6 original nine-grid execution 1/9 (coarse) complete, eight remaining; XLVI actual compact affine physical-state stage full-grid execution PASS for coarse, independent convergence/CFL/energy still OPEN. Next medium/fine and fixed-dt factorial/time-halving using existing checkpoint runner, signed per-multipole E4/E5/tangent comparison, strong trace plus coupled stability. Agda and G1-G6 physical convergence remain OPEN. Do not use CI or DNS as mathematical blockers.

### LV follow-up — fresh-process restart and concurrent production reconciliation

Starting head 76852b32aa881aabf6f2d120d44016eacc239df9 already reports actual full original coarse propagate() checkpoint acceptance for both routes (in-process exception/reentry). Preserve that receipt and do not repeat coarse unnecessarily. Independently executed local fresh-process small-box cursor-driven restart using LIV extracted stage module and compact source/checkpoint helpers: native route completed both schedules (65,130) and (159,160,161), 18/18 final array comparisons bitwise equal inferred from completed loops; affine route not confirmed before execution timeout. No hard-kill or full production separate-process claim. New scripts/check_f8_lv_fresh_process.py adapts local harness imports to repository LIV owner; committed import variant not executed here. Actual coarse production values and checkpoint acceptance are parallel-worker reported, not independently reproduced in this turn. Nine-grid completion remains 1/9 per existing receipt, G1-G6 open. Prioritize medium and medium-dt-half then factorial; preserve signed far controls. No CI or direct checkout.


## Maximum-cut LVI — original nine-label corrected spatial/temporal refinement completed (2026-11-20)

Local native solver/source/checkpoint files retained and git hash-object verified identical to live head 76852b32: solver 26f089b2aea202a82f19db7faa6c0e3eaa4554c5, compact source dec4e79e3a4899952a5deceb786324bc0745982c, checkpoint 4e319596d9064e7c9238b4a6570401e94df8a521. No CI or checkout. Reused LV native coarse full receipt, executed seven further distinct original meshes by actual propagate() in separate process invocations with 12 s cooperative budget, 90 s external timeout, checkpoint every 16 steps. All seven completed. Original geometry: eps=.04, pulse=.065, t_receiver=12, inside_chord=.012, r_outer=3.01,y_outer=2.01, mode3, conservative exact compact source, native (non-affine) physical evolution. Nine named labels = eight distinct configurations; factorial-D and fine are identical and share receipt, not a second execution. 18072 new completed SSPRK3 steps including each original one-step receiver lookahead; coarse plus new unique grid steps 19157. Coarse historical LV results are corrected, not old axial XI data. Fine cursors 698,1452,2236,2259 completed; factorial-A 1902,2259; factorial-B 1022,2087,2259; factorial-C 925,1932,2259; medium-dt-half 1780,3012; fine-dt-half 664,1424,2124,2842,3535,4320,4517. Medium completed in one run (1507). This establishes actual separate-process cooperative restart, not arbitrary hard kill recovery.

| Grid | E4 | E5 | Steps to t=12 (exclude lookahead) | Realized dt |
|---|---:|---:|---:|---:|
| coarse | -6.686964284549739e-5 | -2.93029492369092e-6 | 1084 | .0024992243525406577 |
| medium | -2.83440259136827e-5 | -2.326215693087443e-6 | 1506 | .0017989104901421466 |
| fine / factorial-D | -.0006305010586119393 | -1.9319604479653438e-5 | 2258 | .0011998047821762945 |
| factorial-A | -2.796398969929862e-5 | -2.2844428402152477e-6 | 2258 | .0011998047821762945 |
| factorial-B | -2.696307420875615e-5 | -2.193711083547378e-6 | 2258 | .0011998047821762945 |
| factorial-C | -.0006197097936602348 | -1.8439474155515213e-5 | 2258 | .0011998047821762945 |
| medium-dt-half | -2.7869583443381285e-5 | -2.27229181487936e-6 | 3011 | .0008997539681680747 |
| fine-dt-half | -.0006311771382137478 | -1.962229512899513e-5 | 4516 | .0005999023910881472 |

New locally executed scripts/check_f8_lvi_refinement.py at a46960f6dce6f80e974083daf89173b76d5411b9; local/remote blob dfe2eef989aed4b34928aa0c43cfbbd5a971997c identical. Reads eight complete local corrected JSON receipts, validates declared operator, mesh spacings, source parameters, native mode and finite 3-channel near/far arrays and aggregate sum guards; checks exact finite factorial closure for H/E4/E5 and tangent/laplacian/far channels. Local SymPy exact three identities PASS: E5-2E4=(L-B)/t², A=-4t²E4-L, B=L-t²(E5-2E4), L=Delta3H, A=H_etaeta,B=H_eta. These are inversion identities, not independent strong PDE residual checks. Compact signed data (eight configurations, all H/E4/E5/E4t/E5t/L/farE4/farE5 multipoles) transcribed from actual local output and commit-specific readback verified at 4eac325361e33d329eadaaf9955bd76746bb7b39, Artifacts/ksw668/ads5_f8_LVI_corrected_refinement_compact_20261120.json. Not the byte-identical complete solver receipts; raw full JSON and checkpoints remain local.

Fixed dt factorial A=(.008,.012),B=(.008,.009),C=(.006,.012),D=(.006,.009). For each mode define radial=C-A, normal=B-A, interaction=D-C-B+A; total=D-A. Signed aggregate E4 radial=-.0005917458039609338, normal=1.0009154905408842e-6, interaction=-1.1792180442238713e-5, total=-.0006025370689126317. E5 radial=-1.6155031315295247e-5, normal=9.073175666468814e-8, interaction=-9.708620807896397e-7, total=-1.70351616394202e-5. Both tangent routes consistent with radial dominance. Fine fixed-space halving E4 change=-6.760796018085e-7 (about .107% relative to previous magnitude), E5 change=-3.02690649341694e-7. Medium time half relative to original medium changes E4 by +4.74442470301415e-7, E5 +5.3923878208083e-8. Two/three temporal samples, not quantitative certified convergence. Simultaneous three-grid accuracy remains FAIL/OPEN; no trustworthy continuum sign. Far controls nonzero (fine E4 6.540873721793367e-6, E5 1.9700976392193515e-7), not an exact numerical causal null.

Radial-only E4 difference decomposes by original receiver geometry: spatial=-.000296622523591549, acceleration=-.0002951232803693849, i.e. 50.1267/49.8733 percent of signed total. Per ell0/2/4 spatial approx (-3.36123219e-4,4.03413882e-5,-8.40693245e-7), temporal acceleration (-3.39728054e-4,4.55956987e-5,-9.90924816e-7). Thus dominant radial sensitivity is not isolated to spatial differentiation; it affects the evolved field and acceleration too. Do not conclude which source/evolution/readout mechanism dominates without further tests. Next maximum cut: compare actual compact cell source representations in common radial weighted carrier, use weighted FV/continuum cell overlap and native radial eigen/subspace transport to attribute source versus propagation versus receiver discrepancy per ell; same physical time fibre residual and signed/absolute adjoint ledger pattern from #1530 can be reused but not the canonical FE equations or its physical claims. Test original radial-only third/fourth spacing with fixed normal and sufficiently resolved time, and independent source moment/high-frequency and interpolation residuals. Establish coupled moving SSPRK3 CFL and strong Israel trace separately. LI.6 execution coverage 9/9 labels PASS (8 unique, 7 new); numerical convergence FAIL/OPEN; exact affine parity remains only coarse scope; G1-G6 physical/Agda acceptance not promoted.

### LVI follow-up — independently replayed production medium temporal pair; full receipt preservation (2026-11-20)

Preserve concurrent full eight-distinct-grid compact receipt and refinement analysis at c9e19d5a80373b1197016805291dd20cc22a4530. This turn independently reconstructed all three actual solver files, with local git hash-object matching solver 26f089b2aea202a82f19db7faa6c0e3eaa4554c5, checkpoint 4e319596d9064e7c9238b4a6570401e94df8a521 and source dec4e79e3a4899952a5deceb786324bc0745982c. Local NumPy 2.3.5, Numba 0.65.1, SymPy 1.14.0; no CI or direct checkout. Actual production propagate() independently executed native mode3, original geometry (eps=.04, pulse=.065, t=12, inside_chord=.012, r_outer=3.01, y_outer=2.01), dr=.008,dy=.012, 378x169x3. Medium completed 1507 steps including lookahead via fresh-process cooperative exits at 328 and 1020. Medium-dt-half completed 3012 steps including lookahead via exits at 539,1051,2021,2998. Terminal checkpoint cursor and finiteness of U/P/M and all four histories checked. Full JSON dictionaries augmented with grid/requested mesh/schema/source blob metadata, no numerical field removal, committed byte-identical to local files with blobs fcc651c5daeb00b906bcf291f544b4acbadc08a9 and 17f39b9e7563c31cf76718e06220abe0ce61ef49 respectively. All 52 shared compact receipt component/clock values agree exactly as binary64/integer. No production solver change; neither full fine nor factorial grids independently rerun this turn. They are concurrent-worker reported actual executions.

Local scripts/check_f8_lvi_temporal_receipts.py executed against these two full JSON receipts, 3/3 exact SymPy identity assertions and 44 counted real receipt checks PASS plus common geometry checks. Local scripts/check_f8_lvi_factorial_rational.py executed against selected decimal lexemes transcribed from existing compact receipt 07c0950b5f9d7e8bfa25ad934ac228a5522c0ccf, 24/24 exact arithmetic decomposition assertions PASS. Byte-identical regression script blobs db6bd190375fa60b0b472c6343d41e612b166781 and 1f4ca2a749a71f4449261478d528b99c45091cc4. These are arithmetic/receipt checks, not independent PDE proofs. Fixed-space realized dt ratio 1.99933598937583. Relative changes aggregate E4 1.673871%, E5 2.318095%, tangent E4 1.704220%, tangent E5 2.916996%, far E4 .438915%, far E5 .378344%. E5 ell0 relative 99.41943% from tiny denominator, absolute change 5.627419526524189e-9. Coarse-to-medium E4 absolute change 3.852561693181469e-5 versus temporal halving 4.7444247030141516e-7, about 81x. Radial ell0 signed factorial ratios E4 .9862360513769654, E5 .9705854503707955; total E4 radial=-.0005917458039609338, normal=1.0009154905408836e-6, interaction=-1.1792180442238701e-5. Radial geometry inversion is derived from same receivers, not an independent residual. LI.6 9/9 labels (8 distinct) execution coverage via concurrent receipt plus independent medium pair. Convergence remains FAIL/OPEN, no trustworthy continuum sign, no G1-G6 promotion. Next isolate source projection vs native radial transport vs receiver reconstruction in common weighted FV carrier; use existing source and radial FV owners and reuse #1530 signed/absolute residual ledger, not a new physics model.


## Maximum-cut LVII — weighted radial-fibre endpoint source/transport/receiver attribution (2026-11-20)

Standing local SymPy/NumPy/Numba, checkpoint and geometry-first policies retained; no CI or direct checkout. Starting head c9e19d5a80373b1197016805291dd20cc22a4530. Existing complete A/C native checkpoints and solver/source blobs verified locally (26f089b2aea202a82f19db7faa6c0e3eaa4554c5, dec4e79e3a4899952a5deceb786324bc0745982c). Native checkpoint helper reused. A=(dr=.008,dy=.012,dt request .0012), C=(dr=.006,dy=.012,dt request .0012), exact same realized dt=.0011998047821762945, nt=2258 plus original receiver lookahead, eps=.04, pulse=.065, t=12, mode3, original near/far receiver. 377/502 active radial cells plus enforced zero outer nodes, same 169 normal nodes. Active radial extents 3.012/3.009 differ; do not assert identical outer boundary geometry.

For effective dimension d=3+4q, dmu=r^(d-1)dr, construct I_ij=mu(F_i intersect C_j)/mu(F_i) using exact rational SymPy overlap masses and clipping to actual active cells. Outside source domain use zero extension. Exact nonnegative overlaps, row/column submass sums, common-support total measure and weighted transpose identity checked on actual three carriers. Jensen yields ||Ix||_Wf<=||x||_Wc, with no assumption that I preserves all derivatives or higher Sobolev norms. Conservation is of source supported inside the shared interval; general field totals may lose the coarse-only outer strip. Exact native interior r^2 stencil identity 2d verified for d=3,7,11; origin uses native 2d coefficient. Weighted random adjoint/contraction checks pass. State identification treats nodal values as piecewise constant cell representatives; this is a declared diagnostic choice, not a unique continuum identification or high-order commuting projection.

Actual original compact TT source arrays evaluated independently. Weighted relative ||I s_c-s_f||/||s_f|| = 1.0234901366575235,1.4226571777264103,2.5263611228858185 for ell=0,2,4. Overlap conserves integrated compact source moments but not profile. Native radial commutator ||A_f Iu-I A_c u||/||I A_c u|| on compact polynomial u=(max(1-(r/.12)^2,0))^4 = .6926820071810066,.4872146438501627,.39225748238291747. Neither these probe commutators nor source discrepancies are continuum error estimates. Transfer can introduce its own interpolation errors.

New scripts/check_f8_lvii_radial_fibre.py committed c6752992bba46e99bfd84ba0789716b6f614e353; local executed blob 56c70d1b980708f6b182c2f6b559a20786bc20b6 matches remote. Uses literal native Numba stage/enforce, transcribed original physical-state SSPRK3 chronology and extracted literal original read_all AST (no alternative Weyl formula). Replay of original stored A/C wall histories reproduces all four signed near receiver arrays bitwise. Diagnostic source intervention: on fine operator and original fine clock evolve I s_c instead of independently projected s_f. Separate diagnostic checkpoint identity includes explicit intervention label, source-array hashes and diagnostic script SHA256. Three local bounded executions (8,8,12 s cooperative budgets) reached cursor 873,1687,2259. Independent local control using same transcribed chronology with native s_f completed all 2259 steps (19.78 s elapsed) and reproduced full U/P/M and four checkpoint wall arrays bitwise. That control was executed as an inline local Python regression, not a separately committed test file. 4518 additional completed steps total. No original evolution or source producer modification; intervention is not a physical source replacement.

Let J_c,J_f be original coarse/fine receivers, J_m fine evolution with I s_c, J_I literal fine receiver on transferred coarse terminal histories. For both receiver routes transfer all six wall/tangent arrays including lookahead; do not substitute fine RHS-derived tangent for coarse tangent. Exact finite identity J_c-J_f=(J_m-J_f)+(J_I-J_m)+(J_c-J_I). First term source representation, second transport, third terminal receiver identification. Sign is A minus C (opposite LVI factorial). In exact arithmetic the transport term can also be obtained via sum of the fine homogeneous propagators applied to step defects I G_c-G_f I plus the stage-source quadrature mismatch after source transfer. Current implementation computes this via endpoint differences, not per-time-step signed/absolute adjoint ledger; no claim time-local attribution executed. Coordinate/transfer choice changes the split. Near/far H,E4,E5,both tangent routes and Laplacian, all three signed multipoles retained.

| Near receiver | Source | Transport | Receiver | Total |
|---|---:|---:|---:|---:|
| E4 | .0005235625002629668 | .000053174328726630426 | .00001500897497133665 | .0005917458039609338 |
| E5 | .00000898424192371254 | .00003102598297172032 | -.00002385519358013761 | .000016155031315295247 |
| E4t | .0005234158437083562 | .00005316922762968379 | .00001500822737583379 | .0005915932987138738 |
| E5t | .000008695112004057952 | .00003101275329179221 | -.000023856702550156638 | .000015851162745693527 |

E4 source contribution fraction ~88.48% of signed A-minus-C difference for this identification. E5 exhibits cancellation; near E5 transport greater than signed total. Far E4 source/transport/receiver/total=(-8.1034154222462e-6,1.5565747113401881e-7,9.56596631183076e-8,-7.852098287993874e-6); no causal null claim. Full compact signed data from local LVII.json transcribed to Artifacts/ksw668/ads5_f8_LVII_radial_fibre_attribution_20261120.json at 7c2e9f55304b99f5046dc1f8a95f7ef3c78a1c93, readback verified. Receipt is a structured transcription with metadata, not byte-identical local diagnostic JSON. All 36 (2 positions x 6 metrics x 3 multipoles) additive splits checked at atol=1e-12/rtol=1e-12. Raw checkpoints remain local.

Gates: LVII.1 weighted radial overlap and weighted transpose PASS; LVII.2 actual source projection mismatch TESTED; LVII.3 full-duration source intervention with native-stage control PASS; LVII.4 original receiver-relative endpoint source/transport/readout attribution PASS (declared transfer); LVII.5 independent robustness under higher-order conservative identification OPEN; LVII.6 time-indexed signed and absolute radial-fibre residual transport OPEN; radial and physical convergence FAIL/OPEN. Next maximum cut: evaluate source projections against a common independently integrated continuous compact TT source / higher-order conservative reconstruction (not replace emitter or fit E4). Compare source spectral coefficients using exact native weighted radial Green form, quantify source moment hierarchy and smoothness alias, independently refine radial-only grid. Derive exact fine SSPRK3 transpose with terminal history injections and transport the time-indexed radial commutator defects to both Weyl receivers, including signed/absolute contributions, rather than calling endpoint split an adjoint certificate. Coupled moving CFL, G1-G6, continuum physical and Agda remain OPEN.

## Maximum-cut LVIII — geometry-first constructor type audit (2026-11-20)

Preserve concurrent LVII full source/transport/receiver attribution at e97d86a888b0060af9e65703eb527ffef1f83fbf (reported source 88.48% of signed E4 A-minus-C under declared overlap). Actual solver blob 26f089b2aea202a82f19db7faa6c0e3eaa4554c5 inspected via connector. Local scripts/check_f8_lviii_geometry.py executed 15/15 exact SymPy assertions: three original weighted source primitive derivative identities (arbitrary smooth f), two cubic derivative identities, four cubic reproduction identities, six origin positive/negative controls. Native nodal origin stencil 2d(V1-V0)/h² exactly reproduces Delta_d r²=2d. For literal weighted cell averages of r² instead, avg0=d h²/[4(d+2)], avg1=d/(d+2)*[((3h/2)^(d+2)-(h/2)^(d+2))/((3h/2)^d-(h/2)^d)]. Exact relative origin defects (d=3,7,11) =16/65,608/1093,797168/1151449, independent of h. This is a constructor interpretation negative control, not proof native mass-lumped nodal discretization is inconsistent: conservative cell-average source loads may be legitimate dual/load data rather than state averages. Do not repair native stencil or receiver as though U were literal cell averages without deciding geometry. LVII overlap transfer of state histories is conditional on piecewise constant reconstruction; source/load transfer and nodal field transfer should be distinguished. Next implement independently integrated mass-lumped hat-basis source load vs current cell-constant test load, retaining exact continuous TT source and moment checks; nodal prolongation with weighted adjoint vs conservative overlap for dual source loads; manufacture origin and receiver polynomials for each representation. No production changes, no fresh propagation execution; local exact checks only. Coupled stability and physical convergence remain open. No CI or direct checkout.


## Maximum-cut LVIII — higher source moments and native weighted radial spectrum (2026-11-20)

Local SymPy/NumPy/SciPy, no CI. Starting head e97d86a8. Original source producer fetched at blob dec4e79e3a4899952a5deceb786324bc0745982c. Local runtime reset; earlier complete solver/checkpoints not present. Independent quadrature diagnostic transcribes original normalized TT source differential expressions from solver, not production exact_cell_averages execution. New scripts/check_f8_lviii_moments.py at 78c4bc110c0c97c6cf19200539d96c8824751b25, local/remote blob c427e2eddad751f20811da93473204d85a4f3c1c. Dimensionless u=r/eps, d=3+2ell, h=dr/eps, B_p=integral_0^1 u^p exp(1-1/(1-u²))du. Formal integration by parts gives j=0..4 normalized moment kernels:
- ell0: 0,0,48u²,336u⁴,6048u⁶/5.
- ell2: 0,120u²,720u⁴,2376u⁶,41184u⁸/7.
- ell4: 27u²,99u⁴,1287u⁶/5,3861u⁸/7,7293u¹⁰/7.
All 15 lower-end boundary polynomial jet checks and independent 512-node Gauss-Legendre quadrature comparisons passed with absolute tolerance 1e-8*max(1,abs(target)). Upper-end derivatives vanish for the standard compact bump. Physical moments multiply by eps^(d+2j). B2=.09541369929430046, B4=.03197188662709491, B6=.013917363091747735. New critical cancellation ell0 j=1 as well as j=0. For dr=.008,.006,.004,.003,.002 independent weighted cell averages and native nodal moments give ell0 j=1 .2279535243267503,-14.9811246940545,8.525638228904711,9.692867211723751,-.6921148433155224, while j=0 absolute below 2e-11. These are nodal moment quadrature defects, not failures of the continuum source identity; true cell-integrated higher moments are not represented by nodal weights. For ell2 j=1 target 120B2=11.449643915316055; coarse/fine nodal values 16.894240037349128,-10.261645354674119.

Weighted radial Green matrix built directly from shell-face flux, including origin and enforced zero outer node at original r_outer=3.01. Similarity via sqrt(shell mass) produces symmetric tridiagonal negative radial operator; positive eigenvalues of its negative, weighted Parseval checked on all 15 dimension/spacing pairs. Fraction of source squared weighted L2 norm in discrete eigenvectors with kh>1 (k=sqrt(eigenvalue), dimensionless h):
| dr | ell0 | ell2 | ell4 |
|---|---:|---:|---:|
| .008 | .9940741290 | .9591131648 | .9994058650 |
| .006 | .9409514538 | .8881307966 | .6237175663 |
| .004 | .9786259864 | .9755294281 | .9817601983 |
| .003 | .9649939659 | .9580698955 | .9569633747 |
| .002 | .9335930098 | .9338990943 | .9322473200 |
This is a discrete source energy diagnostic, not a continuum spectral alias bound or receiver-weighted contribution. Different meshes have different eigenvectors/outer extents; no same-index eigenmode identification claimed. No source filtering or modification. Next: exact source moments against continuous low-frequency Bessel test functions; compare actual discrete eigenvector reconstruction against same continuous test functions; derive conservative higher-order transfer retaining moments without fitting receiver, validate production source byte-identical comparison; then time-indexed native SSPRK3 adjoint attribution and additional full propagation. LVIII moment algebra and independent spectral diagnostic PASS; production source parity, higher-order transfer robustness, full radial refinement, signed/absolute time ledger and coupled stability OPEN. No new full propagation or Agda acceptance.

## Maximum-cut LIX — dialectic/trialectic/pants adjoint ledger (2026-11-20)

Preserve concurrent LVIII higher-moment/spectral results at 89629509382a613d2d1224dea14ceb74a448658e. User requests dialectic/trialectic/pair of pants/clopen sphere/cylinder/Swiss cheese/CMYK reuse. Directly inspected default commit 116cd7de01b8a0da03703b3bb8db79c67fd15b50 owners DASHI/Reasoning/DialecticInvariantGeometry.agda (common vs projection, disagreement), DASHI/Reasoning/TrialecticAttachedTwoCellExact.agda (attached face not determined by edges or Cech triple intersection), Docs/RelationalBranchCobordismGeometry.md (capacity vs wave conservation, signed flux, typed seam matching), DASHI/Topology/WormSoilPantsSheafBoundary.agda (latent complement not forbidden, pants not p-adic fibre identity), DASHI/Visualisation/RendererParityExact.agda (explicit bit channels, black suppresses RGB; channel permutation is source-specific, not literal physical ink). Clopen sphere/cylinder candidate docs recovered by search excerpts only; do not identify clopen endpoint cylinder with ambient physical sphere. Use these as finite interface patterns, not proof of physical topological equivalence.

For common carrier with positive metric W_n, G_n dagger = W_n^-1 G_n^T W_(n+1). For error recurrence e_(n+1)=G_n e_n+r_n and receiver row j, lambda_N=W_N^-1 j^T, lambda_n=G_n dagger lambda_(n+1). Exact terminal attribution j e_N = <lambda_0,e_0> + sum_n <lambda_(n+1),r_n>. For multiple terminal history injections add W_n^-1 j_n^T at each corresponding time; tangent injection requires actual stage transpose, not substituted fine RHS for coarse history. For rectangular I use its correct weighted adjoint. Disjoint coordinate masks commute with diagonal W and give exact residual pairing partition; overlapping charts require weights summing to identity. Pants seam gluing must match time, state representation, dimensions, metric and provenance; composition reverses adjoints. Keep signed sum, sum absolute elementary contributions, and cancellation separately. Coarse signed totals cannot reconstruct fine absolute totals. Trialectic face remains independent if using actual crossed intervention factors: additive endpoint split is path-dependent, not unique causal interaction; a genuine 2^3 factorial requires all eight crossed evaluations on defined common domain. CMYK proposed diagnostic channel tags C=source,M=transport,Y=receiver,K=unresolved/interaction, not actual existing colour semantics; no RGB conversion to recover numerical ledger. Local scripts/check_f8_lix_ledger.py executed 66/66 exact SymPy checks using rational 3x3 surrogate transitions and original d=3,7,11 shell weights, all eight masks, cancellation and triple parity marginal negative control. No original native transpose or time-indexed attribution executed. These checks establish finite interface algebra only. Next derive actual mode3 stage transpose with original moving metric and all terminal readout injections; reuse #1530 only after literal stencil parity. Source load hat test and independent radial refinement still open. No CI or direct checkout. G1-G6 remain open.


## Maximum-cut LX — existing Bessel and temporal-fibre producers, cross-PR #1444 weighted Gram audit (2026-11-20)

Checked heads #1444 7b1d88e7332f8367a811025e6a1a91be66828f8b, #1527 89629509382a613d2d1224dea14ceb74a448658e, #1530 e0efe6abf86dd9c4f241272a572e12cc674250d7. Existing default-branch F8 static TT Bessel reconstruction (blob 57e9d58b9413ea67678447b14e2aa49cfaf5cae3) and UVIR sampling contract (7aedbb83ad4a9ec35ced24cf6451beaf36e1ff7b) own angular j0/j2/j4 rule and independent cutoff/spacing axes. #1530 warp_stage_adjoint.py blob 9a782292286ac4781ab0a924540c5a7203c5bfe0 owns original mode3/4 transpose; check_f8_gauss_fibre_dual.py blob 6582b247d187bfc7019c85dab4df537fc5ee3326 owns time-indexed residual telescoping, with checkpointed ledger donor. Reuse, do not derive competing transposes. #1444 BalabanCMP109L13BlockAverageAdjointFloorExact.agda literal normalized adjoint norm floor 1/28561 is specific to its own carrier, not radial; reuse finite Fubini/weighted Gram pattern. YMClayE1A3OriginalFiniteCoordinateProjectionExact.agda actual finite source-coordinate factorization gives source ownership discipline, not a gravity convergence theorem.

New local SymPy script scripts/check_f8_lx_bessel_bridge.py committed 7e128a0cd8cc9a5f0f075dff2ce0ce1f268d4b26, local/remote blob 9d2fe7229f159f0513b6a53e26f5747bb560d9ba identical. Uses transcribed original normalized TT differential source, local SymPy principal Bessel functions and exact weighted differential adjoint. For dimensionless u,k>0, Phi_ell=(2ell+1)!! j_ell(ku)/(ku)^ell, B(k)=integral u² f(u) j0(ku) du. All three effective radial ODE identities and all three differential adjoint identities PASS. By IBP with original compact smooth even bump, normalized source transforms equal (2/5 k^4, -60/7 k², 27) B(k) respectively. Initial quadrupole coefficient guess -12/7 rejected by exact check and corrected to -60/7. No numerical cutoff or fitted source. This verifies continuum algebra, not actual production discrete Fourier coefficients. For rational nonnested partitions [0,2/3,1] and [0,1/2,1], dimensions 3,7,11: exact weighted overlap adjoint, constant reproduction both directions, PSD defect Wc-I^T Wf I (positive diagonals, determinant zero), and I*I != Id PASS. This is a finite negative control, not a uniform Gram floor on actual full radial meshes. Actual outer strips in LVII require zero-extension accounting and do not share the constant reproduction assumption.

Next implementation: use existing normalized scalar transform owner rather than three independent transforms; evaluate actual production cell source coefficients against the exact same continuous Bessel tests and native weighted eigenvectors; check source-to-receiver transport with actual native donor transpose (mode3), signed and absolute inter-grid step residual ledger and saved-history injections. With e_n=I x_c,n-x_f,n, r_n=I x_c,n+1-G_f,n I x_c,n-g_f,n, backwards lambda_n=G_f,n^T lambda_n+1+w_n, receiver discrepancy comprises sum lambda_n+1^T r_n plus initial and receiver/identification mismatch. Tangent history must also include native stage readout noncommutation, not reconstruct coarse derivatives from fine RHS without ledger. No full native propagation or transpose parity executed in this round, earlier local solver/checkpoints absent. No CI. LX continuum Bessel identity and exact nonnested Gram negative control PASS; numerical discrete Bessel weld, actual #1527 transpose parity, full time-indexed ledger, higher-order robustness, uniform stability and physical convergence remain OPEN.


## Maximum-cut LXI — production FV Bessel discrepancy and corrected adjoint receiver covectors (2026-11-20)

Starting heads #1527 bef1cccc4b9f5dfb729943f6bdf3caefb3acaa8c, #1530 e0efe6abf86dd9c4f241272a572e12cc674250d7, #1444 d88d709c9630a2922ac1a47b243932b9480d7bd2. Local execution, no CI. Reconstructed actual production compact source file byte-exact, git hash-object dec4e79e3a4899952a5deceb786324bc0745982c. Default branch scalar transform owner ksw668_f8_uvir_source_cutoff.py blob 62c2e6ccae4e20227e74cd66acfe0c48185c93f7 inspected: normalized unit-mass transform equals B(k)/B(0), not B(k); LXI independent 512-node quadrature evaluates unnormalized B with original exp(1-1/(1-u²)). No source modification.

New executed scripts/check_f8_lxi_discrete_bessel.py at 194813987a3b3a5be1ecc4afac5512e9c71d183c, local/remote blob 92debd7a0c5e0a079ebe571b943525bb17cfbbe2. Actual exact_cell_averages(eps=.04) evaluated on dr=.008,.006,.004,.003,.002. For each ell=0,2,4 and each k=.1,.25,.5,1,2,4,8,16,32 compare native W-weighted nodal sum with exact weighted piecewise-constant cell reconstruction integrated against normalized Bessel functions, and continuum LX common scalar reference. 135 coefficients per route. Sampled relative Euclidean discrepancy (not continuum norm):
| dr | ell0 integrated cell | ell2 | ell4 |
|---|---:|---:|---:|
| .008 | .9324277709538783 | .6636184810631687 | .07510056161694842 |
| .006 | .887899900872093 | 2.028698677460194 | .10161575806985919 |
| .004 | .47035927125586746 | .8384822544236508 | .02940156700598675 |
| .003 | .5240899130842162 | 1.0996352737650386 | .04711180668233708 |
| .002 | .1493592976434534 | .07748461826136668 | .0020596914847759544 |

At dimensionless k=.1 continuous ell0=3.814416976520419e-6; reconstructed cell coefficients by dr=-.00037935241271824793,.02495164220446844,-.014191414207999742,-.016136321447220325,.0011560340135968739. Nodal coefficients nearly identical at this frequency. Cell-integrated dimensionless second moments .22815668582129933,-14.981403926055306,8.5256515380651,9.69287406907302,-.6921151747416736. Thus monopole cancellation defect persists even after replacing nodal Bessel quadrature by integrated test functions; actual FV source representation is responsible for this diagnostic, not just nodal evaluation. No claim of certified quadrature bounds or eigenmode/receiver contribution. Continuous reference from same analytic source, but default-branch scalar transform function not imported in this execution. Discrete Bessel test correspondence TESTED with failure of spectral consistency; actual eigenvector-to-continuous-test weld still OPEN.

Inspected #1530 warp_native_weighted_adjoint.py blob ed8c27a3ea8df73afcb5d515886824dcdd1e6bed and warp_adjoint.py blob 3a35f37e8534b56c85a0adf8a62a0769193c6e02. Original reverse SSPRK3 chronology reusable; their E4 observation covector uses axial Hxx, not corrected full reconstructed Delta3. Do not reuse that legacy covector for corrected #1527. E5 spatial covector already Laplacian, verify complete geometry and clock before integration. New executed scripts/check_f8_lxi_receiver_covector.py at 1ca2ac6e3ab75a6b269cac51c5f38bde0e81d7a1, local/remote blob 2b03c0fbe627c99ab5d3e3fba7ad73fa50fb3fdd. Local SymPy exact four-observation linear Jacobian, both dual-Weyl identities, both legacy axial difference identities, zero axial dependence, exact noncommuting rational SSPRK3 reverse product and finite intermediate-injection residual telescoping PASS. Corrected-minus-legacy E4=(Hxx-Delta3H)/(4t²). The Jacobian is with respect to six receiver-time history variables and spatial inputs, not yet full native state covectors. No new full propagation, donor transpose parity or time-indexed numerical ledger in this round. No Agda acceptance.

Next: reuse #1530 native transpose source and verify against literal current #1527 mode3 stage, including endpoint projection and original Newton clock. Construct corrected full-state injection from existing read_all cubic weights and stage tangent, compare to actual signed original receiver, then implement residual ledger using same aligned clocks A/C and LVII transfer including explicit tangent noncommutation. For source geometry, integrate against radial reconstruction basis reproducing constants and r²; higher-order conservative construction must be derived from same original source/action and retain support, not fit receiver. Compare native radial eigenvectors to common Bessel tests and quantify projection/transport separately. LXI.1 production source Bessel test executed PASS (accuracy FAIL); LXI.2 piecewise-constant representation defect isolated PASS; LXI.3 exact receiver covector and reverse algebra PASS; LX.6 native numerical transpose parity, LX.7 time-indexed radial ledger, LX.8 higher-order identification, physical convergence and coupled stability OPEN.


## Maximum-cut LXII–LXIII — 369 oriented hyperfabric / NS nonlinear temporal seam (2026-11-20)

Starting head #1527 26cf0f7dc6d0124f29e779bd0d0800324c097a64. Existing default-branch owners inspected at 116cd7de01b8a0da03703b3bb8db79c67fd15b50: OrientedThreeAxisBracket369Exact, RightHandRule369Exact, PathfindingTemporalFibreEvolutionExact, NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact, NSTriadKNProjectedConvectionEnergyFluxExact, NSTriadKNCriticalResidualQuadraticVariationRound156Exact. Reuse orientation as ordered comparison incidence, not a physical time reversal or assignment of scalar radial modes to Cartesian directions. R530 exact sign quotient of integer Fourier modes and nine-trit triad address does not preserve addition or physical amplitude, nor identify T^3 with the radial carrier. R156 finite signed pairing CS budget is reusable, not its unpaid cutoff-uniform physical budget. Projected convection energy cancellation requires actual divergence-free physical carrier and projector; not inherited by arbitrary transfers. Retain #1444 actual weighted Gram and #1530 actual stage/adjoint owners.

For same-time identification I_n and next-time I_(n+1), seam r_n=I_(n+1) F_c(x_c)-F_f(I_n x_c). Quadratic affine F=A x+Q(x,x)+g splits exactly into linear commutator, nonlinear triadic defect I_(n+1) Q_c(x_c,x_c)-Q_f(I_n x_c,I_n x_c), and source mismatch. Linear gravity is Q=0 specialization only, not physical NS equivalence. For y=I_n x_c,z=x_f,e=y-z, bilinear Q gives exact secant L(y,z)e=Ae+Q(y,e)+Q(e,z), so next error=L e+r. For moving positive metrics W_n,W_(n+1), L*=W_n^-1 L^T W_(n+1); receiver backward recurrence L* lambda_next+w_n with observation covector represented in current metric. Signed pairing <lambda_next,r>_(n+1) is exact finite ledger term, absolute sum and Cauchy-Schwarz budget retain cancellation information. Reverse comparison exchanges the two paths in the SAME codomain; no inverse transfer asserted. For actual nonlinear SSPRK3 use stage-wise secant composition with Shu-Osher combinations, not claim the full RK map is quadratic.

Local SymPy 1.14.0 executed scripts/check_f8_lxiii_ns_seam.py (commit 3369e0e6218841a63e1df5842953e9e66238c974, local/remote blob 4824267ec0cc6d725df986e8f9d74b12b40a2ee9): 8/8 exact finite assertions on explicit rectangular nonnested time transfers, bilinear quadratic maps, signed seam decomposition, exact secant and error recurrence, moving weighted pairing and defect identity, path exchange, R156 finite Gram identity, nonadditivity of integer sign chart. Initial test incorrectly treated the adjoint matrix as the adjoint-applied vector; corrected and reran all assertions. This is an executable exact finite algebra fixture, not a native NS triad or gravity evolution run. No CI. No Agda check or actual hyperfabric same-object instantiation yet. LXIII algebra bridge PASS; LXI.8–11 remain OPEN. Next retain actual R530 mode addresses and physical triad values for NS, actual radial weighted carriers and stage-time coordinates for gravity; reuse existing donor transpose, corrected Weyl full-state injections, execute actual time-indexed radial ledger, and separately prove the same-action nonlinear matter/stress bridge and cutoff-uniform energy budgets. No physical convergence or NS regularity promotion.


## Maximum-cut LXIV — native mode3 stage and reduced-box radial time-fibre ledger (2026-11-20)

Starting head 07c0784a39be69f53c1a7288e72362f25f0b185a. Native solver blob 26f089b2aea202a82f19db7faa6c0e3eaa4554c5 inspected; literal stage function transcribed into local extracted-stage module (not full byte-identical solver). Actual source producer local blob dec4e79e3a4899952a5deceb786324bc0745982c and #1530 donor warp_stage_adjoint.py local blob 9a782292286ac4781ab0a924540c5a7203c5bfe0 exact. Donor copied without changes into #1527 at 6d104c90243fcd3356899c99d84a8d8f3dbeb7f8. Existing mode3 transpose used, not rederived. New executed scripts/check_f8_lxiv_native_fibre.py at 7c8963de03fb864224f1bd9a1dff24a62e5f8314, local/remote blob 59a9e6fcee91bcddc386d44e45fb892afdf5ec13. Local NumPy/Numba 0.65.1/SciPy, no CI. Reduced box prefix with dr=.008/.006, dy=.012, h=.0011998047821762945, eps=.04, pulse=.065, 16/21 radial nodes, 9 normal nodes, 40 steps plus one lookahead, receiver t=1.0348158150413098 and r=.08. Uses independent Brent clock inversion rather than original Newton iteration, transcribed SSPRK3 chronology and corrected full-spatial observation weights, not complete propagate/read_all. Source remains active at terminal time; E5 formula is only a diagnostic linear functional in this fixture, not a certified source-free physical Weyl observation. No physical causal interpretation. Native mode3 projected stage transpose 8/8 sampled pairings pass, maximum relative discrepancy 2.568479443358641e-15; SSPRK3 composed transpose 6/6 pass.

Weighted shell overlap I applied to all 42 coarse states (including initial and lookahead), zero extension and enforced zero outer node. Residual r_n=I x_c[n+1]-F_f,n(I x_c[n]) for 41 transitions. Backward donor transpose with corrected cubic full-spatial receiver covectors at nt-1,nt,nt+1. Euclidean covector coordinates here (equivalent to weighted dual only after metric conversion); no physical energy metric claim. Tangent observation uses fine stage Udot on transferred states, not separately transferred coarse tangent. Thus ledger telescopes the mapped-state fine observation difference; not yet total original coarse/fine receiver mismatch, which needs explicit tangent noncommutation and coarse observation correction. All 12 multipole/receiver ledgers close, maximum |signed-expected|/sum abs=6.228304920823993e-15. Results (ell, channel E4/E5/E4t/E5t, signed, sum abs):
- ell0: (-241.12985722036865,281.6951341723282), (497.97708746630815,548.9121287907823), (-242.7501212454334,282.91195293192874), (494.74714707083325,544.8990167317411).
- ell2: (-696.3530527911051,1297.437539655185), (602.0551743871868,1338.3565076170742), (-698.1746689037734,1293.8472207511907), (598.4453180507363,1318.5297398467699).
- ell4: (-38.11380513701736,104.03996713444424), (8.199353437687753,101.818937853478), (-38.08383900068225,103.43889457165507), (8.260731033458866,99.90519783416659).
Finite 369 oriented time seam now realized as numerical states/ordered paths and signed dual pairing in this fixture; no Agda typed hyperfabric instantiation claimed. LXI.8 numerical transpose PASS for tested mode3 prefix; LXI.9 corrected full-state injection and LXI.10 reduced-box ledger PASS for declared observation (not literal receiver parity/full physical box). Next actual A/C full-domain time-indexed execution with checkpointed forward history/reverse cursor, exact original Newton clock, independent original read_all parity, source vs transport split and explicit receiver/tangent mismatch; retain signed/absolute per-mode/time ledgers. Full physical convergence, stability, higher-order transfer, NS physical triad and same-action coupling remain OPEN. Prior full grid checkpoints unavailable in current runtime; no CI or full propagation claimed.


## Maximum-cut LXV–LXVI — conservative r²-reproducing weak radial source (2026-11-20)

Ownership reconciliation: #1527 starting head d85cb1c8360cb65a45afaf8be67f21ed3af5a4a8; #1530 c1c5982ca3b790b595548f23b255d7577ecaa6fc. #1527 owns production A/C radial ledger, Bessel/source projection, literal corrected receiver parity and explicit tangent-transfer mismatch; #1530 owns moving-frame/shell metric, TSVF/CMYKalpha, pants/excision and geometric dual representation. Reuse Euclidean native donor transpose and subsequent metric conversion, not a competing adjoint. #1444 weighted Gram and NS signed temporal seam remain shared donors.

New local diagnostic scripts/check_f8_lxv_source_basis.py at 9ab578ce7de0d454075bf5ce77fd664cc4c81f2d, local git hash-object and remote blob 4b44b551def486411f485b988a355a3f9f0c4664 match. Original source module local/remote blob dec4e79e3a4899952a5deceb786324bc0745982c. No CI. On each dimensionless interval [a,b], use psi_left=(b²-u²)/(b²-a²), psi_right=(u²-a²)/(b²-a²). SymPy exact partition of unity and reproduction of u² PASS. Weak load b_i=integral_0^1 u^(d-1) s_l(u) psi_i(u) du using original cell_mass and primitive integration by parts for second moment (ell4 includes the 27u² bump remainder). Candidate native FV coefficient is b_i/W_i, with W_i dimensionless native shell mass; dimensional scaling cancels in this quotient. No production emitter replacement. Exact reproduction implies M0 and M1 (not higher moments generally); all 60 numerical moment checks PASS over 5 dr x 3 ell x 2 moments x 2 Gauss-Legendre resolutions (128/256); all printed diagnostics agree under rtol=1e-7,atol=1e-8. Monopole M1 residual at dr .008,.006,.004,.003,.002 respectively -2.3092638912203256e-13,-3.2178131302672446e-14,-9.947598300641403e-14,-1.4210854715202004e-13,-4.263256414560601e-14 (256 nodes). ell2 M1=120B2≈11.449643915316; ell4 M0=27B2≈2.576169880946, M1=99B4≈3.165216776082. Only first two moments tested.

Same nine dimensionless Bessel test frequencies as LXI; compare actual FV nodal functional to new weak load nodal functional against continuum reference. Relative Euclidean sample discrepancy, NOT continuum weighted spectral norm or receiver error:
| dr | ell0 old/new | ell2 old/new | ell4 old/new |
|---|---|---|---|
| .008 | .9249001550/.8532702937 | .7239887562/.2163259068 | .0729890787/.0036949454 |
| .006 | .8732482677/.2196833584 | 2.0485401715/.1554553505 | .1106500248/.0105817117 |
| .004 | .6295992648/.1856396651 | .8603389204/.0587399081 | .0272397284/.0045581363 |
| .003 | .5738881406/.0533661873 | 1.1127445941/.0137300653 | .0463316157/.0013152915 |
| .002 | .1440562297/.0896248875 | .0740762243/.0111089314 | .0027136081/.0002892831 |

All 15 sampled errors decreased, not monotone under all refinement. At k=.1, monopole continuous 3.8144169765e-6; new values 1.4703005764e-6,5.8726306558e-6,4.4956486782e-6,3.9215736862e-6,3.7379330600e-6. Old FV fine .006 coefficient .0249515043246582; new 5.872630655767708e-6. Remaining higher-moment discrepancy not zero. Crucial support boundary: integral stops at physical epsilon=.04 but nonzero weak loads extend to final node at .042 on .006 and .003 meshes (node at .04 on other meshes). An actual nodal forcing or piecewise reconstruction can extend effective discrete support; must account for this and preserve causal margin before source acceptance. Weak functional and native FV diagonal Riesz identification is a candidate, not yet the consistent Galerkin mass/action or a proved TT-conserved reconstructed stress. No source fitting or filtering. No propagation, endpoint/receiver parity or full time-indexed ledger executed; earlier full checkpoint files absent. Existing LXIV fixture remains accepted only within scope.

LXVI.1 exact basis reproduction PASS; LXVI.2 first two moment cancellation/numerical quadrature PASS; LXVI.3 sampled spectral comparison improved (accuracy/convergence OPEN); LXVI.4 support/action/TT and causal geometry OPEN; LXVI.5 actual candidate source integration and same-clock A/C receiver comparison OPEN; LXIV.6–9 original time-indexed residual ledger, tangent mismatch, checkpoint transport, typed hyperfabric OPEN. Next factor out the tested weak-load producer, check native mass versus Galerkin Gram and support/causal bound, then run unchanged vs candidate source on original A/C carriers with actual production solver and checkpointed source/transport/receiver ledger. Do not independently develop #1530 frame geometry.


## Maximum-cut LXVII — stable reusable source, support and weighted Gram (2026-11-20)

Live starting heads #1527 13366fc202f9f35505045eacd797ab62108e80e3 and #1530 700012f6210b08fd34ae69f23233c9bcf102eb78. Inspected #1530 Docs/physics/KKRadialSourceMomentRefinement20261120.md: that lane separately owns minimum weighted L2 moment interventions and native operator-source variants, mode-4 source-bank compliance sweeps; its operator source can fail the support guard. Do not equate these with our weak-load source or reuse its mode-4 results as mode-3 propagation. Maintain distinct candidate constructors.

Original FV source byte-exact local blob dec4e79e3a4899952a5deceb786324bc0745982c, kept unchanged. New opt-in scripts/ksw668_f8_weak_source.py commit 71066652ea2e1882b6efda0486448ca185dd7811 blob 69f35c6569667034214035d810dee06251a6d2ad; executed scripts/check_f8_lxvii_gram.py commit bd9f08335bdc0637559e640d81a763b245c3301c blob d65412236cd7d21f36dcb13b895c5ba2d0f764c3; both local git hash-object == remote blob. Initial primitive integration coefficient-level quadrature check FAILED at ell4 origin, dr=.008 (128 versus 256 difference .00049494, 256 versus 512 difference .00552184). Original lambdified primitive contains numerically cancelling exponentials/rational factors. Do not relax tolerance. Use exact factored normalized TT derivative profiles P_l(u²) exp(1-1/(1-u²))/(1-u²)^8, evaluated using log of gap and direct weak quadrature on each radial interval. Local SymPy checks 3 factorizations + 3 original weighted primitive derivative identities PASS. This is the same analytic source, not a new profile. Reusable uniform-grid producer rejects insufficient source extent before outer Dirichlet node and returns native W^-1 weak load. 256/512 coefficient comparisons PASS on 5 meshes with rtol=1e-8,atol=1e-6; 30 moment checks PASS at tolerance 1e-8. Maximum monopole M1 abs 6.48015e-12 (256). This is numerical quadrature, not rigorous bound.

Full hat basis on [0,outer node], restricted zero outer Dirichlet dof, G consistent Gram, D full row sum then restricted, W original native FV mass. Exact origin D00/W00=2^(d+1)/(d+2), G00/W00=2^(d+3)/((d+2)(d+4)), 6 SymPy checks PASS. D/W maximum at origin 3.2,28.4444444444,315.0769230769. Actual normalized Gram W^-1/2 G W^-1/2 on 15 active meshes has positive minimum eigenvalue >1/3 in tested configurations (not a proved uniform lower bound); max eigenvalues ~1.892657453,10.359534737,84.024174654 by ell. Polynomial 16-node Gauss quadrature exact in exact arithmetic, numerical eigenspectrum only. Nonzero positive neighbor Gram and different D/W show G,D,W not interchangeable. D-G is a graph Laplacian (sum of positive interval offdiag weights times squared neighbor differences, zero outer value); weak source W^-1 b preserves native work pairing algebraically, not full Galerkin action equivalence or reconstructed TT conservation.

Original rx at t=12, inside_chord=.012, log(12) photon reach. For dr=.008,.006,.004,.003,.002 loaded node last=.04,.042,.04,.042,.04; shell edge margins .00845911117,.00745911117,.01045911117,.00895911117,.01145911117; reconstructed hat support margins .00445911117,.00445911117,.00845911117,.00745911117,.01045911117. All exceed dr/2 on these five meshes. This is geometric source-support guard only, not a finite-speed numerical theorem or far receiver causal-null acceptance. No changed production default. No full propagation or adjoint ledger in this audit. LXVII producer, factored profile exact bridge, numerical Gram and support guard PASS; mass/action consistency, TT reconstructed stress, original propagation and full time-indexed residual ledger remain OPEN. No CI or Agda acceptance.


## Maximum-cut LXVIII–LXIX — original-domain A/C source intervention (2026-11-20)

Starting head 53805768eb3d066fb4fbb72e4fa0c17dc13c6465. Production propagate opt-in weak_source_load implemented at 34e09726c0f4f27f452dbff47ac60c0c2c58ee26 (default false, requires conservative mode3, checks hat support guard, source provenance receipt, config flag). Native checkpoint producer hash extended at fafe38d05d93452eecca8635b1d89e1c51def495. Native checkpoint old identities intentionally incompatible after code/config changes; no acceptance of old checkpoints. Existing original mode3 stage, Newton clock, read_all and original source untouched in default numerical path. Source variant remains diagnostic; no action/TT equivalence promotion.

Local full-duration execution: complete solver unavailable in container and direct raw GitHub download failed DNS. Extracted native stage source local blob e46e91f7319b1483d1e349e94f28cbe6d77d782a, exact source producer blob dec4e79e3a4899952a5deceb786324bc0745982c, weak source blob 69f35c6569667034214035d810dee06251a6d2ad. Original Newton clock, mode3 stage and SSPRK3 chronology, cubic corrected full-spatial E4/E5 FD and tangent readouts transcribed into diagnostic replay. Local script initially imports native_stage, later equivalent extracted module name ksw668_f8_tt_multipole (completed C1 readback rerun). Committed replay scripts/check_f8_lxix_source_replay.py at 24a11ff295b06f554ce8fb717163d5663c317b8e, local final git blob f4cafa1a79d2559364da6ff14cdb6fce9d5afdce matches remote. Diagnostic checkpoints atomic rename with source array check, not full NativeCheckpoint identity; use separate workdir for replay. Native driver scripts/run_f8_lxix_native_source_matrix.py at 764d0d92a4baaf532838a3f2b435dd95053b54e0 is implemented but not executed end-to-end. Re-run exit75 with new native checkpoint directory, e.g. OPENBLAS_NUM_THREADS=1 python scripts/run_f8_lxix_native_source_matrix.py A1 --budget 12. No CI.

Four full-domain diagnostic replays A0,A1,C0,C1, dr=.008/.006, dy=.012, r_outer=3.01,y_outer=2.01, eps=.04,pulse=.065,final_t=12,dt=.0011998047821762945,2259 completed steps each incl lookahead (9036 total). Source representation alone varied within each mesh. All finite. A0 and C0 aggregate near E4 match previous LVI production values within 1.35e-18 and 1.06e-17 absolute respectively; this is scalar reference parity, not full endpoint equality or literal complete native receiver parity. Receipt Artifacts/ksw668/ads5_f8_LXIX_source_intervention_20261120.json committed at 378c3c0b5b1bc86c6fffed26843eb44137b39f60 retains all 96 signed per-mode coefficients (4 runs x 2 locations x 3 modes x 4 receivers).

| run | near E4 | near E5 |
|---|---:|---:|
| A0 | -2.7963989699297e-5 | -2.2844428402125e-6 |
| A1 | -2.7325210541697974e-5 | -2.009738818203833e-6 |
| C0 | -6.197097936602453e-4 | -1.843947415553618e-5 |
| C1 | -1.456021577829e-4 | -1.324166912931084e-5 |

Signed C-A refinement discrepancy reduction ratios (magnitude old/new): near E4 5.00305273, E5 1.43831299, E4t 5.00231340, E5t 1.41513040. Near E4 original -5.91745804e-4, weak -1.18276947e-4. Source intervention A +6.38779158e-7, C +4.74107636e-4. Original near E4 mode defects [-6.75851273e-4,+8.59370869e-5,-1.83161806e-6]; weak [-6.78086561e-5,-4.82315084e-5,-2.23678276e-6]. Thus monopole discrepancy improves substantially but quadrupole changes sign and hexadecapole worsens; no uniform improvement claim. Far refinement discrepancy E4 old +7.85209829e-6, weak -1.15862842e-6 (6.7770634 smaller magnitude); far receiver still nonzero, no causal-null promotion. Factorial relation new=old+deltaC-deltaA evaluated for all 24 mode/location/channel entries, maximum absolute numerical closure 8.131516293641283e-20. This is an endpoint identity, not time-resolved attribution.

LXVIX implementation gates: opt-in native source/config integration IMPLEMENTED (not end-to-end accepted); full-duration extracted-stage A/C replay PASS 4/4; prior near E4 scalar controls PASS; signed endpoint factorial arithmetic PASS 24/24 tested; native full production runs, all receiver and state parity, NativeCheckpoint resume/identity tests for new flag, same-action source conservation, physical stability/convergence and full signed time-indexed ledger OPEN. Next execute native driver on all four labels and compare 96 coefficients, then reuse #1530 transpose and corrected covectors for checkpointed source/transport/receiver time ledger, tracking coarse tangent noncommutation. No new moving-frame implementation. No physical convergence or Agda kernel promotion.


## Maximum-cut LXX–LXXII — Bishop/Paper 9 constructive weak-load enclosure (2026-11-20)

Donor reconciliation: #1529 f5e6dd37492a0808503ec9be5d8bdcd223085be9 controlling constructive constants / Klein j roadmap, #1478 fb374e50e59a98e2b8a1eee215c77428c5728b68, #1530 2a1fb409e7396b4dff5f8e799c33eaff12806312. Existing BishopOriginalExponentialUniformCompactTailExact.sourceExpUniformLimitError is the compact-uniform original factorial-series analytic owner; exact rational evaluator below is not yet an Agda import or same-object proof. Paper9 consumer-selected jet technique motivates source-covector-only accumulation, not a modular identity for F8.

New scripts/check_f8_lxxii_rational_load.py commit 5d043b3b49c8430df9aea62b94e5a6259f538a25, local/remote Git blob d80c9dcba76cd7480d99be21925bf70aed5018d2. Executed locally against original opt-in weak source blob 69f35c6569667034214035d810dee06251a6d2ad. Exact decimal dimensionless meshes h=1/5,3/20. Rational negative exponential via halving to [0,1], alternating degree-25/24 bounds, 80-bit outward dyadic squaring. Common factor v^-8 exp(1-1/v) has derivative sign 1-8v, bound by endpoint extrema plus v=1/8 maximum. Rational polynomial Horner interval, monotone radial power and r² hat interval products; integrate by interval rectangles on each mesh interval up to u=.99. Endpoint collar uses e<3, exp(1/v)>=v^-50/50!, v<=1/50, hence absolute integral <=3 |c| ||P||_1 50! (1/50)^42 times actual overlap length, independently for each hat. No float arithmetic in enclosure construction. Local 32/64 subdivisions per interval: all 39 weak-load enclosures nested and contain the corresponding floating producer coefficient multiplied by exact dimensionless W (membership check, not proof of correct rounding). Max 64-piece enclosure width per ell: A 674.4921551535892,1069.5138296493444,26.23302602855665; C 490.25892850580414,731.4999513814753,16.86060675462044. These broad interval enclosures are an initial certificate, not a useful precision or receiver-error acceptance. No claim of arbitrary-precision convergence of fixed 80-bit evaluator. Exact rational mesh versus float-native mesh discrepancy not separately bounded. No Agda kernel or rigorous native floating propagation error bound.

Consumer source sensitivity K=sum_(n,s) B_(n,s)^T p_(n,s), using homogeneous linear native stage and actual observation injections. For coefficient sensitivity K and dimensionless load b=W s, exact algebraic deltaJ=K^T W^-1 delta b, bound sum_i |K_i| eta_i/W_i if eta_i encloses error to chosen reference. Need actual K and certified arithmetic error before calling this a receiver certificate. Full temporal ledger retains stage insertions separately. Next tighten integration via derivative/Taylor or Bernstein interval quadrature and adaptive subdivision, retain original source normalization and exact endpoint collar, compare against existing oracle. Local full production solver still absent (extracted stage only), earlier LXIX four diagnostic checkpoints available. No new propagation, native restart or receiver parity acceptance. LXII–LXIX previous scope unchanged. LXXII rational enclosure implementation and finite containment PASS, sharp useful precision, native float mesh weld, Bishop kernel, consumer transport and physical convergence OPEN. No CI initiated.


## Maximum-cut LXXIII–LXXV — constructive Taylor source adapter (2026-11-20)

Reuse audit: BalabanClayCommonTaylorRemainderToEnclosureExact (ordered remainder transport, analytic premises separate), BishopNegativeExponentialQuarticBracketExact, BalabanP33BishopTaylorPolynomialFormExact, Docs/proofs/AnalyticKoenigsComplexCompositionMajorant20261110.md (positive finite Cauchy-composition majorant, not itself kernel acceptance). No duplicate general Agda Taylor calculus. New executable source-specific adapter scripts/check_f8_lxxv_taylor.py commit cc89ce5e9bcfe909329ebde1a2b5c16e11d251ea, local/remote Git blob 041f88a4c2b2a7880dd4a9e9c36ea4f8685b67cd. Imports existing rational enclosure evaluator d80c9dcba76cd7480d99be21925bf70aed5018d2 and compares original weak source 69f35c6569667034214035d810dee06251a6d2ad; both local hashes match. 

Panel coordinate u=c+Rw, R=(1-c)/2; recursively halve until r=(y-x)/(2R)<=1/8. A=1/(1-u²), A0=1/(1-c²); nonnegative reciprocal coefficients by two-term recurrence. E=exp(-(A-A0)) coefficients by nE_n=-sum_j j A_j E_(n-j). Truncated rational convolution degree N=20 for A^8, E, TT polynomial, radial measure and hat. Scalar prefactor exp(1-A0) enclosed by existing expneg. Positive majorant at s=1/2 uses A(s)^8 exp(1+A(s)-2A0), absolute TT polynomial, radial power and absolute hat coefficient sum. Geometric tail bound (r/s)^(N+1) times this full majorant; integrated error <= panel length times bound. Exact integration of even coefficients, odd terms cancel. Existing .99 endpoint collar retained. Classical power series identities justify the mathematical enclosure; original Bishop/Agda identification still OPEN. 

Executed exact script locally with timeout 90s, exit 0. A/C 39/39 floating source load membership PASS, exact decimal mesh assumption. Maximum widths for ell 0,2,4 respectively A 6.011287064899487e-6, 1.24824695125466e-5, 3.7028626733927685e-7; C 5.764663747625376e-6, 1.1998844710515312e-5, 3.5740422526794345e-7. Compared to prior LXXII reported maximum widths, improvement roughly 4.7e7–1.1e8 fold. No per-node nesting against LXXII rerun, no receiver sensitivity/error acceptance, no finite-precision native mesh or floating evolution certification. Original production emitter unchanged. Next: tighter degree/panel budget and exact moment compatibility, native adjoint coefficient sensitivity and weighted enclosure consumption; complete native propagation and checkpoint restart gates remain OPEN. No CI or Agda execution.


---

# F8 P0 INTEGRATED EXECUTION DECISION — supersedes rolling microcuts (2026-11-23)

**STOP SMALL BITES.** XCVI–XCIX and all earlier symbolic/truncation diagnostics are evidence and controls, NOT four more separate next steps. User directive is a construction/geometry-FIRST maximum cut, using the original AdS5 / induced 3+1 background, the already-existing matter and source, the ACTUAL original F8 production solver, and the repository's independently constructed action-Galerkin and weighted SBP comparators. No GitHub CI. Do not report finite results as continuum or detected gravitons. This is the CURRENT controlling roadmap for the next substantial packet; earlier sections' many individual NEXT lines are superseded.

## 1. Source owner reconciliation; don't redo solved geometry

At audit: default master c36aa4a423091063bb3741cc74044726279b47c4 and PR #1527 open/draft at d1c49e12fe5bf4dcbe2405f0428c155047f3f2c1 before new packet. Compared with master, PR #1527 had diverged: +55 / -~85,260 commits, 26 changed-file entries (mostly new source consumer scripts and canonical roadmap). The PR title/body still describe XL/YM S3 while branch contains later source P0. DO NOT force-update or blind merge a very old PR branch into master. Confirm exact source blob at actual final head; if later integrating to master, use a clean master-based transplant of only still-new accepted files.

PREVIOUSLY PAID in different original owners:
- Original 5D Einstein-AdS source, original moving a(t)=t induced 3+1 metric, all 16 background Israel components, conserved prescribed compact TT matter and source physical-clock pulse: Docs/physics/KSW668BraneBulkLevinStringTSFVMaxCut20261115.md and original scripts/ksw668_f8_tt_multipole.py / ks...fv_source_flux.py. 3+1 is a SELECTED brane embedding, not a unique emerging dimension from finite cones; distinguish KK projection and induced path cone.
- Original geometry-derived independent action momentum p=U_T-vU_y and q=U_y, finite-element variational and two-stage Gauss reference: Docs/physics/KSW668F8YMNSNonlinearCurvatureRoadmap20261120.md; scripts/check_f8_geometry_variational.py, check_f8_geometric_constraints.py, check_f8_gauss_action.py, check_f8_gauss_trace_diagnostic.py. This reference has physical constructor and finite test records but no same-source complete G1–G6 proof.
- Full original source-lifted weighted SBP and radial hierarchy: Docs/physics/KSW668F8FullCoupledWeightedSBPEnergyMaxCut20261115.md, scripts/ksw668_f8_full_coupled_weighted_sbp_energy.py, ks...characteristic_constraint_maxcut.py, ks...radial_sobolev_hierarchy.py. Homogeneous mode4 semidiscrete E'< =5E, sourced lift E'< =6E+0.5||F||² recorded under premises; fully discrete coupled SSPRK3, forced dynamic Q and pointwise second-derivative receiver H4+epsilon estimates OPEN.
- Historical original original-FV LV/LVI complete production, separate-process checkpoint runs and medium/time-halved full producer JSON exist on master at their OLD exact solver blobs. LXIX A0/A1/C0/C1 96 signature is an extracted-stage diagnostic, not a complete current weak-source native replay. LXXXVII native runner/checker and XCIV original terminal NPZ consumer exist on #1527. Far Weyl/field nonzero violates continuum compact-source null at far (by coordinate support bound) but its finite numerical mechanism is NOT proved.
- XCVI–XCIX already establish original weak SAT Q boundary residual, source flux normalization PASS, artificial 1/v projection risk, regular W/A characteristic variable map, unclosed moving v_T trace, and manufactured H=z4 one-sided O(dy) truncation. A nonzero discrete Q alone does NOT prove wrong continuum geometry. Do not re-derive these again.

## 2. One reproducible local ORIGINAL execution packet

Source-owned new script scripts/run_f8_p0_integrated_local.py consolidates existing owners, no surrogate solver, and writes separate atomic JSON ledgers and logs. Invocation from a literal checkout of this PR, with master source files present:

    python scripts/run_f8_p0_integrated_local.py --phase preflight --timeout 90
    python scripts/run_f8_p0_integrated_local.py --phase native --timeout 90 --max-rounds 64
    python scripts/run_f8_p0_integrated_local.py --phase compare --timeout 90

Preflight fails closed on five original producer Git blob identities and four historical source receipt files. It runs the **existing** original coupled characteristic constraint, full weighted SBP energy, same-action geometric constraints, local Gauss construction, radial Sobolev, XCVI–XCIX moving SAT/trace, XCII/XCIII cones, and XCI/XCV source-backed full producer readout decompositions. Each module exits 0 to PASS within a 90 second local budget; missing/timeout/unsupported imports remain BLOCKED/FAIL. This meta-runner has not been executed from an exact checkout in this container. GitHub commit/readback and independent local SymPy controls do not substitute for it.

Native phase delegates only to existing original run_f8_lxxxvii_native_96_local.sh and source-version-locked run_f8_lxix_native_source_matrix.py, cooperative 90s maximum slices, original NativeCheckpoint, A0/A1/C0/C1 two meshes, two source representations, near/far 3 physical ell modes x E4/E5 + tangent channels = 96 SIGNED original production outputs. Run may take many bounded slices; it is explicit opt-in on a machine with the actual checkout. Fail on changed source/checkpoint fingerprint, missing producer JSON, failed native exit, or full signed historical comparison. Historical parity is DIAGNOSTIC, not a physical certification.

Compare phase checks all 96 outputs and optionally authenticated old full-native NPZ against exactly corresponding historical original FV full producer JSON via XCIV. Do not pass new weak-source checkpoint into old FV NPZ consumer. Missing NPZ is NOT_RUN, not forged. No output from this entire runner can mark physical far null, fully discrete coupled energy, independent continuum convergence, source-to-physical detector or Agda kernel PASS. Source pins are identity checks, and genuine future source changes need a separately recorded source version migration.

## 3. Actual large research weld D1–D5: matched geometry and SAME physical state

Compare three ORIGINAL construction alternatives, NOT three different physics models:
A) native normal_order=3 independent characteristic SAT U/P/M;
B) native normal_order=4 AdS weighted source-lifted SBP;
C) existing action-derived U, canonical momentum, q Galerkin/Gauss, where q is constructed from field rather than free independent characteristic drift.

All three must use IDENTICAL moving AdS5 (T=F(t), z=1/t, v=b_T, physical brane induced -dt²+t² dx_i²), identical real TT compact prepotential and original radial effective d=3/7/11, identical pulse, physical Israel source, near/far event clock, radial/normal domain and outer boundary assumptions. Keep source FV and separate weak-source intervention as explicit contrasts with their own source distributions; matched global moments do not imply same source or same receiver.

At EVERY original substage and physical checkpoint, retain signed:
- U,P,M or U,W,q, including two normal wall layers and 4 radial interpolation nodes; same-object Q=(P-M)/2-DyU, Q_T and original v_T, boundary physical G-A, upper incoming P_N, source work and strong wall trace;
- full weighted z^-3 radial+normal moving energy, negative wall squares, source-lift work, constrained trace and original flux, including all sign and source/clock incidence;
- raw H, radial H_r/H_rr, temporal H_T/H_TT and normal jets BEFORE intrinsic 4D and projected 5D electric Weyl reconstruction, at physically fixed near/far receivers;
- true source cone support, forbidden far-field amplitudes and independent propagation/outer-boundary effects. Do not confuse a point cone with full compact spatial and temporal source.

Acceptance requires 3+ independent radial resolutions, 3+ normal resolutions and 2+ independent time step values, common physical event/source and negative source-off controls. Measure nonzero far H BEFORE Weyl and quantify decay/error as mesh changes, not only parity of 96 signed numbers. To promote physical both-Weyl pointwise trace require a FULL moving forced/constraint-compatible energy and H4+epsilon trace/control, with source-to-Weyl and forbidden exterior source support bound, not merely first-order E or polynomial manufactured identities. Reuse existing formal FIO/microlocal and radial Sobolev owners rather than invent a new signature/369 geometric equivalence.

## 4. One STOP/GO gate table

| Gate | Definition | True status |
|---|---|---|
| D0 already-owned source/geometry | 5D metric, induced 3+1, 16 Israel, TT prescribed source and clock | HISTORICALLY ESTABLISHED, do not reprove |
| D1 compatible full construction | same-source native SAT/SBP/action, including dynamic Q, flux, strong trace | OPEN |
| D2 full discrete control | forced coupled time-dependent energy, SSPRK3/Gauss stability and trace error | OPEN, partial semidiscrete source-lift PASS |
| D3 current 4-way native | A0/A1/C0/C1 original source code, authenticated checkpoints, complete signed 96 outputs | OPEN; old FV-only LV/LVI production separately completed |
| D4 actual same-field receiver | independent normal/radial/temporal original jets, near/far H/E4/E5 with provenance | OPEN |
| D5 causal + continuum | forbid far source signal, quantitative uniform exterior error, 3x spatial axes + independent time | FAIL/OPEN |
| D6 physical theorem/experiment | true tensor retarded Green, source-to-detector coupling, pinned Agda/TOE and empirical evidence | OPEN |

**STOP additional new numbered microcuts until a genuinely integrated source-local execution closes or materially falsifies a D1–D5 gate.** The next honest output should be a consolidated signed test ledger from actual local original runtime and a single geometry-compatible source-to-Weyl comparison, not another tiny exact identity. Original authors / attribution preserved (Caldwell–Langlois, Thorne, Israel and other cited physical/variational/SSPRK3/SBP prior work).


## Post-integration correction — focused master-based draft PR #1547

The governing P0 packet was TRANSPLANTED from original draft #1527 into new draft PR #1547, head 0b47f11b68b4f39abc2607d0e845ab05b8361f6b, branched from master c36aa4a423091063bb3741cc74044726279b47c4. This is the integration vehicle, not a second replacement F8 mathematics owner; preserve source ownership and attribution to original #1527 and merged master sources. Why: old #1527 showed +55/-~85,260 history divergence and lacked several master-owned action/SBP modules in a clean old-branch checkout. New #1547 has all 13 named preflight check modules **present**, and all five production-critical original script blobs byte-identical to current master. The original solver itself and canonical master action/SBP owner modules are UNMODIFIED on #1547; the integration contains only selected new controls/runner/consumer and this roadmap. Run phases from #1547 checkout, not the missing-module old #1527 branch. No complete integrated phase executed here; structural source availability and byte identity are not the same as local runtime PASS.

Guard interpretation: the three-phase local runner and all old receipt/source controls are integrated **readiness**, not successful execution of original new A0/A1/C0/C1 four-way nor causal-null, driven source-to-Weyl or three-grid continuum proof. Keep draft status until local full checkout execution, original native authenticated checkpoint and physical D1–D5 gates have actual evidence. Do not push the diverged research tree into master blindly.


## P0 integrated D1 construction advance — native radial/action same-carrier weld, 2026-11-24

This is a single integrated construction deliverable, not another numbered microcut. Original mode3/mode4 native F8 has three physical multipoles ell=0,2,4, distinct native finite-volume radial L_d for d=3,7,11, native weighted radial shell volume V_d, and exact conservative compact FV source cell loads. The existing master action/Gauss owner instead uses separate sine-radial k_n=n*pi/R, source spectrum(n,R) and k². These are not identical discrete carriers, so previous broad instructions to compare existing action vs native outputs as though they used identical sources were INSUFFICIENT. Preserve prior master geometry and 3+1/AdS5/Israel source results; this is a missing operator-level D1 weld, not a new physics model.

New source-owned consumer on focused master-based draft PR #1547: scripts/check_f8_p0_native_radial_action_bridge.py, integrated into the canonical source-pinned preflight runner as original-native-radial-action-bridge. It reuses the exact original master modules check_f8_geometry_hp.FE for weighted moving normal hp M,C,K, ksw668_f8_full_coupled_weighted_sbp_energy.radial_stiffness for the d=3/7/11 native FV L_d,V_d, ksw668_f8_fv_source_flux.exact_cell_averages for the actual compact source, and original F(t), b=1/t, v=-1/sqrt(1+t²), v_T=t³/(1+t²)² and time pulse. No original solver, source, action, SBP or canonical brane implementation was overwritten.

Canonical semidiscrete assembly, all physical modes and radial indices: m=M W-v C U, W=U_T, U_T=M^-1(m+v C U), m_T=-v C^T W-(1-v²)K U+M L_d U+F_lower+F_upper. Original physical wall source F_lower=-b^-3 amp(T) times exact original compact FV cell load, F_upper=-(b+y_upper)^-3 W_upper. Positive mass-weighted radial energy E=1/2 sum_{ell} V_d [W^T M W+(1-v²)U^T K U-U^T M L_d U]. The exact moving finite-dimensional forced-energy identity partitions E_T into: source/outer work W^T F, moving mass -1/2 W^T M_T W, moving momentum v_T W^T C U+v W^T C_T U, moving normal stiffness (1-v²)/2 U^T K_T U-vv_T U^T K U, and moving radial mass -1/2 U^T M_T L_d U. This is an original-geometry SOURCE-WORK compatibility equation, not a continuum/high-regularity bound or evolved native solution.

Local test on 2026-11-24, no CI: original-function-equivalent standalone numerical source for the original FE / native radial / compact FV implementations (temporary local copies, NOT an exact literal checkout) and new action bridge executed with NumPy/SciPy/SymPy at the source-active clock T-F(1)=.0325, t=1.0233821649028472. Three different radial/normal grids (FE elements, radial points, dr) = (4,9,.008), (6,12,.006), (8,15,.004); both compact source ON and OFF, SIX tested canonical energy identities. Maximum absolute independent centered-difference minus analytic full moving-energy E_T residual 9.718354593291068e-15. Source-ON wall/outer work for the three meshes: +0.0009155359241501222, -0.0027424153686534678, -0.018304984029620348; OFF contains only outer absorption. Native weighted FV radial symmetry/positive stiffness and source zero beyond spatial support checked all three grids. Local script SHA256 5f60b6598fdcb762e9f7a1f02ac026821beff56d31dbbcf1292485a994c26c88; corresponding GitHub source is 5545 bytes. Local execution used source-equivalent support modules instead of literal imported master modules, so the full exact checked-in script still needs replay from a clean #1547 repo checkout before calling it literal-GitHub-head PASS.

Crucial scope: D1 source/operator interface has an actual six-case finite forced-energy result; full same-source continuous-time evolution comparison of original mode3 / mode4 / radial-native action is OPEN. D2 fully discrete stability/constraint and H4-plus trace OPEN. D3 current native A0/A1/C0/C1 96-signed end-to-end OPEN. D4 actual evolved wall and receiver jets and both Weyl OPEN. D5 original far causal-null FAIL and independent mesh-continuum OPEN. D6 formal/physical OPEN. Do NOT promote this finite energy identity or prior sine-mode action numerics to full physical source-to-receiver correspondence.

NEXT SINGLE BIG CUT: use this radial-native action bridge in the existing Gauss/banded evolution owner, while retaining exact physical clock/Israel source/outer conditions; execute forward on same compact 3-mode FV source for the original mode3, mode4 and action formulations. Record state/energy/strong trace and near/far field jets before E4/E5 on at least three independently refined radial/normal meshes and two dt, with source-off and far-cone null negative controls. Preserve all historical master and PR #1527 prior art and original attribution; no GitHub CI. Do not resume serial XC microcuts.


---

## Latest-PR donor review and integrated native-FV Gauss forward (2026-11-24)

**This is one integrated D1 construction step, not a numbered microcut.** The connected GitHub recent-PR scan included #1550, #1549, #1548, #1547, #1546, #1545, #1544, #1543, #1537, #1524, #1520, and #1519. Reuse only genuine same-source, same-operator donor interfaces.

### Relevant owners and boundaries

- PR #1520: original F8 full moving-AdS coupled weighted-SBP energy, source lifting and both-Weyl failclose. It expressly distinguishes physical AdS normal z from 3D radial distance r; eigenvalues of weighted FV L3/L7/L11 are NOT Kaluza-Klein masses. Reuse source-conservative shell weights and energy, not unsupported modular or KK interpretations.
- PR #1543: explicit original-source/physical-endpoint/trace proof boundary, useful as an acceptance discipline; NS R568 trace does not prove an F8 Weyl trace.
- PRs #1537 and #1519: actual signed source-work and storage-ledger negative controls in unrelated physics. Borrow ledger discipline only, not motor/Filsinger sources.
- PR #1524: stale pass marker, dirty-source and absent dependency fail-close controls. Adapt F8 acceptance without GH CI.
- PR #1544: original Wilson source normalization is separate SU(N) physics; not an Israel-source substitute.

### Native FV radial eigenbasis into ORIGINAL action FE and Gauss-2

New focused PR #1547 source-owned script scripts/check_f8_p0_native_radial_gauss_forward.py imports the already committed scripts/check_f8_p0_native_radial_action_bridge.py and existing master hp normal FE / native radial FV / exact compact source owners. For each ell=0,2,4 with d=3,7,11, symmetrize the ORIGINAL radial finite-volume matrix S_d=-sqrt(V_d) L_d / sqrt(V_d). Compute S_d R_d=R_d Lambda_d and B_d=V_d^(-1/2) R_d. Identities B_d^T V_d B_d=I and L_d B_d=-B_d Lambda_d are checked. Project the ACTUAL compact FV source to modal amplitudes by B_d^T V_d source_d, and reconstruct it. This preserves the native radial source and radial operator exactly as finite-dimensional linear algebra; Lambda_d is NOT a KK mass, and the sine-basis action donor was not silently substituted.

Each radial eigenmode uses the EXISTING moving hp normal AdS matrices M(T), C(T), K(T), canonical state [U,m], physical Israel pulse, absorbing outer normal force and original F(t) clock. It is evolved with the two-stage fourth-order Gauss-Legendre collocation at the correct physical stage clock positions. The script checks weighted orthogonality, native-source modal reconstruction, original native-vs-modal first-order RHS parity, finite energy, active compact source and exact zero initial/source-off trajectories.

### Local source-equivalent forward evidence, NOT full production

An equivalent local numerical implementation was executed with original-owner-equivalent local FE, radial FV and compact source functions, not a literal byte-identical checkout. There are 3 radial/normal grids (FE elements,Nr,dr)=(2,9,.008),(3,12,.006),(4,15,.004); four dt=.004,.002,.001,.0005 on each; source-on/off = 24 separate short trajectories. Observation is T-F(1)=.068, t=1.049864423456425 after the original .065 pulse, not the physical t=12. All 12 source-off histories remain exactly zero and all 12 source-on states are finite/nonzero with positive canonical energy. Original native versus transformed modal RHS maximum absolute mismatch at the 3 grids: 1.2302e-10, 1.6871e-10, 5.1557e-9. These small absolute errors reflect weighted eigenbasis roundoff, not proved uniform operator norm stability.

Unweighted source-on field norms at dt=.004/.002/.001/.0005: Nr9 [1.7766345,1.8432598,1.8475571,1.8478285]; Nr12 [1.9137754,1.8494727,1.8466628,1.8464896]; Nr15 [6.9776086,11.7706580,12.1247825,12.1475977]. Finest dt field-norm differences (.001 versus .0005): .00027135, .00017326, .02281512. These are not spatial convergence results. The 3 truncated radial boxes have distinct physical outer radii and DO NOT include the original near/far receivers. The raw field norms are not radial V_d-weighted. Source-on canonical energy at finest dt: 4.4190816e-5, .00534532895, .00242557829. Independent local evidence saved as f8-p0-latest-pr-native-gauss-forward-evidence.zip. The exact committed module has not been executed byte-for-byte against a full repository checkout. No CI.

### Updated large-bite STOP/GO boundary

D1 has materially advanced: SAME original d=3,7,11 FV radial source/operator plus moving canonical action, source-work ledger, and ACTUAL Gauss-2 source-on/off short-pulse forward evolution across 3 grids and 4 times. D1 remains OPEN for the original mode3/mode4 versus action comparison at the same physical full radial/normal domain. D2 fully discrete forced stability and higher trace regularity OPEN. D3 original current FV/weak A0/A1/C0/C1 native 96 signed outputs OPEN. D4 t12 same-state physical wall jets and both Weyl OPEN. D5 out-of-cone far null FAIL/OPEN and independent fixed-domain convergence OPEN. D6 retarded Green, Agda/TOE and detector OPEN.

NEXT ONE substantial cut: extend this existing radial-native Gauss construction to fixed original t12 receiver-containing radial domain, compare ORIGINAL mode3/mode4/action across source-on/off and independent dr/dy/dt while keeping outer boundary and source distribution fixed. Retain stagewise Israel residual, Q, dynamic moving trace, canonical source/energy work, radial/temporal/normal jets, both electric Weyl and far causal support; do not add more isolated identities or promote short-pulse tests as detector results.


---

## F8 P0 — same-domain physical t12 action/Gauss acceptance, 24 November 2026

**This section supersedes the prior short-pulse-only NEXT step, not the original source owners.** Keep the original moving AdS5 induced 3+1 metric, 16-component background Israel, conserved compact TT three-multipole source, source FV and weak source as distinct, original mode3/mode4 and master action/SBP owners unchanged. No GitHub CI or physical detection promotion.

### Three original-geometry execution blockers exposed and corrected

1. The native radial Gauss forward inverse-clock function was hard-coded to t in [1,1.3], literally preventing the physical t=12 receiver. Corrected with a monotone, guarded bracket expansion in scripts/check_f8_p0_native_radial_gauss_forward.py (commit 86e52245). The source-equivalent local solver reached t=12.
2. The radial action bridge asserted absolute max|V L-L^T V|<1e-8. At fixed r_outer=3, mode d=11 gives dr=.03 absolute residual 2.4680048e-8 but *relative* 6.2623e-15, and dr=.025 absolute 3.2829121e-8 / relative 6.9441e-15. This was a false positive caused by strong shell-volume scale, not demonstrable weighted-adjoint failure. Replaced with max relative weighted-operator norm tolerance 5e-12 in scripts/check_f8_p0_native_radial_action_bridge.py (commit 9f3c6d2b). Do not weaken source provenance.
3. The original short Gauss loop rebuilt identical normal FE stage matrices per radial eigenmode. New batched native FV modal Gauss reuses each original physical-clock normal stage and solves across modal sectors; one-step source-equivalent batched/serial original code parity max abs 1.734723475976807e-18. The transformation still preserves original V-weighted d=3,7,11 FV radial operators and compact TT source.

### Actual fixed physical domain and completed local executions

Use physical radial [0,3.0] FIXED for all radial refinements, normal y=[0,2.1], compact source eps=.04, pulse in original bulk time span .065, original t=12 receiver at r_near=2.537365760961938 and r_far=2.649365760961938. Original same-function source / moving geometry, FE order p=1 normal, two-stage Gauss and shell-weighted radial eigendecomposition; no sine-basis substitution. Output H_ell=(r/eps)^ell cubic_interpolated U_ell at y=0, NOT original E4/E5 or continuum pointwise Weyl.

Local source-equivalent stand-alone experiment was actually executed using owner-equivalent original FE/FV definitions in the workspace, NOT a literal full Git checkout: **18 source-ON physical t12 runs plus 18 exact-zero source-OFF controls**. Coarse domain runs 12 on +12 off: ne=2 or 3, dr=(.04,.03,.025), dt=(.04,.02). Fine-domain runs 6 on +6 off: ne=2, dr=(.010,.008,.006), dt=(.02,.01). All t=12, finite state and positive canonical energy, original near/far readouts recorded; new integrated GitHub exact-head 12-on/12-off test file was committed but itself has NOT been byte-identically replayed in full Git checkout.

| original dr, ne=2 | signed far H, dt=.02 | signed far H, dt=.01 | canonical energy at dt=.01 |
|---|---:|---:|---:|
| .010 | -3.8087285637444256e-5 | -4.420058967621054e-5 | .010842517544701915 |
| .008 | -4.550797764901593e-6 | -6.872380654264162e-6 | 4.8347879589291095e-5 |
| .006 | -2.35554463868019e-5 | -2.852541638691038e-5 | .004043773002742062 |

Coarse ne=2 and dt=.02 far H: dr=.04 +1.0780187980229226e-7; dr=.03 +4.962381060345421e-8; dr=.025 +5.17617002724364e-5, with energy increasing similarly. Keeping the physical radial domain fixed removes the previous varying-outer-radius confound, but field H and energy remain highly NONMONOTONE across dr and dt. The fine grid dr=.006 at dt=.01 has positive near H +1.560239528970314e-5, while dr=.01 and .008 near H are negative. This is NOT any claimed uniform continuum convergence or detected propagation.

### Independent source-cell check, not an arithmetic-blame shortcut

New scripts/check_f8_p0_compact_fv_source_independent.py compares the original exact FV primitive cell integrals with independent 200-point Gauss-Legendre quadrature of the ORIGINAL differentiated compact TT multipole functions and exact d=3,7,11 shell weights. The independently executed local equivalent comparison on dr=(.04,.03,.025,.010,.008,.006) matched within worst max-cell relative discrepancy ~2.00838e-8 at dr=.006. At dr=.025 the discrepancy is ~1.0464e-13 despite huge source coefficients. Thus the strong mesh dependence of the highly differentiated compact source is NOT explained by an incorrect primitive antiderivative. At these dr, only roughly 2-8 finite-volume source cells carry the eps=.04 support. Exact FV integration alone does not guarantee sufficient resolution or a mesh-uniform evolution error estimate.

### Integrated code/acceptance and one next large original-physics gate

PR #1547 retains master-based source ownership: new scripts/check_f8_p0_native_fixed_domain_gauss_receiver.py (batched two-stage Gauss, physical t12 near/far H, 3 fine dr x2 FE ne x2 dt x source ON/OFF); new scripts/check_f8_p0_compact_fv_source_independent.py (independent source quadrature); both are registered in scripts/run_f8_p0_integrated_local.py. No changes to original mode3/4 solvers. These committed scripts need literal source-head execution on a clean PR checkout before a repository-byte acceptance claim.

D1 partial: original-carrier action/Gauss full physical t12 H field trajectories measured locally under a fixed radial domain; THREE-WAY original mode3/mode4/action same-state comparison OPEN. D2 fully discrete forced stability, strong trace, uniform high regularity OPEN. D3 current A0/A1/C0/C1 96 signed original native output and checkpoint replay OPEN. D4 action near/far H measured, but independent time/radial/normal jets and original both-Weyl E4/E5 OPEN. D5 far source continuum causal null still FAIL for finite native and independent action discretizations; no uniform convergence. D6 physical tensor Green, Agda/TOE and detector OPEN.

**Single large next action, no XC microcuts:** run original mode3 and mode4 checkpointed original compact TT source on the SAME physical radial/normal domains and matching clock/receiver, compare their raw U/P/M vs action U/W/q and Israel flux, source work, H,Hr,Hrr,Ht,Htt, and signed E4/E5; independently refine 3 radial/3 normal/2 dt without moving boundaries of the study. The action normal p=1 test is not enough for second derivatives and must include p>=3 or independent high-order trace reconstruction. Resolve far field causal-null with an actual bound or measured decay before physics claims.


---

## F8 P0 — governing native-domain correction and partial original-parameter receiver test (2026-11-24)

**This newest correction supersedes the previous 0..3.0 / 0..2.1 fixed-domain examples as the governing native-comparison baseline.** The original current native four-way driver on master uses r_outer=3.01, y_outer=2.01, dr=.008 or .006, dy=.012, dt=.0012, eps=.04 and final_t=12, and original native propagate enforces dr<eps/3. Thus earlier dr=.04/.03/.025 action reference studies and fixed r_outer=3.0, y_outer=2.1 tests are only independent construction diagnostics, NOT parameter-matched original native comparisons. Explicitly preserve this falsification of the earlier broad same-domain wording.

### Source-owner patches on focused draft #1547

- Corrected original action FV radial shell V L=L^T V scale guard: old absolute 1e-8 falsely failed for high-d volumes; new normalized 5e-12 weighted-operator tolerance (9f3c6d2b).
- Corrected Gauss inverse F(t) bracketing so t=12 is reachable, instead of short-pulse-only [1,1.3] (86e52245).
- Added batched original FV radial eigenmode Gauss solver and original t12 near/far wall H, plus independent exact-cell FV-versus-200-node direct profile quadrature, registered both in integrated local preflight (335020f4, 9985e188, 5e8563a6). The batched-versus-serial identical one-step local error was 1.734723475976807e-18.
- **Updated the committed receiver diagnostic again** to requested radial outer r_outer=3.01 and normal outer y_outer=2.01, ne=(2,3), original native-admissible dr=(.012,.008,.006) and Gauss dt=(.004,.002) (aae91d7b). Affine scaling of existing hp FE normal geometry changes h, quadrature weights, physical node locations, and derivative shape functions consistently, without overwriting master FE. Actual radial terminal nodes follow original ceil(r_outer/dr)+1 convention.

### Locally completed genuine-original-parameter receiver experiments, limited scope

Local code uses original-source-equivalent FE, conservative exact FV radial d=3/7/11 and original compact TT source definitions, not byte-identical repo-head producer checkout. At actual moving-clock t=12 and physical near/far receivers on original r_outer=3.01 / y_outer=2.01 requested domains, source-on action/Gauss and exact-zero source-off were completed for SIX ne=2 runs (three dr x two Gauss dt), plus ONE ne=3,dr=.012,dt=.004 run. The rest of ne=3 sweep was interrupted: status PARTIAL, not 12/12 PASS. p=1 normal FE is not original mode3 SBP and dt=.004/.002 is NOT native SSPRK3 dt=.0012.

| native-admissible dr, ne=2 | signed far H, Gauss dt=.004 | signed far H, dt=.002 | terminal canonical energy at dt=.002 |
|---|---:|---:|---:|
| .012 | -1.004328012605307e-5 | -1.0044714576002205e-5 | .0013586261017759034 |
| .008 | -7.629811140861025e-6 | -7.637048964199147e-6 | 4.4450730517766785e-5 |
| .006 | -3.192877967284985e-5 | -3.194620460497012e-5 | .0042438099726308225 |

At ne=3,dr=.012,dt=.004, signed far H=-1.4065117389510964e-5, canonical energy=.0017562153353360651; the matched ne=2,dr=.012,dt=.004 far H=-1.004328012605307e-5. Changing normal FE resolution also changes amplitude. The dt pair differs relatively little at each fixed dr while the far H and energy strongly change across radial dr, supporting a construction/source-resolution research priority but NOT identifying a unique cause.

### Independent original FV source control

Independent 200-node quadrature of the source-defined fourth-derivative TT profiles reproduces exact primitive FV cell averages on dr=(.04,.03,.025,.01,.008,.006) to maximum normalized cell discrepancy ~2.00838e-8. Sharp, alternating source coefficients (for example dr=.025 ell=2 source maximum 2585.18 versus dr=.03 18.54) are present in independent quadrature; they are NOT proof the analytic FV antiderivative is wrong. Coarse dr=.025 violates original native source resolution guard and is a diagnostic only. The compact differentiated source is under-resolved on modest radial grids. Proving evolution convergence requires a native source sampling/regularity and exterior cone bound, not just exact cell integration.

### D1-D6 acceptance after this actual integration

D0: original selected brane/AdS5/Israel/TT construction established, unchanged. D1: compatible native-FV radial action/Gauss forward to true original receiver time and original requested outer boundaries demonstrated in finite local source-equivalent tests, but original mode3/mode4 on same states and all original normal data OPEN. D2: fully discrete forced action/SBP stability, source trace and uniform H4+epsilon regularity OPEN. D3: current original FV-versus-weak A0/A1/C0/C1 full 96 signed authentic native outputs OPEN. D4: near/far action wall H only, no independent physical H_r,H_rr,H_t,H_tt, Israel wall jets and both Weyl E4/E5 OPEN. D5: continuum forbidden far source response still FAIL for finite original FV and action methods, not a demonstrated convergent physical signal; three-grid spatial/normal/time convergence OPEN. D6: tensor Green/Agda/TOE/detector OPEN.

**The next one large bite** remains the original native mode3/weighted SBP mode4/action-Gauss same-source full-time comparison with original domain and physically consistent dr,dy,dt: extract source-pinned full U/P/M or canonical m and q at real t12 near/far, record same-stage Q, Israel G-A, weighted energy/source work and independent radial/temporal/normal jets, E4/E5, source-on/off and exterior causal null. Do not re-label these finite action H results a same-state original native Weyl acceptance. No CI or duplicate physics branch.

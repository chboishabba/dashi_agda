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

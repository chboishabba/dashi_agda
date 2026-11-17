# PV 369 → GaAs [111] SALC / Kane: exact finite cut and source-matched physical gates (17 Nov 2026)

**Owner:** draft [DASHI PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523). **Attribution:** original 369 atomic Fourier and p-shell owners stay unchanged; source material physics credited to Vurgaftman/Meyer/Ram-Mohan, Kane, Koster, and cited quantum-dot experimenters. **Verification:** 39/39 local SymPy symbolic and numerical assertions pass on a parallel equivalent script. The version committed at `scripts/check_gaas_111_salc_kane_exact.py` has not been executed from a GitHub checkout; Agda code is *not kernel checked*. Neither a real material-to-369 map nor a solar conversion gain is established.

## Crucial correction: charge permutation is not the spatial C3 action

Original atomic owner: `DASHI/Physics/Chemistry/AtomicPeriodicTable369MagneticC3PhysicalRealizationExact.agda`. It intentionally distinguishes (i) spatial rotation eigencharacters `rotationPhase m = ω^m` from (ii) `chargePositiveStep`, an abstract sector permutation. `AtomicPeriodicTable369C3FourierSpatialRestrictionExact.agda` proves their finite Fourier relation, not equality in the same basis.

Spinless GaAs zincblende `T_d` valence `T_2 (Gamma15)` restricted to a chosen [111] `C3v` subgroup decomposes `A1 + E`. Choose Cartesian basis `(X,Y,Z)` with real [111] threefold rotation `R: X→Y→Z→X`. `ω=e^{2πi/3}` and the columns of

```
       1   1    1
U=1/√3 1   ω²   ω
       1   ω    ω²
```

are `a1,e+,e-`. Then `U†U=I` and `R U= U diag(1,ω,ω²)`. A compatible `C3v` mirror `W: Y↔Z` exchanges `e+↔e-`; `WRW=R⁻¹`. These are exact complex identities checked by SymPy.

**False equation:** `R mapOriginalP(m)=mapOriginalP(chargePositiveStep(m))` with `mapOriginalP(m)` a trigonal SALC eigenvector. Spatial rotation returns **phase times the same state**, whereas charge step switches the abstract m label. The direct equation fails. This was incorrectly posed by the earlier `GaAsAtomic369ToKaneWeld` field. It has been amended to require separately:

- `crystalC3Rotation(mapOriginalP(m)) = phaseMultiply(P.rotationPhase(m), mapOriginalP(m))`;
- `chargeSectorTransport(mapOriginalP(m)) = mapOriginalP(P.chargePositiveStep(m))`.

The separate phase action must preserve identity and phase multiplication. The new finite owner `Atomic369GaAs111TrigonalCharacterExact.agda` proves exact 3-state character correspondence and both actions separately using existing phase constructors. That is **only a representation-level label correspondence**. The full `GaAsAtomic369ToKaneWeld` remains uninhabited pending actual Bloch/amplitude witnesses, measured oscillator strengths and device output.

## Momentum and photon-polarization convention

For the spinless isotropic Kane tensor `<S|p_j|orb_i>=p δ_ji`, `E_P=2p²/m₀` (when `p` is physical linear momentum; alternatively `P_0=-iħ p/m₀`, `E_P=2m₀|P_0|²/ħ²`). At `E_P=28.8 eV`: `p=1.449709e−24 kg m/s`.

The unitary `U` yields a rotated polarization/valence matrix `U†(pI)U=pI`. So:
- one fixed **Cartesian x** photon-polarization component into *each* normalized SALC has squared momentum `p²/3=m₀ E_P/6`;
- one **matched normalized trigonal polarization** into its corresponding SALC has squared momentum `p²=m₀ E_P/2`;
- all 3 valence states / 3 polarizations have total squared momentum `3p²`, invariant under `U`.
- Circular-polarization **handedness signs** depend on whether the complex electric-field contraction is conjugated, whether the process is absorption or emission, and chosen axis. Do not assert a fixed σ+/σ− correspondence without defining convention.

This is **basis rotation and spectral redistribution**, not increased integrated oscillator strength. In particular, the *same* bulk GaAs spinless full triplet cannot become optically stronger merely by relabeling it in the trigonal basis.

### Source and temperature-correct Kane mass

Vurgaftman/Meyer/Ram-Mohan, *Band parameters for III–V compound semiconductors and their alloys*, J. Appl. Phys. **89** (2001), 5815–5875, [DOI 10.1063/1.1368156](https://doi.org/10.1063/1.1368156), tabulates GaAs `E_P=28.8 eV`, `Δ_so=0.341 eV`, `F=-1.94`, `E_g(0 K)=1.519 eV`, `E_g(300 K)≈1.422 eV`, and `m*=0.067m₀` as recommended near 0 K with separate 300 K effective-mass ranges.

With the standard stated 8-band curvature formula
```
m0/m* = 1+2F + (Ep/3) [2/Eg + 1/(Eg+Delta_so)]
```
the exact parameter substitution yields:

| Temperature/input gap | inverse mass | mass |
|---|---:|---:|
| 0 K, Eg=1.519 eV | 14.9211849901 | 0.0670188059 m0 |
| 300 K, Eg=1.422 eV with same F | 16.0673734596 | 0.0622379260 m0 |

The user's suggested `0.0664m₀` was **not** produced by the claimed 300 K substitution. It is approximately the 0 K result and reflects a mixed-temperature parameter comparison. The 300 K calculation using a temperature-independent remote-band F is a **conditional consistency exercise**, not a claim of a separately experimentally calibrated 300 K 8-band model. The 2-band no-SO estimate `1/(1+Ep/Eg)` ≈0.047 is an inadequate full GaAs prediction.

**Further non-promotion:** zincblende GaAs `T_d` has no inversion symmetry, so `Gamma1 s-like even parity` is not a literal bulk inversion-parity eigenvalue. Under spin–orbit coupling the actual `Gamma6` conduction and `Gamma8/Gamma7` valence **double-group** representations cannot be treated as three isolated spinless SALCs with an actual HH/LH gap.

## Why [111] strained/defect states are the next experiment

A generic spinless `C3v`-respecting perturbation has

```
H111 = epsilon_E I3 + (epsilon_A1-epsilon_E) * J3/3
```

in Cartesian X,Y,Z basis, where `J3` is the all-ones matrix. In the SALC basis it becomes `diag(epsilon_A1, epsilon_E, epsilon_E)`; the E doublet remains degenerate while A1 may split. **Symmetry permits but does not determine the splitting or whether the incident-solar-weighted device output increases.** The precise spinful HH/LH splitting of [111] GaAs requires 8-band Kane/Luttinger–Kohn + Bir–Pikus strain + geometry/field and disorder, not this spinless three-state model.

Measured/source-backed candidate controls:
- [*Anomalous Stranski-Krastanov growth of (111)-oriented quantum dots*](https://doi.org/10.1038/s41598-019-54668-z): a GaAs (111) strained-dot study with a **modelled** 3.8% tensile-strain case and computed valence HH/LH reordering, and physical quantum-dot growth/optical measurements. Don't promote computed dot band splittings to measured PV power.
- [*Tuning valence-band mixing of excitons confined in GaAs/AlGaAs quantum dots*](https://doi.org/10.1103/PhysRevB.87.075311): reversible applied anisotropic strain changes measured exciton emission intensities and fine structure. It concerns luminescence, not power conversion; verify orientation in its exact sample before classifying it as (111).
- [*Spectral signatures of high-symmetry quantum dots and effects of symmetry breaking*](https://doi.org/10.1088/1367-2630/17/10/103017): [111] C3v quantum-dot optical symmetry/breaking and valence mixing.
- [*Theoretical analysis of random alloy fluctuations in (111) InGaAs/GaAs quantum dots*](https://doi.org/10.1103/PhysRevB.94.125308): source-specific electronic/optical matrix-element anisotropy controls; does NOT establish a solar harvest advantage.
- For diamond NV, [Doherty et al. 2013](https://doi.org/10.1016/j.physrep.2013.02.001) provides a physically **different** defect C3v Hamiltonian and SALC setting. Equivalent group decomposition does not establish identical GaAs and diamond orbital wavefunctions, rates or electrical extraction.

## Exact next gates

G1 FINITE **passed numerical**: normalized SALCs, R and mirror algebra; 39 local symbolic+source-parameter assertions with separate archive receipt. Source-written exact Agda character module not yet typechecked.
G2 FORMAL **open**: local Agda Golden typecheck of the new finite module and corrected GaAs source, including its TOE import dependency; actual complex-algebraic `R U=U D` inside Agda remains unproved.
G3 MATERIAL **open**: source-traced GaAs (111) spinful 8×8 Kane/Bir–Pikus including temperature-indexed bandgap, remote bands, strain and confinement; validate against measured HH/LH spectra and dipole polarization.
G4 POWER **open**: actual absorptance, EQE, recombination, zero-bias and loaded I-V curves under AM1.5G, source/driver/strain actuation energy, geometry, and independent matched controls.
G5 369 **open**: a mathematically explicit same-material nontrivial morphism beyond a generic `C3v` representation, showing a controlled advantage not also present in an unrelated non-369 parameterization.
G6 DELIVERY **open**: >50% aperture-normalised net electric PCE with independent confirmation; heat and biofuel outputs separately accounted, not counted as electrical power.

**Research conclusion:** the finite Fourier/SALC bridge can be closed and is a valid source of selection rules. It does not close GaAsAtomic369ToKaneWeld as a *physical* 369 derivation. The highest-value material next experiment is strain/polarization-resolved [111] optical spectroscopy plus measured PV I–V against matched [001] and unstrained controls, not claiming >50% from the orbital relabeling alone.

## Added symbolic 8×8 spinful Schur-complement verification (17 Nov)

A second standalone checker `scripts/check_gaas_8band_spinful_schur.py` constructs an explicit near-Γ **eight-state** truncated Kane Hamiltonian:

- two spin states of the s-like conduction orbital;
- six states from Cartesian `X,Y,Z` valence orbitals ⊗ spin 1/2;
- `H_v=(2 Δ_so/3) L·S-(Δ_so/3)I_6`, with an exact fourfold eigenvalue 0 and twofold eigenvalue `-Δ_so`;
- `H_c=[E_g+(1+2F) ε]I_2`, where `ε=ħ²k²/(2m_0)`;
- interband block `H_cv = sqrt(E_P) sum_i k_tilde_i <S,σ|i,σ>`, with `sum k_tilde_i²=ε`.

Computing the exact Schur complement of the six valence states (not merely substituting the already-known inverse-mass formula) yields

```
H_cv (Eg I6 - Hv)^(-1) H_vc
 = Ep * [2/(3 Eg) + 1/(3(Eg+Delta)] * epsilon I2 .
```

Consequently `m0/m*=1+2F+(Ep/3)[2/Eg+1/(Eg+Delta)]`, for all momentum directions in this isotropic truncation. An independent numerical 8×8 eigenspectrum check for [100], [010], [001], [111] at both 0K and 300K fixed-F inputs confirms the analytical curvature. **17/17 local checks PASS**; no Agda kernel proof of this complex-spinful matrix yet.

This is a **near-Γ 8-state curvature model**, not a full finite-k fitted 8-band material device model. It omits the full valence Luttinger k² terms, real heterointerface boundary conditions, Bir–Pikus strain, conduction/valence field-driven confinement, screening, doping, recombination and measured PV efficiency; and the parameter F summarizes remote bands rather than resolving them as physical states. These are physical producer gates, not proofs to fabricate by selecting scalar data.


## 17 Nov continuation: source-qualified [111] Bir-Pikus matrix and spinful optical response

**Owner:** \`scripts/check_gaas_111_kane_birpikus_maxcut.py\` and \`DASHI/Physics/Photovoltaic/GaAs111BirPikusC3vFiniteExact.agda\`; imported into \`DASHI/Unified/PVPrimaryTOESpliceExact.agda\`. **94/94 locally executed numeric/model checks PASS**. Source-written Agda has no native kernel acceptance. The local script's exact committed GitHub copy has not been independently rerun from a branch checkout.

**Original sources and limits:** Bir–Pikus original strain formalism; [Vurgaftman et al., GaAs parameters, JAP 89 (2001)](https://doi.org/10.1063/1.1368156); [Bahder, strained zincblende eight-band, PRB 41 (1990)](https://doi.org/10.1103/PhysRevB.41.11992); [OghmaNano, explicit Cartesian XYZ Bir–Pikus convention](https://www.oghma-nano.com/manual/bir-pikus.html). Bahder's FULL operator also has conduction shear deformation and k×strain interband coupling missing from the present **near-Γ truncation**, therefore do NOT label the present model a complete Bahder implementation.

### Exact strain-model and source conventions

Using a **prescribed homogeneous symmetric strain tensor** ε and 3×3 orbital basis (X,Y,Z), define the following specified Cartesian convention:

\`\`\`
(H_BP)ii = av_eff Tr ε + b(3 εii - Tr ε)
(H_BP)ij = sqrt(3) d εij, i≠j .
\`\`\`

GaAs illustrative constants: ac=-7.17 eV; effective valence energy coefficient av_eff=-1.16 eV; b=-2.0 eV; d=-4.8 eV; Eg(300 K)=1.422 eV, Δ_so=0.341 eV, Ep=28.8 eV. **Vurgaftman's valence a_v sign convention is not directly the Oghma matrix convention**; av_eff=-1.16 means an actual valence shift -1.16 Tr ε. This is declared, not silently equated to a source's +1.16 magnitude. F=-1.94 is reused from the zero-temperature mass parameter set solely in the conduction-curvature truncation. Uncertainty and temperature fit remain open.

For a generic [111] axial strain with n=(1,1,1)/sqrt(3), ε = ε_perp I+(ε_parallel-ε_perp)nn^T, δ=ε_parallel-ε_perp:

\`\`\`
H_BP,[111] = av_eff Tr ε I3 + (d δ / sqrt(3))(J3 - I3).
E_A1 = av_eff Tr ε + 2 d δ/sqrt(3)
E_E  = av_eff Tr ε - d δ/sqrt(3)  (twofold spinless).
E_A1 - E_E = sqrt(3) d δ.
\`\`\`

This algebra is checked by direct 3×3 matrix-eigenvalue computations at ±0.8%, ±0.5%, +0.3% and zero strain, including C3 rotations and compatible mirrors, and the *same entry covariance* is encoded by finite Agda case exhaustion. The [001] comparator ε=δ zz^T gives orbital splitting |3 b δ| and breaks the [111] C3 action. A zero (pure hydrostatic) strain component does not lift valence spin-orbit degeneracy.

The **spinful** valence part is \`H_v=2Δ/3 L·S-Δ I6/3+H_BP⊗I2\`; conduction \`H_c=Eg+ac Tr ε+(1+2F)ε_k\` and Kane interband \`sqrt(Ep) k_tilde_j\`. The numeric model is eight-state and Hermitian but omits the full Luttinger valence dispersion, Bahder's k×strain mixing, actual boundary strain, confinement, piezoelectric polarization, and wavefunction-derived absorption or electric extraction. The relevant [111] rotation is orbital R⊗spin SU2(120°), whose third power is −I6 (spinorial double group); [001] strain fails that C3 test. Time reversal is conserved and every listed Γ level remains Kramers degenerate.

### Spinful numeric diagnostic: exact source parameters, illustrative tensor

At **0.5% axial [111] strain** with \`ε_perp=0\`, the Γ transitions from three Kramers valence pairs into the conduction-edge doublet are:

| E_transition (eV) | longitudinal ([111]) Kane strength/Ep | each transverse strength/Ep |
|---:|---:|---:|
| 1.378094 | 0.000000 | 1.000000 |
| 1.404637 | 1.218820 | 0.390590 |
| 1.734120 | 0.781180 | 0.609410 |
| **sum** | **2.000000** | **2.000000** |

For opposite prescribed −0.5% [111] axial strain: transition edges 1.437115, 1.465906, 1.794129 eV; longitudinal strengths 1.434817, 0, 0.565183 respectively and transverse strengths 0.282591, 1, 0.717409. Unstrained [111] spectrum: Γ8 fourfold 1.422 eV, Γ7 doublet 1.763 eV. At **zero strain**, the original eigensolver can choose an arbitrary basis inside the fourfold Γ8 subspace: calculating intensities separately for arbitrary two-state subsets is NOT invariant. The checker was corrected to group **all exactly degenerate multiplets by spectral projector**; the correct polarization-invariant Γ8 and Γ7 strengths are 4/3 and 2/3 per polarization.

For the [001] comparator at +0.5% prescribed axial strain, energies are 1.381950, 1.401347 and 1.733553 eV, with a different direction-dependent optical decomposition. The numerical results are **spectral matrix-element weights**, not absorption coefficients, EQE, power conversion or proof of photovoltaic gain.

**Conservation:** summing over every valence state and both conduction spin states for any normalized light polarization gives 2 Ep, independent of strain. This holds because the spin-independent Kane momentum tensor is a complete orbital-spin isometry and does not rely on fitted experimental spectra. It is not an upper bound on actual absorption of a designed device with different thickness or optical modes. Longitudinal [111] polarization is a mathematically useful component; for a plane wave propagating **along [111]**, E must be transverse, so a longitudinal excitation is not a directly realizable collinear far-field optical setting.

### Adversarial acceptance and candidate controls

1. **PASS under stipulated model:** +/−strain, 111↔001, C3v rotation/mirror, spinorial triple rotation, Kramers/time reversal, Hermiticity, complete projector dipole sum, non-symmetric input rejection. 94/94.
2. **OPEN as FULL material physics:** source-calibrated and physically relaxed ε_ij(r), finite-k Luttinger parameters and Bahder k×strain couplings, atomistic/alloy/defect mixing, strain temperature and measurement uncertainty.
3. **OPEN as optical experiment:** measured [111] vs [001] reflectance/absorptance/EQE at specified spectral flux and controlled strain, resolved Γ-valence polarization and extraction at the same two-terminal MPP.
4. **OPEN as 369-specific claim:** evidence that the original ternary/369 construction restricts or predicts a measurable material parameter or operation *beyond* conventional Td→C3v group theory. A group representation equivalence is not evidence of net extra harvested energy.
5. **OPEN as benchmark:** actual AM1.5G/G173 photovoltaic efficiency, standard aperture normalization, stability/controls, and >50% independent confirmation. Heat remains a separate auxiliary coproduct.


## Further maximum cut: exact spinful closed-form spectrum and polarization (17 Nov)

**Independent symbolic result**: \`scripts/check_gaas_111_birpikus_closed_form.py\` verifies the exact six-state spinful characteristic polynomial, derives the optical polarization weights analytically, and checks them against independently diagonalized 8-state near-Γ numerical operators at six nonzero signed [111] strain values. **37/37 local symbolic and cross-validation checks PASS**, in addition to the earlier **94/94 physical-model consistency checks**.

Set \`A = a_v,eff Tr ε\`, \`u=d(ε_parallel-ε_perp)/sqrt(3)\`, and spin–orbit energy \`Δ=Δ_so\`. For the *specified uniform axial* [111] strain model,

\`\`\`
E_pure = A-u                         (a Kramers doublet)
c      = A+u/2-Δ/2
h      = 3u/2+Δ/6
r      = sqrt(h²+2Δ²/9)
E_mixed,± = c ± r                    (two Kramers doublets).
\`\`\`

The full spinful valence characteristic polynomial is **exactly**

\`\`\`
det(λI6 - Hv) = (λ-E_pure)^2 [ (λ-c)^2-r^2 ]^2 .
\`\`\`

At zero strain (\`u=0\`) its six states recover fourfold energy \`A\` and the split-off doublet \`A-Δ\`. This closes the **analytic, source-convention-specific near-Γ spectral reduction** without a numerical eigensolver. It is not an analytic result for an atomistic crystal with strain gradients or all missing 8-band terms.

For each mixed Kramers doublet, its \`A1\` orbital fraction is

\`\`\`
w_± = (1 ± h/r)/2 .
longitudinal Kane weight / Ep = 2 w_±
each normalized transverse Kane weight / Ep = 1-w_±
\`\`\`

The unmixed \`E\` Kramers pair has longitudinal 0 and each transverse 1 (same dimensionless Ep units). As a result \`sum_all_pairs longitudinal=2\` and \`sum_all_pairs transverse=2\` **exactly for every prescribed signed strain**. Under the explicitly stated threefold and time-reversal symmetry these are projector/oscillator sum rules, not equivalent to integrated *solar absorptance* or additional useful power.

At +0.5% prescribed axial strain, the exact symbolic formulas reproduce the 94-test numerical values: \`E_pure≈0.0080564eV\`, \`E_mixed,-≈-0.3479696eV\`, \`E_mixed,+≈-0.0184868eV\`, \`w_+≈0.6094100\`. The optical thresholds include a separate conduction hydrostatic shift and are **1.37809, 1.40464, 1.73412 eV**, as reported above.

**Physical acceptance remains OPEN:** actual GaAs [111] strain field and orientation, temperature/coherence, full Bahder terms, valence k², measured electric-dipole spectra vs frequency/linewidth, photon-extraction boundary conditions, terminal JV at the MPP, and anything uniquely predicted by the original 369 construction rather than standard C3v group theory. Agda source remains uncompiled in this environment.


## 17 November P1d–P2 maximum cut: coherent-film elasticity, full-8-band parameter discipline and G173

**Status:** executable and Agda source committed to existing PR #1523. Original finite SALC and thermal modules remain in place, and thermal remains auxiliary. Numeric checks on a locally mounted prior Bir–Pikus source plus new independent pseudomorphic tests: **72/72 locally PASS**. Full 2002-row G173 JS model executed through the GitHub mirror. The new committed Python scripts and Agda imports have **not** been typechecked/run from a fresh remote checkout: do not claim native CI/Golden acceptance.

### Elastic producer: film, not dot

Source: cubic zincblende [111] layer, coherent in-plane mismatch \`e_in=(a_sub-a_layer)/a_layer\`, zero traction normal to the [111] plane. Choose \`n=(1,1,1)/√3\` and \`epsilon=e_in I+(e_out-e_in) n n^T\`. The cubic tensor Hooke law yields \`n·sigma·n = [(C11+2C12+4C44)e_out+2(C11+2C12-2C44)e_in]/3=0\`.

For example GaAs stiffness set C11=118.8, C12=53.8, C44=59.4 GPa, exact reduced ratio \`e_out/e_in=-269/580=-0.463793103448276\` (NOT zero). At +0.5% in-plane mismatch: \`e_out=-0.23189655%\`, \`delta=e_out-e_in=-0.73189655%\`, trace=+0.76810345%. Independently computed normal and transverse traction components vanish numerically to precision; reversed sign behaves correctly. The exact integer equality \`4640×269=2152×580=1248160\` is carried by \`GaAs111PseudomorphicElasticExact.agda\`, importing original \`GaAs111BirPikusC3vFiniteExact.agda\`.

**Material identifier gate:** This is an idealized coherent planar layer, not a measured strain tensor for Yerino's tensile self-assembled GaAs QDs grown on InP(111)A. Those dots have finite geometry, relaxation and piezoelectric interfaces; a pure GaAs-on-GaAs lattice match would give zero coherent misfit. The coefficients and temperature must be tracked against the actual grown *layer* rather than silently assigning pure GaAs coefficients to an InGaAs alloy.

Independent source for [111] strain and piezo equations: [Phys Rev B 84, 195207 (2011)](https://doi.org/10.1103/PhysRevB.84.195207); [Bahder's strained eight-band original, 1990](https://doi.org/10.1103/PhysRevB.41.11992) AND [1992 erratum](https://doi.org/10.1103/PhysRevB.46.9913); GaAs parameter compilation [Vurgaftman et al. 2001](https://doi.org/10.1063/1.1368156).

### Piezoelectric boundary is NOT a PV source

With zincblende tensor strain \`P_i=2 e14 eps_jk\` for cyclic \`i,j,k\`, the ideal coherent [111] tensor gives

\`\`\`
P_111 = (2 e14 / sqrt(3)) (e_out-e_in).
E_111,unscreened = -P_111 / (eps0 eps_r) ,
\`\`\`

where the field sign depends on the chosen [111] axis and interface charge orientation. At +0.5% misfit with illustrative e14=-0.16 C/m² and epsr=12.9, \`P_111=0.00135219 C/m²\`, **|E|=11.84 MV/m** in an unscreened planar-interface approximation, corresponding to a **59.2 mV potential drop across an arbitrarily assumed 5 nm thickness**. This is not an open-circuit PV voltage, not a measured internal field, and not a free energy source. Actual electrostatic screening, carrier density, interface boundaries, quadratic piezoelectric terms and deformation of sublattices are OPEN. A [001] diagonal biaxial stress control has zero first-order zincblende polarization along [001]; a [111] sign reversal reverses the sign of P.

### Eight-band Luttinger renormalisation prevents a serious false gain

The repo already has the 8-state Kane/Schur structure. Adding published **six-band** Luttinger \`gamma1,2,3=(6.98,2.06,2.93)\` directly to the 8-band valence block DOUBLE COUNTS explicit conduction-band couplings. Under the explicitly chosen near-Γ, no-remote-energy-dependence convention:

\`\`\`
gamma1prime = gamma1 - Ep/(3 Eg)
gamma2prime = gamma2 - Ep/(6 Eg)
gamma3prime = gamma3 - Ep/(6 Eg).
\`\`\`

At the **300 K conditional model** Eg=1.422 eV, Ep=28.8 eV this gives \`(0.22894515,-1.31552743,-0.44552743)\`. An explicit eight-state Hermitian model with valence spin-orbit and the corrected Cartesian 3×3 Luttinger block reproduces the six-band Γ8 heavy- and light-hole curvature:

\`\`\`
m_HH^[111]/m0=1/(gamma1-2 gamma3)=0.892857...
m_HH^[001]/m0=1/(gamma1-2 gamma2)=0.349650...
\`\`\`

The local exact eigenspectrum resolves the [111] and [001] curvatures to finite k. The larger **normal effective mass** can change *joint density of states and confined optical transitions*, but is not an independent oscillator-strength increase or extracted PV gain. This convention is source-backed by the discussion of six-band vs eight-band Luttinger parameters, [Phys Rev Research 2 033264, 2020](https://doi.org/10.1103/PhysRevResearch.2.033264) and [nextnano eight-band Hamiltonian](https://www.nextnano.com/docu/nextnanoplus/latest/reference/models/quantum/hamiltonian_zb_8kp.html). Renormalization schemes differ with spin-orbit denominators/remote-band choices; no general 8-band measured source fitting is claimed.

**Important hydrostatic source-sign gate:** some published GaAs compilations tabulate \`a_c=-7.17\` and \`a_v=+1.16 eV\`, yielding a bulk gap hydrostatic coefficient \`a_g=a_c-a_v=-8.33 eV\` in that sign convention. Other strains papers use an effective valence Hamiltonian coefficient \`a_v,eff=-1.16\` in a different energy-zero/operator convention. The inherited script uses \`-1.16\` with \`-7.17\` for the conduction band, which would give \`a_g=-6.01 eV\` under a **naive shared reference**. We must not silently identify these as the same experimentally calibrated band-offset convention. For +0.5% in-plane strain, the difference in valence hydrostatic shift between these alternatives is **17.82 meV**, sufficient to change the hypothetical solar-response calculation. This is a strict OPEN calibration gate: reconcile absolute band offsets and material convention before reporting experimentally predictive absorption or cell efficiency.

**Missing full Bahder terms:** Bahder 1990 reports additional conduction deformation potentials a', b', the spin-orbit strain interaction, and terms linear in k×strain in the conduction-valence block. The geometrical test \`k_eff=(I-epsilon)k\` in the new script is only an **alternative kinematic control**, NOT the proven full Bahder interband operator. No complete Bahder implementation is claimed, and actual b' and other coefficients must have source values or remain symbolic.

### Experimental spectroscopy donors are separate observables

- [Hayakawa et al., PRL 60, 349 (1988)](https://doi.org/10.1103/PhysRevLett.60.349): measured enhanced (111) versus (100) GaAs/AlGaAs quantum-well optical transitions and absorption anisotropy. Useful qualitative mechanism/geometry control; no published spectra fitting performed here.
- [Karlsson et al., PRB 81, 161307(R), 2010](https://doi.org/10.1103/PhysRevB.81.161307): *Fine structure of exciton complexes in high-symmetry quantum dots: Effects of symmetry breaking and symmetry elevation*. Pyramidal InGaAs/AlGaAs dots, polarization-resolved exciton transitions and electron-hole exchange; NOT the same as the \`Gamma8/Gamma7\` band-edge energies of a uniform film.
- [Sallen et al., PRL 107, 166604, 2011](https://doi.org/10.1103/PhysRevLett.107.166604): magnetic-field-dependent heavy-hole mixing and nominally dark transitions in [111] GaAs/AlGaAs QDs; a **zero-magnetic-field** Kane model cannot simulate those Zeeman/exchange observations.
- [Yerino et al., APL 105, 251901, 2014](https://doi.org/10.1063/1.4904944): tensile self-assembled GaAs/InP(111)A QDs, median **exciton fine-structure splitting 7.6 micro-eV**. The meV orbital valence splittings predicted by our coherent-film model are NOT this fine-structure splitting and cannot be used to pretend a fitted spectral result. Dot wavefunctions/exchange must be added.

### P2: real G173 spectrum coupled to conditional absorptance and reciprocity

Reuses \`scripts/check_pv_astm_g173_radiative.py\`, 2002-row four-column NLR ASTM G173-03 source, \`scripts/check_gaas_111_kane_birpikus_maxcut.py\` and the new pseudomorphic + renormalised-Kane script. \`scripts/check_pv_111_g173_radiative_jv.py\` constructs Γ-point valence spectral projectors, two transverse **normal-incidence** polarizations, and a hypothetical direct-allowed onset

\`\`\`
alpha(E) = alpha0 * Σ_j [w_j * sqrt(max(E-Eg_j, 0))]
A(E)     = 1-exp(-alpha(E)*thickness)
EQE(E)   = collection*A(E).
\`\`\`

The weights sum to one after normalizing over the complete two-spin Kane oscillator manifold; this normalization does NOT make \`alpha0\` a measured bulk GaAs absorption coefficient. Baseline \`alpha0=4×10^6 m^-1 eV^-1/2\`, selected thicknesses 0.2,2,20 micron, normal-incidence reflectivity 0, same-material 300K source; **no interface/QW/cavity/exciton absorption fit**.

For the radiative diode, use **A(E) in both** solar photon current \`Jsc=q∫Φ_G173(E)A(E)dE\` and emitted dark-current integral \`J0=q(2πq³/h³c²)∫E² A(E)/[exp(E/Vt)-1] dE\`, and optimize \`Pmax=V[Jsc-J0(exp(V/Vt)-1)]\`. That energy-diagonal angular-averaged emissivity assumption is a **device-model simplification**; true angular/polarization-dependent Kirchhoff reciprocity, electroluminescence, nonradiative losses, extraction and contacts are OPEN.

**Executed against the original 2002 G173 global spectral rows retrieved from public source mirror \`frssp/atlc/ASTMG173.csv\`, SHA \`300821f0504ed3069a6af949056f60af378f6fc2\`. Integrated power 1000.370656 W/m².** Numeric values for *conditional* perfectly collecting [111] cases, using the inherited \`a_v,eff=-1.16\` convention (which is **NOT reconciled**):

| thickness | zero-strain ideal Pmax | +0.5% coherent [111] in-plane Pmax | -0.5% coherent [111] in-plane Pmax | tensile delta |
|---|---:|---:|---:|---:|
| 0.2 μm | 128.842 W/m² | 128.976 W/m² | 127.460 W/m² | +0.134 W/m² |
| 2 μm | 314.153 W/m² | 314.640 W/m² | 310.336 W/m² | +0.487 W/m² |
| 20 μm | 331.849 W/m² | 336.005 W/m² | 328.355 W/m² | +4.157 W/m² |

**Adversarial negative control:** in the 2 μm case, a loss of just **0.15097%** of the strained sample's collected current (required collection fraction 0.9984903), holding its hypothetical optical J0 fixed, eliminates the entire +0.487 W/m² advantage. The 2 μm baseline radiative-only ideal efficiency is ~31.40% and the strained ideal is ~31.45%: **neither is a measured cell, a certified improvement, nor evidence for a genuine 369 mechanism.** They cannot be summed onto an independently optimized 3-junction radiative ideal without recomputing photon redistribution/current matching.

### Max-cut status and next experimental requests

**PASS model-only:** exact source-ratio integer equality; 72 local pseudomorphic/8band/piezo tests; conditional near-Γ spectral projectors and 2002-row G173 reciprocal-diode integration carried out in GitHub connector calculations.

**OPEN source/physical acceptance:** same-temperature and same-reference GaAs band offsets (especially valence a_v sign), alloy composition-dependent elastic and Kane params, Bahder original AND 1992 erratum full 8×8 strain/k operators, finite-film boundary strain, atomistic QD wavefunctions/exchange, screening and piezo, independently measured Γ-to-exciton observables, experimentally fitted alpha(E)/EQE and angular emission, JV/Pmax under matched spectrum, and nontrivial 369-derived predictive constraint versus ordinary C3v symmetry.

**Required calibration data:** for the same wafer/dot: precise layer/substrate composition, orientation, reciprocal-space map or XRD strain, well thickness/interface, temperature, polarization-resolved PLE/absorption with linewidths and confidence intervals, and JV/EQE at actual AM1.5G irradiance. Experimental PL fine structure alone cannot replace that same-object dataset.

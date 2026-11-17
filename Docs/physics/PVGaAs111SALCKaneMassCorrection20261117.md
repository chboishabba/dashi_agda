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

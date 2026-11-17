# PV 369 / GaAs maximum cut: Bahder 1992 corrected operators, independent (111) mass benchmark and coordinate no-gain (17 Nov 2026)

**Owner:** [DASHI draft PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523); Agda golden kernel acceptance OPEN. **No native compiler, CI, measured device data, source fitted material or independently demonstrated >50% PCE.** Thermal and HV/ORC remain auxiliary. The original atomic 369/C3, finite quantum producer and CoTaSe2 Wannier same-basis covariance owners are reused by import, not modified or falsely promoted to the same material.

## Why experimental source calibration cannot be called complete

**Primary empirical authority:** L. W. Molenkamp, R. Eppenga, G. W. 't Hooft, P. Dawson, C. T. Foxon, and K. J. Moore, *Determination of valence-band effective-mass anisotropy in GaAs quantum wells by optical spectroscopy*, Phys. Rev. B 38 (1988), 4314(R). DOI https://doi.org/10.1103/PhysRevB.38.4314 . The paper reports high-resolution excitation spectra in GaAs/(Al,Ga)As QWs grown along (001), (111)B and (310). The **published abstract** reports inferred HH001=0.34 m0, LH001=0.094 m0, HH111=0.70 m0, extracted through an eight-band QW model. We have NOT obtained full paper data/figures or fitted its specific well widths, temperatures, confinement or material composition; these are **model-inferred experimental effective masses**, not direct same-wafer bulk curvatures.

**DASHI simplified theoretical contrast:** The nominal six-band bulk Luttinger values gamma1=6.98, gamma2=2.06, gamma3=2.93 yield the rational exact theoretical values:

| Target | Nominal mass | 1988 QW-inferred mass | Nominal relative discrepancy |
|---|---:|---:|---:|
| [001] HH | 1/(gamma1−2gamma2)=50/143=0.349650 m0 | 0.34 m0 | +2.84% |
| [001] LH | 1/(gamma1+2gamma2)=10/111=0.090090 m0 | 0.094 m0 | −4.16% |
| [111] HH | 1/(gamma1−2gamma3)=25/28=0.892857 m0 | 0.70 m0 | **+27.55%** |

**Do not erase the discrepancy by refitting generic gamma3:** A naive exact algebraic solve gamma3=(gamma1−1/0.70)/2=2.775714..., versus 2.93 original, but this comparison conflates a band-edge analytic mass with a finite-width excitonic QW-effective mass from an eight-band fitting protocol. That ~5.27% gamma3 displacement is a **diagnostic, not a calibrated replacement**. Higher-alpha priority: acquire the same paper's full orientation-resolved QW optical spectra, layer wells/barriers and sample temperatures, implement confinement/exciton and source-fitting to those quantities, then cross-validate. Authors retain experimental ownership.

**New exact-source module:** `DASHI/Physics/Photovoltaic/GaAs111MeasuredMassAdversarialExact.agda` imports the existing GaAs optical-device owner and proves that the three original rational-model mass ratios are not definitionally equal to the published comparison ratios, with a typed separation of mass spectroscopy vs exciton fine structure vs absorptance, EQE and terminal MPP. This is a mismatch witness, NOT a falsification of the full 8-band Kane model.

**Local independent executable:** `scripts/check_gaas_1988_mass_and_bahder_erratum.py`; **27/27 exact arithmetic and source-gating checks PASS**, source values and nonpromotion boundaries explicit.

## Original Bahder 1990 + inspected 1992 primary erratum

**Authoritative:** Thomas B. Bahder, *Eight-band k·p model of strained zinc-blende crystals*, Phys. Rev. B 41 (1990), 11992, DOI https://doi.org/10.1103/PhysRevB.41.11992 . *Erratum*, Phys. Rev. B 46 (1992), 9913, DOI https://doi.org/10.1103/PhysRevB.46.9913 . **The actual one-page 1992 PDF was inspected as an image**; the original full 1990 article PDF requires APS authorization from this environment, so full equation-by-equation original-source acceptance is not claimed.

The erratum explicitly corrects:
1. **Equations 33–35:** spin-orbit strain coupling matrices N1 (4×4), N2 (4×2), N3 (2×2), in the original Γ8⊕Γ7 basis.
2. **Equation 30:** the valence deformation constant `a=−(ell+2m)/3`; the source notes that this differs in sign from a cited Bir/Pikus book convention.
3. **Equation 16:** `R=−(sqrt(3)/2)(hbar²/m0)[gamma2(kx²−ky²)−2i gamma3 kx ky]` in the author's fixed basis.
4. **Equation 42:** the factors of Planck's constant in P,Q,R,S must be **squared**; checking only R does not pay all four terms.

**New independently tested source transcription:** `scripts/check_bahder_1992_corrected_spin_strain_blocks.py` builds complex symbolic N1/N2/N3 as printed on the erratum page, combines them into one Hermitian traceless six-state block, and checks the full zero-strain and hydrostatic limits, [111] tensor shear response, corrected R axes and complex Hermiticity, corrected a sign and hbar² dimensional dependence. **36/36 local tests PASS**. The equivalent *full eight-band* physical Hamiltonian, including the different Γ8/Γ7 vs Cartesian spin-orbit basis, has **not** been constructed from the original Bahder full operators. No fake source unitary is inserted.

**Quantitative omitted-term budget:** using coherent +0.5% (111) in-plane strain, nominal GaAs 300 K elasticity gives eps_out=−0.0023189655, eps_in=0.005 and spin-orbit Δ=0.341 eV. The corrected erratum spin-orbit strain block has eigenvalues approximately (eV):

`−0.00113667` (2×), `−0.00014493` (2×), `+0.00128159` (2×), and spectral operator norm **1.2816 meV**. It is traceless; its hydrostatic limit has Γ8 shift −2Δeps/3 and Γ7 shift +4Δeps/3, but not zero overall operator. For a *same-basis* Hermitian assembly, Weyl's eigenvalue perturbation inequality bounds corresponding eigenvalue shifts by the spectral norm. This is NOT the actual full-device correction or solar-power loss until correctly combined with the orbital Bir-Pikus matrix, k dispersion, confinement and material source conventions. The earlier 0.487 W/m² *conditional* radiative PV advantage therefore lacks a demonstrated model-error margin.

**New typed obligation ledger:** `GaAsBahder1992ErratumGateExact.agda`. N1/N2/N3, the explicit R and scalar a convention have independent symbolic source checks; the full P,Q,R,S Planck-factor normalization, conduction a'/b', strain×k, source-authenticated common Γ8/Γ7 basis and actual device strain remain fail-closed.

## Representation-level physical no-free-gain gate

Earlier source: `AtomicPeriodicTable369MagneticC3PhysicalRealizationExact.agda` and `Atomic369GaAs111TrigonalCharacterExact.agda` and original `DASHI/Physics/CondensedMatter/CoQuarterTaSeTwoWannierBNSCovarianceExact.agda`, whose evidence discipline explicitly requires actual material Hamiltonian and symmetry sewing in the SAME Wannier basis.

**New native Agda source:** `Atomic369BasisTransportNoFreeGainExact.agda` defines a true finite bijection with inverses and proves that for any Nat-valued original observable `O`, the *transported* observable on the new label space satisfies `O'(encode(a))≡O(a)`, and the transported endomorphism intertwines with the encoding. It inhabits the original finite magnetic/trigonal **LABEL** equivalence. This is not an analytical complex Hilbert-space Fourier unitary proof, and it cannot be promoted to a material wavefunction map without same-basis data.

**Independent numerical synthetic control:** `scripts/check_gaas_369_same_basis_no_free_gain.py`: finite U Fourier matrix; coherently conjugated H, dipole, source density and charge/current measurement have invariant eigenvalues, tr, tr-square, all finite transition magnitudes and expectation values, **35/35 local tests PASS**. A genuine perturbation changing H with the same optical/extraction operators is deliberately distinct. Therefore any **369-specific photovoltaic advantage** must predict a change in physical operators/coupling/geometry, not merely reorganize quantum labels or select the same three C3 characters.

## Complete this before claiming P1d, P2 or >50%

**P1d EXPERIMENT OPEN:** same-sample QW thickness, alloy composition, growth orientation, calibrated layer strain/relaxation, interface charges/field, temperature, full measured PLE/absorption and polarized line widths. Molenkamp mass comparison is not a same-sample calibrated fit; Yerino dot exciton FSS is a different observable and requires exchange.

**P1d FULL BAHDER OPEN:** original 1990 PDF full equations, all corrected 1992 components in common eight-state basis, source a'/b' and k×strain coefficients, full valence Luttinger dispersion and material boundary conditions, native Agda kernel acceptance. A code route using the original published a,b,d only is not yet a full Bahder model.

**P2 ACTUAL PHOTOVOLTAIC OPEN:** measured reflectance/transmittance and source-constrained absorptance alpha(E,angle,pol), EQE, nonradiative recombination and transport, loaded JV/Mpp and optical escape under ASTM G173, matched [001]/[111] and passive/active controls. Only then can a 0.487 W/m² conditional margin be assessed.

**369 SPECIFIC OPEN:** demonstrate a material prediction invariant under coordinate relabeling but different under an actual 369-controlled state/coupling operator, and test it against a conventional no-369 control. Merely expressing T2↓C3v=A1⊕E does not add a physical transition or efficiency.

**P3–P6 RETAINED:** driven Stark/Floquet, source-aware RF energy, carrier multiplication, thin films and BH4 biological photosystems independently remain in the PV-first roadmap. Ground/heat/ORC remains a secondary auxiliary ledger.

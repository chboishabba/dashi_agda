# R2P2 × optical lattice × 369 wave: source-distinct control cut

Date: 2026-10-28. **Source written in PR #1407. Agda kernel and checkout-based Python test suite have not executed. No empirical 171Yb R2P2 lattice calibration or quantum-gravity discovery is established.**

## 1. Yesterday's repository/PR precedence

Checked current GitHub code and the actual PR file histories:
- [#1085](https://github.com/chboishabba/dashi_agda/pull/1085), **merged**, is the existing owner for `DASHI.Physics.Closure.WolfPrize2026UltracoldControlBridge` and `BothwellYe2022MillimetreRedshiftReceipt`. It records the distinction between Immanuel Bloch's ultracold lattice many-body control and Jun Ye's optical lattice / redshift metrology. The **2022 vertically oriented strontium-lattice clock** is a physical but separate gravity experiment.
- [#1117](https://github.com/chboishabba/dashi_agda/pull/1117), **open, unmerged**, retains distinct geodetic, metrology, optical transfer, empirical-ingestion and clock ratio owners. Do not assert these PR-only additions are on the current PR's master base.
- [#1292](https://github.com/chboishabba/dashi_agda/pull/1292), **open**, is the 2026-10-27 quantum metrology/TOE normalization, on its own `agent/ym-goal1-r485-toe-stack-20261027` base. It is not silently imported as an available master theorem. Retain its independent PR proof ownership.
- [#1407](https://github.com/chboishabba/dashi_agda/pull/1407) is the present R2P2 Veritasium/369 architecture. It already imported `DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact`, 369 wave exact-state preservation, a signed comb-beat nonfactorability theorem, a polyphase/finite causal diamond and 3-clock synthetic loop.

Repository PR search for `Aubry`, `optical lattice`, `lattice clock` and file search for `AubryAndre` or `OpticalLattice` did **not** reveal a distinct new 2026-10-27 Aubry–André Agda proof owner. This is a search result, not proof of absence on every unmerged private branch. No such prior work is overwritten.

## 2. Three disjoint experimental referents

| Referent | Apparatus / species | Observable | Source type |
| --- | --- | --- | --- |
| **Bothwell et al. 2022 (Ye/JILA)** | Vertical optical lattice, ultracold **strontium** in one millimetre-scale sample | Spatially resolved gravitational frequency gradient | Original *Nature* experiment, https://doi.org/10.1038/s41586-021-04349-7; source-owned |
| **Ma, Stöltzel, Christensen et al. 2026** | Horizontal **87Sr** lattice, **813 nm + 497 nm** magic-wavelength bichromatic potentials | Reduced tunnelling, Rabi linewidth, differential Ramsey coherence | Original **arXiv:2610.17499v2 (2026-10-14)**, https://arxiv.org/abs/2610.17499 ; separate experiment |
| **Triano, Sinclair, Ludlow, Caldwell et al. 2026 R2P2** | Two neutral **ytterbium** optical lattice clocks at Mt Blue Sky and NIST Boulder | Remote gravitational-potential/frequency ratio through 69 km free-space + 81 km fibre link | Original APS DAMOP 2026-06-03 abstract, https://meetings-archive.aps.org/damop/2026/g07/7/ |

The APS source **does not certify the isotope of each R2P2 clock**. A `neutralAt 70 101` 171Yb state in the DASHI architecture is a *model/example*, NOT an independently source-verified identity for both clocks. The Ma experiment uses 87Sr (Z=38, N=49), not that Yb model.

**Ma experiment source details**: Two collinear horizontal strontium lattices, both tuned near magic wavelengths, with a clock probe at **698 nm**. The paper defines

```text
H_AA = -J Σ_i (|w_{i+1}><w_i| + |w_i><w_{i+1}|)
       + Δ Σ_i cos(2π β i + φ)|w_i><w_i|
β = λ_primary / λ_secondary
```

The ideal irrational/incommensurate chain has the conventional threshold `Δ/J=2`. Ma et al. experimentally demonstrate recovery of a narrow, Fourier-limited clock carrier and up to approximately **two-second** differential Ramsey coherence, reaching as much as **100-fold** improvement over the delocalised regime. The publication itself cautions that experimental `incommensurate` means no short-period repetition over the actual finite system; its full spectra also use a continuous bichromatic potential when the tight-binding approximation is inadequate. These results belong to Ma and collaborators. They are not predictions by DASHI and are not remotely transferred R2P2 Yb measurements.

## 3. Reuse-first original finite proof and nonpromotion

New source-written owner: `DASHI/Physics/Closure/R2P2OpticalLattice369HamiltonianCutExact.agda`. It imports existing **merged/default-master** owners: `WolfPrize2026UltracoldControlBridge`, `BothwellYe2022MillimetreRedshiftReceipt`, `AtomicPeriodicTable369GenerativeExact`, R2P2's primary-source boundary and the previously added **369 wave/signed beat information-loss cut**.

The new minimal **three-site path P3** carries two independent unsigned integer operators:

```text
A(x,y,z) = (y, x+z, y)          # nearest-neighbour adjacency
D(x,y,z) = (0, y, 2z)           # site-dependent potential toy
e_left   = (1,0,0)

A(D(e_left)) = (0,0,0)
D(A(e_left)) = (0,1,0)
```

Hence `A∘D ≠ D∘A` on an explicit finite basis witness; `finiteLatticeOperatorsFailToCommute` is the source-written Agda proof term. The `3` labels the mathematical sites, not 3/6/9 physical orbitals or lattice wavelengths. This is not Ma's true `-J` hopping, cosine onsite modulation, calibrated `J,Δ,β,φ`, an infinite quasiperiodic spectral transition, atom-light coupling, an optical Hamiltonian derived from Maxwell, or a claim of improved real clock coherence. No same-object physical mapping is asserted.

The module also imports the existing 87Sr atomic identity `neutralAt 38 49` and documents that the R2P2 Yb isotope needs independent confirmation. Its `ClockExperimentLane` datatype has three different constructors: `maBichromaticSr87`, `bothwellYeVerticalSr`, `trianaMountainYb`. It proves their nonidentity at the *source-index level*; this does not establish a general physical inequivalence theorem.

A canonical `OpticalLattice369PhysicalAuthority` record composes the earlier source owners. Fields for `finiteP3ProvesInfiniteAAThreshold`, `maMagicLatticeTransferToR2P2Verified`, `actualR2P2TrapDepthMeasuredHere`, `maPublishedCoherenceDataIngested`, `opticalLatticeControlsMetricRedshift` and `measuredQuantumGravityObserved` are **all false**. These are explicit scope declarations, not negative results about nature.

## 3b. Signed three-site spectral calculation (independently executed)

Added `scripts/r2p2_optical_lattice_3site_diagnostic.py` as a **pure Python/Fraction**, finite three-site spectral calculation. The executable uses

```text
H(J,D) =
[  0  -J   0 ]
[ -J   D  -J ]
[  0  -J  2D ]
```

with real signed off-diagonal hopping. Here `D` is *only a synthetic linear on-site gradient*, **not** the calibrated `Δ cos(2π β i+φ)` of the Ma experiment and not a gravitational energy shift. Exact determinant and trace arithmetic yield:

```text
det(λ I - H)
  = λ³ - 3D λ² + (2D² - 2J²)λ + 2D J²
  = (λ-D)((λ-D)² - D² - 2J²)
```

Thus `λ=D` is an exact finite eigenvalue for every rational `J,D`; the other roots are `D±√(D²+2J²)`. For the synthetic choice `J=1,D=2`, the cubic is `λ³-6λ²+6λ+4`. This is a **genuine finite spectral calculation**, not an AA transition or an optical-clock measured spectrum. Its independent arithmetic oracle was **actually run** locally for `(J,D)=(1,2),(1,0),(0,2),(3,6),(2,9),(-2,-3)`, 6/6 exact rational characteristic/cofactor/central-eigenvalue tests passed. The committed diagnostic file and full GitHub checkout suite were **not** run locally; equivalence of source and independently exercised arithmetic was checked by authored formula, not an exact-head execution receipt.

The executable is called by the PR-local CI workflow, and `tests/test_r2p2_optical_lattice_369.py` now exercises all six parameter pairs. This remains below Agda kernel certification and below a fit to Ma et al.'s published Rabi/Ramsey spectra.

## 3c. Ma supplementary S4: five rational supercells and C18 non-identity

The original **Ma et al. 2026-10-14 arXiv:2610.17499v2 Supplement S4** uses rational supercells `N497:N813 = 18:11, 85:52, 139:85, 175:107, 265:162` for the continuum plane-wave representation, with coupling offsets `±N497` and `±N813` in momentum-index space (S6). These belong to the *plane-wave* representation, **not** the nearest-neighbour site-basis adjacency in our P3 toy. Using one basis as the other without an explicitly unitary/bounded change of basis would be a wrong-type identification.

The finite Agda source now proves, by exact natural-number arithmetic, all five **nominal-only** wavelength cross-product offsets using the labels `497` and `813` nanometres:

| Periods 497:813 | N497×497 (nm) | N813×813 (nm) | Nominal length mismatch |
|---|---:|---:|---:|
| 18:11 | 8946 | 8943 | 3 nm |
| 85:52 | 42245 | 42276 | 31 nm |
| 139:85 | 69083 | 69105 | 22 nm |
| 175:107 | 86975 | 86991 | 16 nm |
| 265:162 | 131705 | 131706 | 1 nm |

These are *mathematical exercises on rounded wavelength labels*. The operational magic wavelengths are distinct calibrated quantities; no physical mismatch or apparatus configuration is reconstructed from this table. In particular this finite data does **not** prove Ma's spectral convergence, experimental threshold, magic-wavelength systematic shifts, or R2P2 Yb calibration.

`DASHI.Foundations.Base369BinaryTernaryRefinement.phase18-sector-count` independently proves the inherited C18 index carrier has **18 sectors**. New `maPhysicalEighteenAndC18EqualAsNumbersOnly` records the arithmetic coincidence; `maSupercell18IsNotAnIdentifiedC18PhysicsRealization` keeps the physical identification **false** absent a source-produced map. The distinction is attached to `R2P2369AtomicQuantumDiamondArchitectureExact` and all three TOE roots. These flags are epistemic guardrails; not theorems that a future apparatus *could never* relate the carriers.

`scripts/r2p2_optical_lattice_3site_diagnostic.py --nominal-supercell-pareto` computes the exact rational relative nominal mismatch `abs(N497*497 - N813*813)/(N813*813)`. Its two objectives are *smaller N497* and *smaller nominal relative mismatch*. At these objectives, **85:52 is Pareto dominated by 18:11**; 18:11, 139:85, 175:107, 265:162 are nondominated. This analysis was independently executed using Python `Fraction` against the five source-provided integer pairs (cross-products, exact mismatches and dominated flags). The committed exact-branch script/test suite has not executed locally; no actual physical spectral optimality follows. The original authors keep priority for the approximants and simulations. The Pareto ranking is source-written DASHI analysis with its own explicitly limited objectives.

## 4. Pareto / snowball / Ibrahim plan — real cutset

**P0: Experiment identity** — separate the 2022 Sr vertical redshift, 2026 Ma Sr87 horizontal AA localization, and 2026 R2P2 neutral-Yb mountain redshift. This is a primary-source provenance/authority gate.

**P1: Typed confinement producer** — a specific isotope, 1S0–3P0 atomic transition, polarization, primary/secondary magic wavelength, differential Stark shifts, hyperpolarizability, BBR shift, tunnelling J, onsite modulation Δ, phase φ and uncertainty. Do not infer `171Yb` or 497/813 nm for R2P2 from the Ma paper.

**P2: Clock measurement** — atom preparation, cooling, resolved Rabi/Ramsey interrogation, phase/contrast, servo frequency, sample-averaged systematic shifts, stability Allan deviation and covariance. Ma's Ramsey 2 s is *measured for Ma's apparatus*, not R2P2.

**P3: Frequency comb and physical link** — preserve signed beat, f_rep, f_CEO, tooth index, cycle slips, atmospheric/fibre nonreciprocal delay and calibrated bidirectional 69/81 km transfer.

**P4: Gravity comparator** — independent geopotential/time models and uncertainties, same-epoch Yb clock ratio, external raw-data checksum and reproducible residual against GR.

**P5: Physical inference** — prespecified model-specific alternatives with enough independent observables to discriminate the model from apparatus biases. Neither clock coherence nor a 369 finite toy automatically demonstrates gravity quantisation.

Attribution: Aubry & André retain original ideal localization-theory priority; Ma et al. retain their 2026 experiment; Bothwell/Ye the 2022 strontium gravity result; Triano/Sinclair et al. the 2026 R2P2 technical network; original DASHI/Wolf/Atomic/Wave/PR theorem authors retain their owners. Ibrahim/Danforth/Dodds and prior Monster 3B work remain separate. Search priority and shared numerals never promote one representation to another. No ESD files are touched.

## 5. Verification status

- Source-written Agda finite three-site witness. Imported by `DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda` and **all three TOE roots**.
- Added `tests/test_r2p2_optical_lattice_369.py`, exact noncommuting map and source/authority static contract, plus six signed spectral cubic test cases.
- Target `R2P2OpticalLattice369HamiltonianCutExact.agda` added to the existing PR-local focused pinned Agda workflow.
- Python arithmetic can be checked independently in a local runtime. It is **not** an Agda kernel receipt and not a source-specific measurement.
- Agda binary was absent on the available host. The current PR has no reported exact-head GitHub workflow run. Do not claim test suite or kernel success unless actually executed.

**Exit wall:** only instrument-correct primary-source calibration and real published ratio/spectra/covariance data can establish the physical relationship beyond finite construction. Kernel checks must separately verify source-written type correctness.

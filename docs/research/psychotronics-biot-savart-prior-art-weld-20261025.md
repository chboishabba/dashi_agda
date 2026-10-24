# Field Loom: reuse DASHI's existing Biot–Savart theorems and filament solver

**25 October 2026 · source-specific prior-art weld, not a new physical law or gravity result.**
This cut corrects an under-reuse in PR #1242. The repository already owned Biot–Savart before the Field Loom proposal. A bare "Biot–Savart loop simulator" was not the first source-owned mathematical implementation; it was a **different numerical representation** requiring its own verification. Preserve original authorship, representation, scope and verification status.

## Repo exact mathematics: original owners and what is actually established

| In-repo source module | Reused named result/law | Exact admissibility and remaining limit |
|---|---|---|
| `DASHI/Physics/Closure/NSTriadKNFourierBiotSavartExact.agda` | `biotSavart`, `biotSavartTransverse`, `crossNormLagrange`, `biotSavartNormGainSquared`, `phaseCorrectedCurlBiotSavart` | Rational **amplitude** `|k|⁻²(k×ω)`; the omitted complex Fourier phase is deliberately separate. Exact rational/vector identity source, **not** measured current/field conversion or thin-wire integral |
| `DASHI/Physics/Closure/NSTriadKNMaxwellFluidBiotSavartBridgeExact.agda` | `coupledBiotSavart`, `magneticFieldFromCurrent`, `magneticFluidRelation`, `coupledBiotSavartTransverse` | Already reuses Fourier inverse curl for Maxwell current and fluid vorticity **up to an explicit coupling**. Equality of elliptic amplitude operators does not equate MHD dynamics, viscosity, arbitrary coils or experimentally measured fields |
| `DASHI/Physics/Closure/NSPeriodicBiotSavartTransversality.agda` and `NSFourierBiotSavartTriadKernel.agda` | Generic Fourier-vector laws, modewise divergence-free transversality and vorticity transfer | Abstract law-stack under a supplied Fourier carrier; not a new electrodynamic law; finite periodic/triadic fluid closure is distinct |
| `DASHI/Physics/Plasma/MHDPhysicalInverseCurlMagneticHelicityExact.agda` | Complex periodic Fourier physical curl, magnetic vector potential, reality/adjoint and inverse-curl identities | Different, more physically phase-complete **magnetic vector-potential** construction; periodic/complex boundary remains separate from open real-space wire |
| `DASHI/Physics/Plasma/MHDMaxwellLorentzReductionBidiExact.agda` | Maxwell U(1) → MHD law-stack distinctions | A magnetostatic identity is not full Maxwell evolution, plasma kinetics, MHD turbulence or plasma-water chemistry |
| `scripts/psychotronics_field_loom_coils.py` | Original PR #1242 finite circular-loop midpoint quadrature `loop_b`, `pair_b` | The runtime producer for *illustrative* real-space filament fields; not a mathematically certified Fourier-to-wire kernel equivalence nor calibrated coil |
| **This cut**: `DASHI/Physics/Closure/FieldLoomExistingBiotSavartReuseExact.agda` | **Thin import-only bridge** delegates the exact Fourier field, transverse identity, Maxwell/fluid scaling and phase-corrected inverse curl to existing owners | Reuses existing identities without duplicating their definitions or asserting physical filament equivalence; source-written, **no new Agda kernel check** |
| **This cut**: `scripts/test_psychotronics_field_loom_biot_savart_reuse.py` | Independent analytic on-axis and elliptic-integral off-axis loop-field reference to the **existing** `loop_b`; current reversal, superposition, numerical `∇·B` and singularity checks | Numerical consistency, not original discovery/physical calibration; optional SciPy `ellipk/ellipe` is required for off-axis reference, and singular ideal-wire configurations are excluded |

**Historical and modern attribution:**
- **Jean-Baptiste Biot and Félix Savart**, original 1820 current-generated magnetic-field experiments; the classical law is theirs, not Maxwell's, DASHI's or a modern Fourier-fluid paper's. **André-Marie Ampère** independently developed foundational current interactions, also 1820s.
- **James Clerk Maxwell**, *A Treatise on Electricity and Magnetism* (1873), canonical later electromagnetic synthesis; the Fourier current-to-field relation is a representation of magnetostatics, not an original 1873 claim about our fabricated loop.
- **Jean Leray (1934)**, Fourier fluid projection lineage; **J. Thomas Beale, Tosio Kato, Andrew Majda (1984)**, DOI `10.1007/BF01240221` and **Xiaoyutao Luo (2019)**, DOI `10.1007/s00021-019-0411-z`, original fluid/vorticity literature. Their mathematical work must not be misattributed as the historical origin of current-field magnetostatics.
- **Samuel J. Ling, William Moebs, Jeff Sanny**, *University Physics Volume 2* (OpenStax, 6 October 2016), [§12.1](https://openstax.org/books/university-physics-volume-2/pages/12-1-the-biot-savart-law): secondary pedagogical source for the line-current integration, not a newly invented force law. Original derivation remains classical.
- [Oregon State *The Relationship between B, A and J*](https://books.physics.oregonstate.edu/GSF/mtriangle.html) gives the standard vector-potential/real-space integral relation. Its current distribution and `1/|x-x'|` Green kernel require specified domain/boundary conditions.
- [NIST CODATA 2022](https://physics.nist.gov/cgi-bin/cuu/Value?mu0%7Csearch_for=magnetic) recommends `μ₀=1.25663706127(20) ×10⁻⁶ N·A⁻²`. In the SI after 2019, `μ₀` is **not exactly** `4π×10⁻⁷` as some old textbooks claim. The existing Python `MU0=4e-7*pi` is an explicitly retained **legacy numerical approximation**; the relative discrepancy is ~`1.3×10⁻¹⁰`, negligible at the current illustrative stage but nonzero and should join a future actual calibration/constants uncertainty ledger. Model numbers in old PR remain reproducible without silently changing `MU0`.

## Exact mathematical boundary: a shared Fourier symbol is not a free-space wire proof

For sufficiently well-behaved divergence-free steady current density `J` in free space, the *classical magnetostatic theory* has:
```
B(x) = μ₀/(4π) ∫ J(x') × (x-x') / |x-x'|³ d³x'
B̂(k) = μ₀ i[k × Ĵ(k)]/|k|²   (k ≠ 0; transform convention explicit)
```
The finite thin circular filament is a **distributional line-current**; its Biot–Savart integral is the *line integral* `B=μ₀ I/(4π)∮ dl×R/|R|³`. By contrast the repo's rational `BS.biotSavart` deliberately **omits the Fourier `i`** and is modewise finite/periodic. To show same physical object with the line-current solver, one must fix Fourier sign and transform factors, real/complex phase, `k=0` mode, periodic vs infinite boundary conditions, distributional current continuity, μ₀/source scale, convergence near wire, and the precise regularisation/finite-wire cross section. These remain **unpaid**; the new Agda import adapter proves only directly **reused** algebraic results.

## Tested independent elliptic-current-loop reference (bounded)

For a circular filament radius `a`, axial displacement `z`, cylindrical radial coordinate `ρ > 0`, define `m=4aρ/((a+ρ)²+z²)`, `D²=(a-ρ)²+z²`, `Q=(a+ρ)²+z²`. Then the standard complete-elliptic-integral reference is
```text
B_z = μ₀ N I / (2π√Q) [ K(m) + (a²-ρ²-z²)E(m)/D² ]
B_ρ = μ₀ N I z / (2πρ√Q) [ -K(m) + (a²+ρ²+z²)E(m)/D² ]
```
Here `K,E` are complete elliptic integrals with **parameter** `m=k²` (not elliptic modulus `k`); `ρ=0` uses independent axial expression `B_z=μ₀ N I a²/[2(a²+z²)^(3/2)]`; the singular ideal wire is excluded. The off-axis formulas are long-established classical results and not claimed as invented by DASHI or SciPy's contributors. See [off-axis current-loop formula comparison](https://tiggerntatie.github.io/emagnet-py/offaxis/off_axis_loop.html), which carefully distinguishes SciPy's `ellipk(m)` convention.

**Independent local Python/NumPy/SciPy check**, distinct from the committed GitHub test blob: five off-axis points for an ideal `a=0.1m`, `N=256`, `I=1A` loop returned relative field discrepancies between `~2×10⁻¹⁶` and `~7×10⁻¹⁶` for 256 midpoint ring samples (smooth test sites away from the wire). On-axis cases also reproduced the closed form at floating-point rounding level. A pair of loops had finite-difference `|div B|×(0.1m)/|B|` `~1.3×10⁻⁶ to 3.1×10⁻⁶` for three current-free spatial sites with 0.1mm finite-difference step. These are numerical checks of a particular idealised model, not physical observations, and do not prove uniform convergence near the ideal wire or equivalence to the repository's exact Fourier carrier.

**Explicit regression source:** `python3 -m unittest scripts/test_psychotronics_field_loom_biot_savart_reuse.py -v` with `PYTHONPATH=scripts`; off-axis test uses `scipy.special.ellipk,ellipe`. All tests are source-written in PR #1242, but no checked-out GitHub blob was run in this container (its network cannot reach GitHub); independent numerical checks *were* executed locally. Agda not installed in the container, so no kernel theorem-check receipt is claimed.

## Consumer gates after this correction

- **S1**: field solver provenance and independently checkable analytic normalisation **pay the idealised test/calculation gap**, not instrument calibration/force. Continue force balance, covariance and exact source-stream→pair reduction; never claim a gravity result from magnetic forces.
- **S6**: reuse the existing `loop_b` responses in rank/failure placement; no new Biot–Savart integrator or new free field-pattern degrees of freedom. Add nonideal winding/core, sensor error and noise-weighted calibration **only** after real geometry and data exist.
- **G**: an exact Fourier transverse vector or numerical Maxwell divergence check cannot be promoted to a measurable change of `g`. Existing `AmyEskridgeAntigravityMeasurementObservationWeldExact` demands a gravitational observation channel and inspected laboratory source; still unpaid.
- **H/I attribution**: no retroactive historical proof that Pavlita, Amy, Ning Li, any missing/deceased scientist, BKM or Luo originated Biot–Savart or had a shared programme. Original claims, contemporaneous witnesses, institutional records, implementation and kernel-verified facts remain separate.
- **Stopping rule**: this source-side prior-art ownership gap is closed in documentation and import-only code. No further independent numerical coil *reimplementation* is justified unless a measured geometry presents a concrete shortcoming in the existing `loop_b` abstraction. The next information purchase is still calibrated physical coil measurements and source-grounded observation.

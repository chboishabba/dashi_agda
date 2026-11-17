# PV369 M1–M3 passive first-law and original [111] operator maximum cut — 17 November 2026

**PR:** https://github.com/chboishabba/dashi_agda/pull/1523 (draft). **Two independent physical goals remain OPEN:** (1) independently calibrated >50% **NET** aperture-solar-to-electric efficiency after all driver and auxiliary consumption; (2) a real, quantitatively distinguishable original-369 physical material/operator effect versus conventional crystal/strain/spin–orbit physics on a matched source. Photons, EQE, synthetic J–V, 4T output labels, thermal co-products, bio fuel, and Fourier basis transport do not themselves constitute either endpoint.

## M1: exact checkout status and new acceptance coverage

No local clone of PR branch is accessible in the present runtime because github.com DNS fails. `agda` is not installed. The exact source code was inspected and updated **using GitHub's branch file API**, not independently run as a full exact checkout. No GitHub workflows or commit statuses were present at last inspection. The Golden runner `scripts/check_pv_369_m1_local_acceptance.py` now enumerates **9 Python programs** and **12 Agda source targets**, and always returns nonzero (2) without Agda rather than mistakenly signalling kernel acceptance. Any source-written Python tests and local algebraic reproductions do not count as exact checkout acceptance.

## P5: NEW passive physical first-law discriminator, not another denominator wrapper

Existing original `scripts/check_pv_g173_same_sample_optics_eqe_iv_weld.py` had already checked R + sum(A_j) + T = 1 at each wavelength, 0≤EQE_j≤A_j, IV short-circuit J matching the integrated source EQE, then computed separate terminal maximum power. **Missing physical constraint**: a copied/fabricated IV curve could have maximum terminal output greater than the incident solar energy **actually absorbed by its own junction**, while passing the current/EQE/optics checks.

For a PASSIVE externally undriven junction and exactly the SAME illuminated spectral source:

```
P_absorbed,j = integral_lambda [I_lambda(lambda) A_j(lambda)] d lambda
P_gross_MPP,j <= P_absorbed,j
sum_j P_absorbed,j <= P_incident
```

The original P5 producer now computes each junction's absorbed-solar power directly from its existing measured optic files and rejects any `gross_mpp_W_m2 > per_junction_absorbed_solar_W_m2` with an explicit floating numerical tolerance. The outgoing source receipt now carries `per_junction_absorbed_solar_W_m2` and `passive_mpp_le_absorbed_solar_checked=true`. The P5 selftest adds an original optical passive-energy sanity test and a physically impossible 20× voltage (same original EQE Jsc) negative test. This catches forbidden energy creation in a fitted source J–V curve that had correct photon number and short-circuit current.

Both **P7** consumers independently recheck source absorbed solar per junction and sum source absorbed ≤ incident: `scripts/check_pv_369_worst_case_power_intervals.py` and `scripts/check_pv_369_unsampled_iv_mpp_envelope.py`. P7 rejects modified/fabricated JSON reporting extra gross MPP or missing first-law receipt, instead of assuming P5's earlier execution is trustworthy. Three new adversarial P7 bound-receipt cases reject absent P5 passive-energy flag, source MPP > absorber power and duplicated incident sunlight.

**Independent numerical crosscheck:** for existing synthetic P5 400–1000nm, 600 W/m² integrated constant solar source, four equal A=0.2 absorbers receive exactly **120 W/m² apiece**. Existing EQE=0.16 and source linear IV gives Jsc≈54.200455 A/m² and gross MPP≈13.550114 W/m² apiece, pass. At 20× fixed-charge-output voltage, gross MPP≈271.002276 W/m² >120 W/m², hence **reject**. This is an independently evaluated simple case; the exact committed producer/consumer script tests were NOT run from the current GitHub checkout.

**Formal:** new `DASHI/Physics/Photovoltaic/PV369PassiveAbsorbedEnergyCeilingExact.agda` derives `grossTerminalElectricalMPP <= absorbedSolarEnergy` from a SOURCE-admitted energy conservation equality `absorbed ≡ gross + otherLoss`, using original `Circuit36927RecoveryEnergyBoundExact` and its `≤-append`/equality transport. With previous `PV369NetHalfThresholdExact` and `PV369IntervalRobustAcceptanceExact.leTrans`, it then derives contradiction from a claimed strict passive `gross > absorbed`. The source physical energy ledger is not inhabited. No Agda Golden kernel proof claimed. Reused original P5/TOE owners, no ESD modifications.

**Physical scope:** For P3 externally driven optical systems, assign measured external work on the SAME physical junction and net it out; a passive P5 receipt is not the right model. For P4 multiplication, extra charge does not create extra photon energy: the absorbed optical energy still bounds useful output absent additional work. For a GaInP/GaAs *series upper tandem* and separately extracted Si group, P5's per-output photon partition must be replaced with an original **3 absorber → 2 electrical group** bridge, not by assigning the two independent output groups four invented absorbers.

## M3: same-object original [111] orbital operator and scalar non-distinction

Source owner `DASHI/Physics/Photovoltaic/GaAs111BirPikusC3vFiniteExact.agda` models the spinless [111] Bir–Pikus valence 3×3 orbital block in Cartesian XYZ with common diagonal D and shear off-diagonal S:

```
H = [[D,S,S], [S,D,S], [S,S,D]]
A1 = (1,1,1)   eigenvalue D+2S
E  = 2d orthogonal subspace  eigenvalue D−S (double)
```

**Original exact atomic** `AtomicPeriodicTable369P2CoulombExecutionExact.agda` computes `Vee=(21/128)I₃` in a *different selected hydrogenic common-spin 2p²* sector. The numerical scalar is **NOT to be physically added to a GaAs strain Hamiltonian across these different Hilbert spaces**. It is only a separate mathematical scalar counterexample, proving that a common shift alone cannot split the degenerate E representation. Under ordinary spinless C3v, the source [111] shear matrix *already* respects both 120° rotation and mirror. Therefore seeing `A1 + E` splitting in this block is not evidence of an independent 369-specific prediction.

New `scripts/check_pv_369_bp111_scalar_coulomb_distinction.py` uses **SymPy exact symbolic matrices** to check C3 order, mirror action and conjugacy, source Bir–Pikus covariance, exact A1 and two E eigenvectors/eigenvalues, and a separate 21/128 scalar perturbation counterexample (without identifying the physical sectors). It includes a physically distinct but generic anisotropic source perturbation as a negative control: merely breaking C3v is not uniquely '369'. Independently reproduced representative SymPy matrix identities locally; exact committed 19 test suite unexecuted.

New `DASHI/Physics/Photovoltaic/PV369BirPikusA1RowSumExact.agda` imports the original physical [111] `BP.bp111Entry` source matrix, and **derives** all three exact Cartesian row sums `D+(S+S)` by standard Nat associativity/commutativity. This is a nonnegative **matrix-shape identity only**: signed deformation-potential energies, full valence spin–orbit, conduction band, corrected Bahder eight-band and exciton/optical polarization/terminal IV are separately required. The finite original A1 proof is added to the TOE and the local Golden runner. No fabricated oscillator strengths or terminal gain.

**Next high-alpha physical M3 producer**: explicitly source-measured same-material [111] strain and piezo, full corrected eight-band (Bahder) spectral eigensystem with the proper energy-reference convention and source wavefunction sewing, plus independently specified **369-distinct Hamiltonian operator** and preregistered polarization/angle-resolved absorption or transport prediction after matched conventional control. Mere source C3v symmetry, parameter refit, basis permutation, or addition of the 21/128 hydrogenic scalar cannot establish distinct 369 physical effects.

## Roadmap status

- **M1:** 9 Python/12 Agda pinned local acceptance source-listed; exact run OPEN.
- **P5:** passive per-junction absorbed-solar first-law inequality in Python source + exact conditional Agda theorem; complete execution/physical evidence OPEN.
- **P7:** original raw JV, optics, EQE + signed losses; two consumer first-law rechecks added; strict independent >50 measurement OPEN.
- **M2:** Green v68 actual conventional 3J/2-output 4T source printed-precision/architecture audit completed, original calibrated stabilized IV/photocurrent data OPEN.
- **M3:** original [111] exact A1 row and spinless symbolic E degeneracy and original p² scalar no-369-gain negative control added; real 369-specific material physics OPEN.
- **P3/P4/P6:** remain parallel, separately sourced routes with full energy ledger; do not treat heat/fuel output as net electrical work.

Reproduction once the actual pinned branch is available:

```bash
python scripts/check_pv_369_m1_local_acceptance.py --require-agda \
  --output m1_pv369_exact_local_acceptance.json
```

This local receipt must be passed before promoting formal results; source-write operations, web primary records and independent small arithmetic checks are not a substitute for native Golden.

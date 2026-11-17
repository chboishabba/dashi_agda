# P5/P7: source-matched 4T/2T optical-EQE-IV handoff — 17 Nov 2026

**Goal remains two simultaneous physical endpoints:** (A) independently verified **net aperture-solar-electric efficiency >50%**, and (B) an **original 369-derived material/operator change** that beats a conventional same-source matched control. Model-only 4T/2T configurations are NOT observed 369 gain. Thermal and chemical outputs cannot be added to an electric numerator. Preserve separate P1 material, P2 transport, P3 RF/Floquet, P4 carrier multiplication, P5 optics, P6 BH4 biology and P7 independent certification.

## Reused rather than recreated

- Original `scripts/check_pv_astm_g173_radiative.py`: complete 2002-row four-column AM1.5G source checksum; incident power 1000.37065557 W/m², NOT a source of actual diode absorption or observed JV.
- `DASHI/Physics/Semiconductor/Device/SpatialContinuityRecombinationExact.agda` and `FiniteScharfetterGummelFluxExact.agda`: conservation/transport interfaces. Their finite synthetic fixtures are not actual calibrated mobility/contact data.
- `DASHI/Environment/SolarOpticalSiteFibreCrossPollinationExact.agda` and `CanopySpectralRadiativeTransferExact.agda`: wavelength/angular/site provenance and distinction between radiance and device response, without identifying canopy photons with semiconductor carrier measurements.
- `PVPrimaryConversionMaxCutExact.agda`, `PV369NetHalfThresholdExact.agda`, `PV369G173MultiJunctionLossFrontierExact.agda`: energy balance, strict net >50% and previous *heuristic ideal-model* headroom.

## Implemented executable measured-data adapter

New `scripts/check_pv_g173_same_sample_optics_eqe_iv_weld.py` supplies a **fail-closed** computational adapter to actual future measurements. It does NOT fetch, simulate or invent any measured specimen.

Run on a genuine sample using:

```sh
python scripts/check_pv_g173_same_sample_optics_eqe_iv_weld.py \
  --spectrum /path/to/astm_G173_2002_row.csv \
  --optics /path/to/same_sample_R_A1_A2_A3_A4_T.csv \
  --eqe /path/to/same_sample_EQE1_EQE2_EQE3_EQE4.csv \
  --iv /path/to/cell1_V_J.csv /path/to/cell2_V_J.csv \
       /path/to/cell3_V_J.csv /path/to/cell4_V_J.csv \
  --converter-efficiency 0.97 0.97 0.97 0.97 \
  --auxiliary-w-m2 0 --drive-w-m2 0 --recovered-w-m2 0 \
  --output measured_device_receipt.json
```

The **4-column original G173** spectrum is accepted directly only with the 2002-row source integrity/irradiance checksum. A custom *observed* 2-column wavelength and irradiance spectrum is also allowed, with explicit provenance to be separately authenticated. Spectral input must have an **identical wavelength grid** across optics/EQE. There is deliberately NO implicit wavelength interpolation.

The optical file is a per-wavelength exclusive partition `R+A1+A2+A3+A4+T=1`; `0<=EQE_i<=Ai<=1` and no double-counting of photons. Units: irradiance W/(m² nm), wavelength nm, current density A/m², voltage V, terminal power W/m². `Jsc_i = q∫Phi_solar(wavelength)*EQE_i(wavelength) dlambda` is compared with `J_i(V=0)` from each independent **measured illuminated IV**; >2% difference (default) is rejected as inconsistent. This does not authenticate uploaded data and does not fit recombination.

For **4T**, use each curve's exact piecewise-linear `max_V (V J_i(V))`, multiply by each specified converter efficiency between zero and one, then subtract actual reported auxiliary/drive input and add recovered electrical drive subject to `0<=recovered<=drive`. For **2T**, invert the **same individual** J-V curves and compute `max_I I*Σ_i V_i(I)`, with each piecewise-linear segment's quadratic extremum included. This is an IDEAL lossless series *prediction*: individual 4T measurements do not establish performance of an assembled two-terminal stack. Contacts/interconnect losses for the 2T assembly are not sourced and must be added, not inferred. Neither is a measured terminal Pmax until verified device provenance and voltmeter/currentmeter sources are independently checked.

The adapter refuses missing input families, nonmonotone/negative JV, inconsistent Jsc, unphysical fractions, recovered drive greater than input and efficiencies above 1. The output field `real_world_certified=false` is always false: an independently attested physical claim must be attached externally, not self-issued by a numerical model.

**Independent executed local validation:** `scripts/check_pv_g173_same_sample_weld_independent_fixture.py` (exact reproduced test file), **25/25 PASS** on synthetic 4J data and adversarial predicates. Its perfectly flat synthetic spectrum 400–1000nm, per-wavelength R=0.1, each Ai=0.2, T=0.1, EQE_i=0.16, and linear 1V J-V curves give gross four-terminal power **54.200455 W/m²**, net **50.574442 W/m²** after illustrative 97% converters and 2 W/m² auxiliaries, under 600 W/m² incident: **8.429% synthetic net**, NOT a device. This is deliberately a negative control, not a successful >50 result. The full committed measured-data adapter itself was source-written and has not been executed from a fresh GitHub checkout; independent local receipt checks exercise its mathematical contract and rejection conditions.

## Formal P5/P7 source-gated join

`DASHI/Physics/Photovoltaic/PV369FourJunctionOpticsToMeasuredIVExact.agda` imports the existing physical owner modules and defines `FourJunctionPhotonBin` with source photon count partition, reflected/transmitted and four **exclusive absorber** counters, each collected-electron count ≤ corresponding absorbed count for the P4-unmodified baseline. A synthetic exact 100-photon fixture proves only arithmetic, not a physical measured absorber. For carrier multiplication, P4 needs an independently evidenced greater-than-one quantum yield with proper energy conservation, not a forged EQE≤Ai assertion.

`OpticalToTerminalSourceWeld` requires measured same-site solar fibre, wavelength-specific bin witnesses, spectrally observed reflectance/absorption/EQE, independently observed per-cell illuminated IV, same-source optical/Jsc closure, continuous carrier transport, real 4T converter/auxiliary costs and the original strict net PV acceptance. **All physical producers remain open**. Its universe level is `Set₂` because the original `SolarOpticalSiteFibre` lives in `Set₁`. This revealed and repaired an older `Set₁` universe mismatch in `GaAs111OpticalDeviceSourceWeldExact.SameArtifactPVConversionWeld` as well; native Agda kernel acceptance still pending.

## What we learned about the 369 claim

The 369-derived Fourier/SALC/triadic labels alone cannot enhance the score of the identical device with identical source and IV; earlier `Atomic369BasisTransportNoFreeGainExact` gives the exact no-free-coordinate-gain abstraction. The **next material test must supply an actual changed Hamiltonian, absorption/EQE or carrier transport operator** from the original 369 physical construction, and submit the resultant measured terminal net energy against a conventional identical-aperture baseline.

## Highest-alpha next cuts

1. Real same-wafer one-sun AM1.5G per-junction 4T stack specimen: original reflectance/transmittance/absorptance spectral rows and EQE for ALL cells; original measured illuminated V-J for each contact; converter/MPPT losses and all auxiliaries with signed calibrated power. Reconstruct the P5/P7 actual measured receipt. No such dataset was present in this round; the source weld stays uninhabited.
2. From the same sample, compute both 4T and conditional ideal-series 2T response with instrument uncertainty and source spectral/angular effects. Find actual loss partition relative to **a reproducible conventional no-369 4J or 5J model**, not the generic ideal optimizer.
3. P1d original corrected Bahder 1990/1992 operator, consistent real GaAs/InGaAs material basis, measured quantum-well/strain/optical response. Need a 369-specific preregistered prediction not already entailed by Td→C3v.
4. P3 RF drive, P4 multiplication, P6 BH4 photosystems retain separate energy-certified experiment lanes and are NOT blocked on a GaAs QW solution.
5. Independently verify >50% **net** power plus strict matched conventional-vs-369 physical advantage on a single actual candidate. Until then, *none* of the numerical model outputs demonstrates >50%.

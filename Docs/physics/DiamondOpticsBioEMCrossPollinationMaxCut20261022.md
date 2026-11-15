# Diamond NV optical readout × prior DASHI optics / optogenetics max-cut

## Existing source owners directly inspected
- `DASHI/Physics/Optics/OpticalPhenomenaKernelBridge.agda`: Maxwell phase propagation, Rayleigh constitutive response, optical approximation-regime gates; no NV-specific fitted optical constants.
- `DASHI/Physics/Semiconductor/Device/LitavisSPADMultimodalObservationExact.agda`: source-attested SPAD photon-count/timestamp/histogram architecture, not an experimentally validated detector for the Omar diamond MCG instrument.
- `DASHI/Physics/Optics/OpticalSurfaceManufacturingToleranceExact.agda`: design-to-fabricated-optics conformance and metrology; cannot substitute observed laser/fibre photon collection efficiency.
- `DASHI/Biology/LiMinyongPhotopharmacologyBidiExact.agda`: reversible light-control/molecular-target readout surface; distinct from classical opsins and NV fluorescence.
- `DASHI/Biology/OptogeneticMemoryObservationBoundaryExact.agda`: optical intervention -> neural response -> behaviour with explicit evidence adequacy.
- `DASHI/Biology/Levin/MitopolaritonTwoModeSpectrumExact.agda`: candidate mid-IR mitochondrial light–matter spectral mode, separate from NV laser pump and opsin actuation.

## Newly committed implementation
- `DASHI/Physics/QuantumSensors/NVOpticalPhotonReadoutExact.agda`: finite optical readout carrier with detector bright/dark/background expected counts, explicit normalized two-population partition, symbolic resonance-to-population response supplied by a selected source calibration. The canonical population constructor proves exact normalization; it does *not* prove 0<=p<=1, nor positivity of photon means.
- `DASHI/Physics/QuantumSensors/NVOpticalGaugeBioEMBridgeExact.agda`: composes existing finite triangle electromagnetic curvature, NV axial spin-one resonance and the optical photon-mean readout. Proves that gauge-equivalent edge potentials yield identical predicted photon means, conditional on the provided response model. No empirical data are inferred by congruence.

## Cross-pollination architecture
Three independent light channels:
1. NV green optical pumping + red/near-IR fluorescence collection + microwave interrogation (actual bands/device specifics source-calibrated).
2. Visible light-sensitive opsin neuronal intervention and downstream electrophysiology/behaviour.
3. Mid-infrared illumination and speculative coupled vibrational/electromagnetic modes in mitochondrial cristae.

Share *causal experiment accounting* (intervention, competing hypotheses, detector timing, photon statistics, physical optics regime, thermal controls), not undemonstrated mechanism equality. The paper-specific diamond NV instrument may not use SPADs; that device owner is a candidate measurement adapter only.

## Highest-value next physical cut
1. Verify the exact fluorescence photon likelihood (Poisson or more complete detector model), including positivity and normalized optical-state populations on a constructive real carrier and source-identified laser/microwave pulse sequence.
2. Link collection optics / NA, scattering, optical aberration, detector QE, photon timing, background and device response to actual calibrated MCG optical readout, with objective noise/error estimates.
3. Connect optical measurement to spatial cardiac currents and frequency/time-domain reconstruction, with actual human instrumentation geometry.
4. Distinguish optogenetic actuation wavelengths vs NV pump/readout vs mid-IR bioenergetic exposure; use shared sham/thermal/phototoxicity controls, blinded perturbations and pre-registered outcomes.
5. If using KK, require physical 5D-to-4D derivation plus same-object electromagnetic current/field map; gauge invariance in a toy finite cochain does not establish diamond sensor physics.
6. Ground crystal symmetry and full transverse spin matrices in `OrdinaryComplexQutrit`, not only the local symbolic script.

## Verification, attribution
Source-written modules in PR #1238 only; no kernel/CI check at user request. The algebra of spin-1, optics, Maxwell propagation, and quantum measurement are classical sources; distinct original biological experiments retain their authorship. No empirical optical efficiency, detector dark counts, ATP effect or engram experience is claimed.

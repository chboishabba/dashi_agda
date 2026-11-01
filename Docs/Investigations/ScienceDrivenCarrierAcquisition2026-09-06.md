# Science-driven carrier acquisition — 2026-09-06

## Purpose

Continue the missing/deceased-scientist investigation and the memorial science formalisation together.

The science is used to identify the technical object that actually carries capability.  A capability carrier can then generate evidence-acquisition questions about possession, distribution, replacement difficulty, observer visibility and event linkage.  None of those downstream propositions are inferred from scientific importance alone.

## Deepened generic science

### Nickel-base superalloy process state

New owner: `DASHI/Physics/Materials/NickelBaseSuperalloyProcessStateDepthExact.agda`.

Sources:
- Samuel J. Galpin, "A review of microstructure phenomena during manufacture of polycrystalline Ni-based superalloys", *Materials Science and Technology* 38(16), 2022, DOI `10.1080/02670836.2022.2069332`.
- N. D'Souza et al., "On the Evolution of Primary Gamma Prime Precipitates During High Temperature and High Strain Rate Deformation and Subsequent Heat Treatment in the Ni-Based Superalloy, RR1000", *Metallurgical and Materials Transactions A* 50, 4205-4222 (2019), DOI `10.1007/s11661-019-05330-w`.
- Z. Yao et al., "Effect of rejuvenation heat treatments on gamma prime distributions in a Ni based superalloy for power plant applications", *Materials Science and Technology* 29(7), 2013, DOI `10.1179/1743284712Y.0000000199`.

The implemented chain is:

`nominal composition -> thermomechanical/heat-treatment history -> gamma/gamma-prime/grain/TCP/segregation state -> temperature-dependent properties`.

Key firewall: same nominal composition does not imply same microstructure.

Investigative consequence: the likely reconstructive carrier is not merely the published composition window.  It is the exact process state: heat treatment, deformation/cooling history, gamma-prime size/fraction/coherency, grain-boundary state, segregation/porosity and qualification data.

### Fission instrumentation/control qualification

New owner: `DASHI/Physics/Nuclear/FissionICQualificationReliabilityDepthExact.agda`.

Sources:
- NASA Glenn, "NASA Fission Instrumentation and Controls Workshop", 2024.
- NASA, "NASA 40 kW Fission Surface Power", NTRS `20250008475`, 2025.

The programme-level maturation coordinates include neutron fluence, gamma dose, temperature, 10-year operation, measurement integrity, probability of failure, accelerated testing/physics-of-failure, autonomous diagnosis and automated off-normal response.

Key firewall: radiation-hard does not imply mission-qualified.

Investigative consequence: acquisition should target component-specific qualification ownership, calibration-drift curves, accelerated-life/physics-of-failure models, fault-injection results, failure envelopes and system-level probability-of-failure evidence.

### Reduced kinetic plasma validity and closure

New owner: `DASHI/Physics/Plasma/ReducedKineticValidityClosureDepthExact.agda`.

Source:
- N. F. Loureiro et al., "Viriato: A Fourier-Hermite spectral code for strongly magnetized fluid-kinetic plasma dynamics", *Computer Physics Communications* 206 (2016) 45-63, DOI `10.1016/j.cpc.2016.05.004`.

The owner makes the model-validity state explicit: strong-guide-field/reduced ordering, formal KREHM electron-beta ordering, retained kinetic physics, finite Hermite truncation, closure/dissipation and convergence.

Key firewall: numerical convergence does not imply asymptotic-model validity.

Investigative consequence: first establish whether any reconstructive residual is actually non-public: exact source artifact, application-specific closure/dissipation, convergence/resolution receipts and target-regime configuration.  Deep public mathematics is a control against over-promoting hidden-knowledge claims.

### Cryogenic messenger-tag perturbation

New owner: `DASHI/Chemistry/Spectroscopy/CryogenicTagPerturbationAndAssignmentDepthExact.agda`.

Sources:
- Christopher J. Johnson et al., "Communication: He-tagged vibrational spectra ... quantifying tag effects in cryogenic ion vibrational predissociation spectroscopy", *J. Chem. Phys.* 140, 221101 (2014), DOI `10.1063/1.4880475`.
- "Vibrational Predissociation Spectroscopy of Cold Protonated Tryptophan with Different Messenger Tags", *J. Phys. Chem. A* 122 (2018) 8037-8046, DOI `10.1021/acs.jpca.8b07532`.
- "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects", *J. Phys. Chem. A* 128 (2024) 7137-7144, DOI `10.1021/acs.jpca.4c03552`.

The measurement state now contains tag identity, binding energy, number/site, trap temperature, dissociation threshold, conformer population and tag-dependent action yield.

Key firewall: action intensity is not definitionally a linear absorption intensity, and different messenger tags need not produce identical measured spectra.

Investigative consequence: mission-relevant spectroscopy know-how should be sought in apparatus calibration, tag-response models, conformer libraries, cross-tag comparisons and mixture-specific discrimination/false-positive datasets rather than in the generic public spectroscopy protocol.

### Flash-radiography forward/inverse model

New owner: `DASHI/Physics/Accelerators/FlashRadiographyForwardInverseUncertaintyExact.agda`.

Sources:
- "A stochastic approach to quantifying the blur with uncertainty estimation for high-energy X-ray imaging systems", *Inverse Problems in Science and Engineering* (2015), DOI `10.1080/17415977.2015.1046859`.
- A. Walker, A. Friou, K. Ginsburger, "High-energy X-ray spectrum reconstruction: solving the inverse problem from optimized multi-material transmission measurements", *Frontiers in Physics* 11 (2023) 1257548, DOI `10.3389/fphy.2023.1257548`.
- S. Wei et al., "Uncertainty Quantification of Density Reconstruction Using MCMC Method in High-Energy X-ray Radiography", *Communications in Computational Physics* 27 (2020) 1485-1504, DOI `10.4208/cicp.OA-2019-0060`.
- Q. Li et al., "Uncertainty Quantification Enforced Flash Radiography Reconstruction by Two-Level Efficient MCMC", *IEEE Transactions on Image Processing* 30 (2021) 7184-7199, DOI `10.1109/TIP.2021.3101929`.

The forward state now explicitly includes source spectrum, focal spot/source blur, detector PSF/response, geometry, attenuation, density, scatter and photon noise.  The inverse state includes priors/regularisation, density/spectrum/blur reconstruction and posterior uncertainty.

Key firewall: a radiograph does not uniquely determine density without calibration/model assumptions.

Investigative consequence: the highest-value carrier is the calibrated experiment-specific forward/inverse chain and uncertainty model, not public accelerator architecture.

## Science-driven investigative compiler

New owner: `DASHI/Culture/MissingDeceasedScienceDrivenAcquisitionExact.agda`.

Current mechanistic priority order:

1. **Highest:** flash-radiography inverse-chain possession and observer visibility.
2. **High:** alloy process-window possession/replacement.
3. **High:** fission I&C qualification/failure-map possession/replacement.
4. **Medium:** action-spectroscopy apparatus/tag/mixture calibration and replacement.
5. **Control:** plasma source/closure/configuration non-publicness, because much of the numerical architecture is already public.

This is a search-priority ordering only.  It is not a targeting, motive or causal-event ordering.

## Event boundary

The investigation still requires independent receipts for every downstream step:

`scientific carrier -> person/role possession -> concentration/replaceability -> observer visibility -> selection/targeting -> event linkage`.

No step is inferred merely because the previous one is true.

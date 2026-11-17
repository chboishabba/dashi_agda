# PV >50% / physically distinct 369: quantum-well confinement and strict endpoint max-cut
Date: 17 November 2026. Owner: [DASHI draft PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523).

## Goals and non-promotion

Primary endpoint: **independently measured >50% NET aperture-normalized solar-to-electric power/energy conversion**, correct source spectrum, duration, concentrator normalization and electrical RF/thermal/auxiliary consumers. Separate secondary coproducts (chemical, excitonic, fuel, heat) remain energy-accounted but do not count as electrical numerator. A genuine *369-specific* result must predict a physical state/operator/observable that differs from a conventional same-material C3v model and survives a same-source net-Pmax matched control. A mere 3/6/9 codename, finite Fourier representation, permutation, SALC basis or triple degeneracy is not enough.

Separate research branches retained: P1 full source-matched atomic/quantum-dot material and corrected Kane–Bir–Pikus; P2 measured absorption/EQE/transport/JV; P3 nonlinear Stark/Floquet/Franz–Keldysh with signed RF work; P4 carrier multiplication/fission with useful voltage; P5 photonic films/angle-selective routing and multi-junction current matching; P6 BH4/photosynthetic electron/redox/fuel engineering; P7 independent certified net 50+ result. Thermal heat pump/cooling/ORC is auxiliary, not the conversion mechanism.

## P1d: move the 1988 QW mass discrepancy into confinement energy

Primary source: Molenkamp et al. PRB 38, 4314(R), DOI [10.1103/PhysRevB.38.4314](https://doi.org/10.1103/PhysRevB.38.4314). Published [111] HH QW-inferred mass 0.70m0; nominal bulk Gamma Luttinger curvature inverse (γ_1-2γ_3=1.12) yields (m_{HH}=25/28=0.892857m0). These are DIFFERENT physical inverse problems; exact disagreement is a negative control, not automatic disproof of either the original 1988 8-band QW fit or standard gamma compilation.

Original contextual source: R. Eppenga and M. F. H. Schuurmans, *Theory of the GaAs/AlGaAs quantum well*, *Philips Technical Review* 44(5), 137–149 (November 1988), [contemporaneous full volume](https://www.worldradiohistory.com/Archive-Company-Publications/Philips-Technical-Review/80s/Philips-Technical-Review-1988.pdf). Describes envelope-function confinement in 1–10nm GaAs/AlGaAs wells and importance of hole-band mixing. The PDF extracted text was read, but an attempted page screenshot returned 403; original figure-level sample extraction not claimed.

Illustrative 1D FINITE square QW with constant hole masses, symmetric 0.2eV barrier, barrier mass 0.9m0, and BenDaniel–Duke matching (tan(kL/2)=(m_w/m_b)κ/k). These arbitrary barrier parameters ARE NOT Molenkamp specimen metadata. Computed levels above the well bottom:

| L | E_ground for m=0.70m0 | E_ground for m=25/28 m0 | Delta |
|---|---:|---:|---:|
| 5 nm | 14.023meV | 11.949meV | 2.074meV |
| 8 nm | 6.366meV | 5.279meV | 1.087meV |
| 10 nm | 4.294meV | 3.525meV | 0.769meV |

All source-independent local equivalents of the committed script passed **40/40** boundary, width, barrier, positive-state and mass controls. Owner `scripts/check_gaas_111_qw_mass_confinement_cut.py`. Exact Agda source `GaAs111QuantumWellConfinementExact.agda` imports the previous `GaAs111MeasuredMassAdversarialExact` mass inequality and leaves actual same-specimen well/barrier parameters, 8-band envelope boundary conditions, exciton fitting and loaded PV collection uninhabited. No full QW 1988 spectral calibration claimed.

## P7: repaired strict acceptance and constrained loss margin

`PVPrimaryConversionMaxCutExact.MatchedDrivenPVGain.positiveNetElectricalGain` previously required only weak <= and could admit equal net power; it now requires a strict successor bound `suc passiveEffective <= drivenEffective`, with signed RF in and recovered RF both included. Native Agda kernel check remains open.

`PV369NetHalfThresholdExact.agda` imports the existing motor bound and PV source, carries a measured common-aperture incident solar and electrical gross/drive/recovery/aux fields, a net electric port balance, and the **strict** threshold `suc incidentSolar <= netElectric+netElectric` in the same discrete energy/power quantum. It proves generic `suc n <= n -> False`; equality at 50.0% cannot pass. It does NOT construct a physical witness: calibrated meters, time/spectral/aperture consistency, independently observed loaded JV and certified output remain separate.

The existing **hypothetical 3J, 2-terminal, ideal radiative, one-sun G173 model** had η≈51.741%, numerical gap optimisation, not globally certified. Its arithmetic headroom is 1.741 percentage points = 17.416 W/m² for G173 global 1000.370656W/m², only 3.3648% of *ideal electrical output*. This is all that would remain for combined optical, current mismatch, resistive, nonradiative, manufacturing, temperature and auxiliary losses. It is a *target-model arithmetic budget*, not a real device margin. 47.6% independently certified 665-sun four-junction CPV and one-sun 3J ideal have different incident spectra/concentration; do NOT subtract their values directly.

## Physically distinct 369 versus relabelled symmetry

`Atomic369BasisTransportNoFreeGainExact.agda` already proves a coordinate/label isomorphism transports arbitrary observable readouts unchanged; previous 35 local matrix tests confirm same-system unitary conjugation of Hamiltonian, optical dipole, density and readout is not a PV mechanism.

New `PV369MatchedDevicePhysicalAdvantageExact.agda` requires both:
1. a same-aperture/spectrum materially sourced conventional device and proposed 369 device with strictly greater **NET** electrical output after drive and auxiliary costs;
2. a physically measured >50% net solar-electric candidate with exactly the same identity as the improved case.

It proves that equality of source-observable net outputs (the consequence of a mere coordinate relabeling) and strict advantage cannot coexist, by reusing the original Nat strict inequality obstruction. This is a formal physical-*acceptance interface*, not an inhabited 369 physical advantage.

## Strict remaining work / highest-alpha next cut

1. **Agda Golden kernel** verify new sources and full TOE import closure. Current environment has no Agda binary; don't claim acceptance or merged PR.
2. Fetch full Molenkamp paper experimental well widths, AlGaAs compositions, temperatures, strain/exciton PLE data; implement finite-barrier **spinful 8-band** envelope eigenproblem including mass discontinuities and exchange. The toy 1D finite well is only a sensitivity comparator.
3. Original complete Bahder 1990 equations plus corrected 1992 N blocks, R, a, P/Q/R/S, k×strain and strain spin-orbit terms in a consistent SAME eight-state Γ basis. Keep source temperature and valence band reference consistent.
4. Measured same-sample absorption/EQE, radiative+nonradiative recombination, angular source/emission, contacts, actual loaded PV MPP and active drive energy.
5. A preregistered 369-specific material parameter, operator or spectroscopy difference versus a conventional same-material non-369 model, with separate source and held-out validation.
6. Only after actual net Pmax and loss budget: stack/multi-junction field calibration and independent >50% certification. Continue P3/P4/P5/P6 in parallel; do not overindex the single GaAs lane.

**Provenance/governance:** Original physics papers own published phenomena, DASHI original atomic ternary/369 and quantum producers own their prior construction; imports only; no ESD modifications. User's Agda golden/local verification policy governs acceptance.

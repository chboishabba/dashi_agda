# Missing/deceased scientist science + boundary implementation — 2026-09-05

## Purpose

The knowledge-release investigation now carries the underlying science explicitly. A boundary receipt is not allowed to float free of the technical object that crossed it.

Generic owner:

- `DASHI/Core/ScientificMechanismEvidenceBidiExact.agda`

It distinguishes:

- established background law;
- constitutive/engineering mechanism;
- source-proposed mechanism;
- mathematical reformulation;
- numerical method;
- benchmark/validation test;
- experimental observation;
- source interpretation;
- preliminary consistency claim.

Key firewall:

`source mechanism != established physical law != preliminary observation != independent replication != numerical benchmark`.

## POAMS

Owner: `DASHI/Physics/POAMSScientificMechanismBoundaryExact.agda`

Source-backed scientific content:

- NASA/MSFC reformulated POAMS into a model predicting a non-Newtonian spin-coupled force associated with nucleon alignment;
- rudimentary/preliminary data were reported as appearing consistent with the prediction;
- NASA explicitly called for further work with better methodology and measurement.

Status:

- reformulation: SOURCEBACKED;
- preliminary experiment: SOURCEBACKED/PRELIMINARY;
- independent replication: OPEN;
- established new force: NOT OWNED.

Highest scientific leaves:

- quantitative mechanism-specific scaling;
- calibrated force/torque uncertainty budget;
- vibration/electromagnetic/thermal/mechanical controls;
- independent replication.

## Jacinto/Hardwick burn-resistant alloy

Owner: `DASHI/Physics/RezaBurnResistantAlloyScienceExact.agda`

Public patent science now includes:

- composition family: Ni 55-75 wt%, Co 12-17, Cr 4-16, Al 1-4, Ti 1-4;
- high Ni -> burn-resistance design role;
- Co -> solid-solution strengthening;
- Cr -> oxidation resistance;
- Al/Ti -> gamma-prime strengthening;
- minor C/B/Zr additions -> grain-boundary strengthening role;
- vacuum induction melt -> vacuum arc remelt -> mechanical working;
- engineering target = simultaneous high-pressure-oxygen burn resistance + high tensile strength.

Open scientific leaves:

- heat-treatment schedule;
- gamma-prime phase fraction/size distribution;
- grain size/phase stability;
- raw burn-test and tensile-test datasets;
- quantitative microstructure -> property model.

This also clarifies the patent boundary: publication externalised real composition/mechanism/process knowledge, but not necessarily the full microstructural/process-control know-how.

## LeBlanc / FSP-SNP instrumentation and controls

Owner: `DASHI/Physics/LeBlancFissionInstrumentationControlScienceExact.agda`

The public science/engineering object is represented as the chain:

`sense -> signal conditioning -> state estimation -> requirement comparison -> actuation -> protection -> telemetry -> fault diagnosis`.

Public NASA material also exposes:

- the live FICS/CINDI database concept;
- FICS Working Group;
- draft technology growth/maturation path.

Open science/engineering leaves are component-specific qualification under radiation, temperature, lifetime, drift, reliability and integrated fault-tolerance requirements.

Boundary consequence: public technology-maturation architecture does not imply that database contents, detailed component qualification evidence or flight design files are public.

## Loureiro / Viriato

Owner: `DASHI/Physics/Plasma/LoureiroViriatoNumericsScienceExact.agda`

Formalised architecture:

- KREHM and KRMHD reduced models, with RMHD limit;
- Strang/Godunov operator splitting;
- parallel options: second-order MacCormack or TVD RK3 + seventh-order upwind flux scheme;
- perpendicular pseudo-spectral method;
- Hermite spectral representation in parallel velocity space;
- linear/nonlinear benchmarks including 2D/3D Orszag-Tang-type decay.

Firewall:

`benchmark success != universal physical validity`.

The remaining boundary leaf is still whether the actual Viriato source artifact was publicly released and whether any prior bounded state existed for that same code object.

## Chavez / DARHT-Scorpius

Owner: `DASHI/Physics/ScorpiusRadiographicAcceleratorScienceExact.agda`

Formalised public chain:

`pulsed power -> electron injection -> induction acceleration -> beam transport -> conversion target -> bremsstrahlung x-ray pulse -> object transmission -> detector image -> hydrodynamic inference`.

The accelerator/radiography mechanism is conventional physics. The sensitive layer can instead reside in experiment geometry, material state, timing, detector calibration, reconstruction, inversion and stockpile-specific interpretation.

Open scientific leaf:

- experiment-specific forward/inverse model and uncertainty chain.

Boundary consequence:

`public accelerator architecture != public experiment-specific classified weapons data`.

## Maiwald / cryogenic action spectroscopy

Owner: `DASHI/Physics/MaiwaldActionSpectroscopyScienceExact.agda`

Formalised chain:

`electrospray ionisation -> ion guides -> cryogenic trap -> buffer-gas cooling -> messenger tagging -> mass selection -> tunable IR excitation -> photodissociation -> fragment detection -> action spectrum -> structure assignment`.

Source-backed results include:

- valine messenger-tag photodissociation;
- distinguishable IR signatures for deprotonated valine vs aminovaleric acid despite same mass/composition;
- DFT-assisted structure assignment;
- messenger-tag binding/temperature tradeoffs.

Open scientific leaves:

- complex-mixture selectivity/sensitivity;
- realistic planetary matrices and radiation histories;
- mission-temperature operation;
- instrument-level false-positive and qualification performance.

Boundary consequence:

`public experimental poster != complete apparatus files/raw dataset/mission-qualified implementation release`.

## Science x boundary carrier matrix

Owner: `DASHI/Culture/MissingDeceasedScienceBoundaryCrossPollinationExact.agda`

| Case | public technical carrier | potentially non-public carrier |
|---|---|---|
| POAMS | model + derivation + preliminary experiment report | V5 data/hardware, complete know-how, Institute derivatives |
| Reza/Jacinto | composition + qualitative mechanisms + fabrication description + examples | raw test data, heat treatment, microstructure/process control, tacit know-how |
| LeBlanc | I&C maturation architecture + database concept + working-group outputs | live DB contents/access, detailed qualification/design artifacts |
| Viriato | reduced equations + algorithms + numerical architecture + benchmarks | source artifact/prior bounded code state unresolved |
| Scorpius | accelerator/radiography architecture | experiment-specific data, inverse model, weapons-design interpretation |
| Maiwald | experimental chain + benchmark isomer discrimination | full apparatus design, raw data, mission-qualified implementation |

## Current scientific frontier

The strongest discriminator is no longer merely `private -> public`. It is closer to:

`which reconstructive technical carriers crossed which boundary, by what mechanism, relative to matched peers?`

Candidate high-value carriers:

1. source code / executable implementation;
2. raw calibration and experimental data;
3. process windows / heat treatment / manufacturing recipes;
4. detailed qualification and failure-mode data;
5. experiment-specific inverse models;
6. design files and reproducibility instructions.

Ordinary papers and patent publication are weakly discriminating unless they expose unusually reconstructive layers relative to comparable peers.

McCasland remains intentionally outside a single-mechanism science fixture at this stage: the current evidence establishes broad technology/acquisition and disclosure-network roles rather than one event-time scientific object that can be responsibly assigned a mechanism owner. A technical fixture should be added only after an exact programme/artifact is selected.

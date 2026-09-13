# Twenty-Scientist Science Capability BIDI Design

## Purpose

Build one repo-native BIDI surface over the retained 20-scientist science atlas. The object must embody each scientist's source-backed scientific/engineering kernel, expose intended applications, admit separately typed possible-application candidates, and compile reverse obligations back to the exact science/custody leaves required to make an application operational.

The design must not create a new planner or a new scientific ontology. It reuses `ScientificCapabilityCarrierBidiExact`, `ApplicationTransformationCapabilityBidiExact`, `CapabilitySynthesisHypergraphExact`, `QueryFactorisationSufficiency`, the existing domain science owners, and the Round-6 science/succession ledger.

## Chosen architecture

Use a thin roster-specific adapter rather than expanding the core capability ontology.

1. `ScientistTechnologyFibre` binds one retained scientist to an existing science kernel, one or more existing `ScientificCapabilityCarrier`-style coordinates, an intended application, a possible-application candidate, and reverse science/custody obligations.
2. `ApplicationClaimStrength` distinguishes `sourceBackedIntended`, `documentedEngineeringInterface`, `crossDomainCandidate`, and `speculativeOnly`. Possible application never implies historical deployment, programme membership, possession, or event cause.
3. `TwentyScientistCapabilityState` is a list of all 20 fibres. Its projections answer bounded queries such as "what science is represented?", "what application class can this fibre support?", and "what remains unpaid?".
4. `IntegratedScienceCapabilityBidi` groups the fibres into benign/system-level capability compositions using existing `CapabilitySynthesis` classes. The first composite is a `multiDomainScienceAndEngineeringPlatform`-style surface: modelling/compute, power/control, sensing/diagnostics, materials, autonomous guidance, planetary/astronomical sensing, life-science sensing, and environmental prediction. It is a capability-design object, not a historical-programme claim.
5. Reverse BIDI routes any requested composite application back to missing `TransformationCoordinate`/carrier/custody leaves rather than manufacturing them from domain adjacency.

## Per-scientist science coverage

The adapter must include all 20 Round-6 scientists and point at the existing science objects:

- Loureiro: KREHM/KRMHD/Viriato Fourier-Hermite plasma modelling.
- LeBlanc: space-fission instrumentation/control, qualification and calibration.
- Maiwald: cryogenic messenger-tag action spectroscopy and QIT mass spectrometry.
- Reza: oxygen-service Ni alloy, gamma/gamma-prime/process windows and turbopump applications.
- Grillmair: stellar-stream matched filtering/orbit inference; separate astronomical spectroscopy fibre.
- Hicks: small-body photometry/spectrophotometry and physical-property inference.
- McCasland: fault-tolerant Gramian sensor/actuator placement.
- Anthony Chavez: DARHT/Scorpius engineering only through the LANL identity carrier; missing-person inheritance remains identity-gated.
- Jason Thomas: STING and VPS34/NCOA4 ferritinophagy chemical biology.
- Amy Eskridge: mechanism/programme discrimination only until an Amy-authored technical object is paid.
- Ning Li: superconducting gravitoelectric/gravitomagnetic theory and constrained YBCO apparatus tests.
- Chen Shuming: hardware verification and processor-development engineering.
- Feng Yanghe: Bayesian/noisy-label classification and separately War Skull decision-agent engineering.
- Zhou Guangyuan: high-temperature polyimide-aerogel structure/process/property science.
- Liu Donghao: DSMM/data-security maturity governance, not generic cryptography.
- Zhang Xiaoxin: geomagnetic-storm prediction plus separately Fengyun space-weather monitoring.
- Zhang Daibing: UAV landing/localisation/path-following/formation control.
- Li Minyong: photopharmacology and fluorescent molecular probes.
- Fang Daining: multifield mechanics and elastic-metamaterial inverse design.
- Yan Hong: hypersonic inlet shock/boundary-layer thermal control; plasma-flow control remains a separate fibre until source-welded.

## Application semantics

Each fibre has two application surfaces.

`intendedApplication` records what the primary work itself was designed to do, e.g. plasma simulation, FSP I&C qualification, molecular identification, oxygen-rich turbomachinery survivability, stellar-stream detection, UAV guidance, or space-weather forecasting.

`possibleApplication` may name a technically compatible extension only when its strength is typed. A cross-domain candidate is a design/search coordinate, not a historical fact. There is no constructor from a possible application to programme membership, deployment, motive, targeting, disappearance cause, or homicide.

## Integrated BIDI object

The initial integrated object is an abstract research/engineering platform, not a weapon blueprint. It may consume fibres from all 20 through typed subsystem roles:

- modelling and inference: Loureiro, Grillmair, Hicks, Zhang Xiaoxin, Feng, Fang;
- robust control/autonomy: McCasland, Zhang Daibing, Chen, LeBlanc;
- sensing/diagnostics: Maiwald, Chavez, Li Minyong, Jason Thomas;
- materials/extreme environments: Reza, Zhou, Fang;
- power/field-physics discriminators: LeBlanc, Ning, Amy as explicitly differently paid fibres;
- governance/security/integration: Liu Donghao;
- hypersonic/flow actuation: Yan Hong.

The integrated surface records only that these scientific capabilities can inhabit a common systems-engineering design space. It does not assert collaboration, shared programme, classified deployment, or event causation.

## Factorisation/firewalls

Reuse factorisation language rather than inventing a parallel sufficiency notion. The implementation must encode named false boundaries for:

- `possibleApplicationImpliesHistoricalDeployment = false`
- `technicalCompatibilityImpliesSameProgramme = false`
- `integratedCapabilityImpliesRosterCollaboration = false`
- `scienceCarrierImpliesPersonPossession = false`
- `institutionContinuityImpliesExactCapabilityTransfer = false`
- `applicationCandidateImpliesEventCause = false`
- `allTwentyFibresPresentImpliesOneHistoricalSystem = false`

The BIDI reverse direction is constructive: a requested operational application yields acquisition/proof obligations for geometry, calibration, process window, validation, data, source code/algorithm, qualification and custody as appropriate.

## Testing

TDD static contract first. A focused checker must fail while the new owner is absent, then require:

- exactly 20 retained fibre names;
- intended/possible application distinction;
- all named firewalls;
- at least one science carrier and one reverse obligation per fibre;
- integrated object includes all 20 fibres by name;
- aggregate imports the owner.

No Agda/kernel success claim is allowed without a fresh executable build or exact-head workflow receipt. Source presence/static greps are only source-written validation.

## Files

Create:
- `DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda`
- `scripts/check_missing_deceased_twenty_scientist_science_capability_bidi.sh`
- `docs/superpowers/plans/2026-09-12-twenty-scientist-science-capability-bidi.md`

Modify:
- `DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda`

Potential later split, not required for the first tranche: per-domain executable proof owners for science kernels that currently have only source/algorithm depth rather than executable finite witnesses.

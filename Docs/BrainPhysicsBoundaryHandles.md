# Brain Physics Boundary Handles

Non-promoting boundary inventory for the current Brain -> BrainDNA -> chemistry/physics-facing handoff lane.

This document is an inventory, not a promotion receipt. It records the exact local names that currently expose Brain connector coordinates or handles, and it states the physics laws that are still absent from this boundary.

## Scope

- Worker role: bounded read-and-document inventory.
- Owned artifact: `Docs/BrainPhysicsBoundaryHandles.md`.
- Searched surfaces: `Ontology/Brain`, `Ontology/BrainDNA`, `DASHI`, and existing Brain docs for `BrainConnector`, `hamiltonian`, `crossBand`, `thermoChecksum`, and `BrainPhysicsHandoffPromotion`.
- Worktree note: the repo already had unrelated dirty changes before this document was added. This inventory does not revert or overwrite them.

## Local Brain Connector Handles

### Region, motif, and lens coordinates

`Ontology/Brain/BrainRegionAutomatonSurface.agda` defines the local region vocabulary:

- `BrainRegion`: `S3`, `S4`, `mu`
- `RegionLens`: `s3Lens`, `s4Lens`, `muLens`
- `RegionMotif`: `M1` through `M9`
- `motifIndex : RegionMotif -> Nat`
- `lensOf : BrainRegion -> RegionLens`
- `motifOf : BrainRegion -> RegionMotif`
- `RegionCorrespondence` with fields `region`, `lens`, and `motif`
- exact witnesses `correspondence-lens-exact`, `correspondence-motif-exact`, and `observeRegionState-motif`

This is a typed coordinate handle for region/lens/motif packaging. It is not a neural dynamics law.

### Brain theme and coherence profiles

Local Brain theme/profile surfaces exist as theorem-thin packaging:

- `Ontology/Brain/BrainLearningEigenbasisSurface.agda`: `BrainLearningEigenbasisProfile`, `profileOfState`, `profile-threshold-exact`, `profile-phase-exact`, `profile-width-exact`, and `profile-stateOf-width-layer-coherent`.
- `Ontology/Brain/BrainMorphospaceGapJunctionSurface.agda`: a morphospace/gap-junction surface with a `coherence : MorphospacePoint -> MorphospacePoint -> Nat` field.
- `Ontology/Brain/BrainThemeConsumerLaws.agda`: `BrainThemeConsumer` includes `coherenceWithSelf`, with `consumer-self-coherence-exact`.
- `Ontology/BrainDNA/BrainThemeIntegratedSemantics.agda`: `BrainThemeIntegratedSemanticProfile` carries `lens`, `motif`, `visualClass`, `learningPhase`, `morphSemantic`, `order`, `width`, `emittedAdmissibility`, `recoveryBoundary`, `thermoChecksum`, `hamiltonianChecksum`, and `crossBand`.

These profiles expose exact alignment and checksum handles. They do not assert neuroscience completeness, learning dynamics, or physical law recovery.

### Cross-band and Hamiltonian-like handles

The current BrainDNA connector chain exposes `crossBand` and `hamiltonian` as `Nat` fields carried through exact profile witnesses:

- `Ontology/BrainDNA/BrainExtractionConnectorDepth.agda`: `BrainExtractionConnectorDepth` has `crossBand : Nat` and `hamiltonian : Nat`.
- `Ontology/BrainDNA/BrainSummaryStructuralDepth.agda`: `BrainSummaryStructuralDepth` has `crossBand : Nat` and `hamiltonian : Nat`.
- `Ontology/BrainDNA/BrainCrossoverAbstractComposition.agda`: `BrainCrossoverAbstractProfile` has `crossBand : Nat` and `hamiltonian : Nat`.
- `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda`: `BrainAtomicChemistryHandoffProfile` has `sheet : SheetCoordinates n`, `crossBand : Nat`, `hamiltonian : Nat`, and `recoveryBoundary : Nat`.
- `Ontology/BrainDNA/BrainConnectorSemanticDepth.agda`: `BrainConnectorSemanticDepthProfile` has `crossBand : Nat` and `hamiltonian : Nat`.
- `Ontology/BrainDNA/BrainConnectorEndToEndSemanticDepth.agda`: `BrainConnectorEndToEndSemanticProfile` has `crossBand : Nat` and `hamiltonian : Nat`.
- `Ontology/BrainDNA/BrainConnectorEndToEndSemanticLaws.agda`, `BrainConnectorConsumerSemantics.agda`, `BrainConnectorConsumerLaws.agda`, `BrainConnectorIntegratedConsumerSemantics.agda`, and `BrainConnectorIntegratedConsumerLaws.agda` carry `thermoChecksum`, `hamiltonian`, and `crossBand` through downstream consumer/law profiles.

Important boundary: the local field name `hamiltonian` is a checksum/summary-style natural-number handle in this lane. It is not a Hamiltonian dynamics theorem.

### Thermo and Hamiltonian checksums

`Ontology/BrainDNA/BrainChemistryCodecConsumer.agda` defines `BrainChemistryCodecConsumerProfile` with:

- `thermoChecksum : Nat`
- `hamiltonianChecksum : Nat`
- canonical witnesses `consumerThermoChecksumCanonical` and `consumerHamiltonianChecksumCanonical`

`Ontology/BrainDNA/BrainWholeChainIntegrationLaw.agda` defines:

- `SemanticChecksumPair` with fields `thermo : Nat` and `hamiltonian : Nat`
- `chainCarrierChecksum`
- `composeHopChecksums`
- `wholeChainSemanticChecksumComposes`
- `wholeChainChecksumMatchesStreamingCarrier`

This is a checksum-composition handle across the current chain, not a thermodynamic law or Hamiltonian evolution law.

### Physics-facing handoff handle

`Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda` is the local interface-like handoff. It imports `DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem` and packages:

- `BrainAtomicChemistryHandoffProfile`
- `physicsRecovery : AtomicChemistryRecoveryTheorem`
- `chemistryCarrierSupport : Set`
- exact witnesses including `handoffChemistryStructured`, `handoffCrossBandMatchesIntegration`, `handoffHamiltonianMatchesIntegration`, and `handoffRecoveryBoundaryExact`

The module comment states that it remains theorem-thin and does not claim atomic recovery, chemistry recovery, or a physical derivation.

`Ontology/BrainDNA/BrainPhysicsHandoffPromotion.agda` exists, but its local boundary is explicitly gated:

- `H_phys` maps the existing `C_atom` carrier to `O_chem`.
- `BrainPhysicsHandoffPromotion` composes `Whole.I_chain` through `H_phys`.
- It carries `Candidate256.canonicalCandidate256QuotientCrossBandLaw`, `LchemWitness`, and `AtomicChemistryRecoveryGateWitness`.
- Its `nonClaimBoundary` strings state that it does not reinterpret the BrainDNA carrier and that atomic recovery gates are exposed only as gates already present on `AtomicChemistryRecoveryTheorem`.

Despite the filename, this inventory does not treat that file as a Brain-to-physics law receipt. It is a gated composition surface over already-landed chemistry/closure gates.

## Missing Physics Laws

No local Brain boundary theorem receipt was found that proves any of the following from the Brain connector handles:

- Hamiltonian dynamics.
- Maxwell equations.
- Schrodinger equation or continuum Schrodinger dynamics.
- General-relativistic curvature or sourced Einstein equations.
- Full Standard Model recovery.
- Full SM+GR unification or physics unification.

The repo contains physics modules and downstream closure surfaces elsewhere, including Schrodinger/Einstein/SM/GRQFT-named files, but the Brain boundary files inspected here only carry theorem-thin exactness, checksum, cross-band, recovery-boundary, and handoff gates. Existing claim-boundary docs also mark limited SM+GR/GRQFT promotion as downstream and not complete.

## Required For Future Lateral-Support Review

A future lateral-support review would need receipts beyond this inventory:

1. A theorem that maps the Brain connector coordinates into a declared physics state space with explicit units, parameters, and invariants.
2. A real dynamics law over the `hamiltonian` handle, not just a `Nat` checksum or profile field.
3. A bridge showing how `crossBand` participates in a physical interaction or observable law, with exact hypotheses and nontrivial consequences.
4. A thermodynamic interpretation of `thermoChecksum` with state variables, conservation/dissipation conditions, and calibration status.
5. External calibration or authority receipts if empirical adequacy is claimed.
6. For Maxwell, Schrodinger, GR curvature, Standard Model, or unification language: a theorem receipt that consumes this Brain boundary and proves the named law under stated assumptions.
7. An explicit non-claim ledger for anything still only carried as a gate, candidate, checksum, or diagnostic.

Until those receipts exist, the correct reading is: non-promoting Brain-to-physics boundary handles are present; Brain-derived physics laws are missing.

## Grep Evidence

Representative local evidence from the bounded scan:

- `Ontology/Brain/BrainRegionAutomatonSurface.agda:23-40`: `motifIndex`, `lensOf`, and `motifOf` define the local motif/lens mapping.
- `Ontology/Brain/BrainRegionAutomatonSurface.agda:91-122`: exact lens/motif observation witnesses.
- `Ontology/BrainDNA/BrainThemeIntegratedSemantics.agda:30-40`: `BrainThemeIntegratedSemanticProfile` carries motif, thermo checksum, Hamiltonian checksum, and cross-band fields.
- `Ontology/BrainDNA/BrainChemistryCodecConsumer.agda:47-48`: `thermoChecksum` and `hamiltonianChecksum`.
- `Ontology/BrainDNA/BrainChemistryCodecConsumer.agda:120-135`: canonical thermo/Hamiltonian checksum witnesses.
- `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda:56-58`: `crossBand` and `hamiltonian` in `BrainAtomicChemistryHandoffProfile`.
- `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda:101-128`: handoff witnesses tying cross-band and Hamiltonian fields to local chemistry/integration profiles.
- `Ontology/BrainDNA/BrainConnectorSemanticDepth.agda:33-34`: connector semantic-depth profile carries `crossBand` and `hamiltonian`.
- `Ontology/BrainDNA/BrainConnectorEndToEndSemanticDepth.agda:34-35`: end-to-end connector profile carries `crossBand` and `hamiltonian`.
- `Ontology/BrainDNA/BrainConnectorEndToEndSemanticDepth.agda:140-171`: exact cross-band/Hamiltonian matches to handoff and connector-depth profiles.
- `Ontology/BrainDNA/BrainWholeChainIntegrationLaw.agda:48-72`: `SemanticChecksumPair`, checksum composition, and chain-carrier checksum.
- `Ontology/BrainDNA/BrainPhysicsHandoffPromotion.agda:23-27`: explicit non-derivation boundary for the promotion module.
- `Ontology/BrainDNA/BrainPhysicsHandoffPromotion.agda:113-123`: `H_phys` non-claim boundary.
- `Ontology/BrainDNA/BrainPhysicsHandoffPromotion.agda:210-234`: `physicsHandoffPromotionOf` composes `Whole.I_chain`, `H_phys`, and Candidate256 law gates with non-claim strings.
- `Docs/BrainLaneStatus.md:238-250`: Brain lane is not local closure, not current theorem evidence for physics unification, and not a finished brain formalism.
- `Docs/BrainDNACrossoverStatus.md:147-168`: status doc lists exact region/motif, thermo/Hamiltonian, cross-band, and recovery-boundary witnesses on theme/connector surfaces.
- `Docs/BrainDNACrossoverStatus.md:706-713`: richer whole-chain downstream semantics remain a target, with no closure or biological completeness claim.
- `Docs/LimitedSMGRUnificationClaimBoundary.md:252-270`: full Standard Model coverage, quantum gravity, full unification, and discrete Einstein-law receipts remain blocked/missing for limited SM+GR claim promotion.

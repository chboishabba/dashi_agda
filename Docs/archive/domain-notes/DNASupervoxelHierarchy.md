# DNA Supervoxel Hierarchy

## Scope

This note starts the DNA-first supervoxel lane that previously existed only in
the archive thread `DNA Cassette Tape Comeback`.

The local repo previously had:

- no DNA 4/16/64/256 carrier,
- no chemistry-native supervoxel note,
- no theorem surface for chemistry quotienting.

This pass starts that lane.

## Lane Status

In the updated `PhysicsRealityRoadmap` / `PhysicsUnificationMap` language, this
is an adjacent archive-derived program that is now genuinely localized in Agda.
It is a real formal lane in this repo, but it is not currently part of the
central physics-unification theorem spine.

What is localized here now:

- DNA-first `4 -> 16 -> 64 -> 256` carrier ownership
- chemistry quotient and `U/V` coordinate ownership
- concrete chemistry screening and UV-aware refinement
- complement, sheet/Hamiltonian, supervoxel, streaming, eigenclass, and
  channel owner surfaces

What is genuinely formal here:

- typed Agda owner modules for the carrier, quotient, and chemistry-visible
  interfaces
- bounded theorem surfaces for local complement, involution, stabilization, and
  admissibility-style facts
- a local formal packaging of DNA-side storage/channel pressure

What this does not currently justify:

- a physics-unification claim
- a localized brain theorem lane
- a localized brain-DNA theorem lane
- a realistic external DNA storage codec or synthesis/sequencing channel model

Concrete open gaps:

- stronger theorem depth on the theorem-thin DNA surfaces
- a real external codec beyond the current channel boundary/interface layer
- a more realistic physical channel model for synthesis, sequencing, and error
  recovery
- wider crossover localization for brain-side and brain-DNA/channel ideas that
  still mostly live in archive or sibling-repo form

## Archived guidance now made local

The archive material pointed to four recurring ideas:

- DNA should be treated as a native 4-adic carrier, not only as a remapped
  ternary stream;
- the natural fixed-height hierarchy is `4 -> 16 -> 64 -> 256`;
- chemistry sees only a quotient of the raw sequence;
- thermo / reverse-complement risk should be modeled as a screen or kernel on
  that quotient-aware carrier.

## Landed modules

- [`Ontology/DNA/Supervoxel4Adic.agda`](../Ontology/DNA/Supervoxel4Adic.agda)
- [`Ontology/DNA/ChemistryQuotient.agda`](../Ontology/DNA/ChemistryQuotient.agda)
- [`Ontology/DNA/ChemistryConcrete.agda`](../Ontology/DNA/ChemistryConcrete.agda)
- [`Ontology/DNA/ChemistryUVCoordinates.agda`](../Ontology/DNA/ChemistryUVCoordinates.agda)
- [`Ontology/DNA/ChemistryUVConcrete.agda`](../Ontology/DNA/ChemistryUVConcrete.agda)
- [`Ontology/DNA/ComplementLaws.agda`](../Ontology/DNA/ComplementLaws.agda)
- [`Ontology/DNA/ChemistrySheetHamiltonian.agda`](../Ontology/DNA/ChemistrySheetHamiltonian.agda)
- [`Ontology/DNA/SupervoxelAdmissibility.agda`](../Ontology/DNA/SupervoxelAdmissibility.agda)
- [`Ontology/DNA/StreamingEncoderSurface.agda`](../Ontology/DNA/StreamingEncoderSurface.agda)
- [`Ontology/DNA/EigenclassSurface.agda`](../Ontology/DNA/EigenclassSurface.agda)
- [`Ontology/DNA/ChannelCodingSurface.agda`](../Ontology/DNA/ChannelCodingSurface.agda)
- [`Docs/DNAUVCoordinateBridge.md`](./DNAUVCoordinateBridge.md)

## What is now implemented

### 1. DNA-first 4-adic carrier

`Supervoxel4Adic.agda` defines:

- DNA alphabet `A C G T`
- Watson-Crick complement
- fixed-height block carriers:
  - `DNA4`
  - `DNA16`
  - `DNA64`
  - `DNA256`
- a first `BlockLift4Adic` record

This is intentionally the smallest honest carrier.

### 2. Chemistry quotient surface

`ChemistryQuotient.agda` defines:

- `U`-style strong/weak feature stream
- `V`-style purine/pyrimidine feature stream
- a `ChemistryFeature` record
- a `ChemistryQuotient` record with:
  - `featureMap`
  - `thermoKernel`
  - `admissible`
- a quotient interface on `DNA256`

So the repo now has a formal place to say:

> chemistry does not see the raw sequence directly; it sees a feature quotient
> plus a thermo-like scalar screen.

## Current boundary

This is still early and intentionally narrow.

What is implemented:

- the carrier hierarchy
- the chemistry-visible quotient surface
- the first quotient interface on `DNA256`
- a local `U/V` coordinate bridge with:
  - `encodeUV`
  - `decodeUV`
  - proofs that the `U/V` pair still determines the underlying base exactly
- a first concrete chemistry quotient instance with:
  - `U/V` feature map
  - strong-base thermo scalar
  - local immediate-repeat ban
  - local immediate-complement ban
  - bounded span-2 complement exclusion
  - sliding 4-window GC-extremal ban
  - sliding 4-window reverse-complement palindrome ban
  - sliding 6-window hairpin-like reverse-complement ban
- a UV-oriented concrete refinement with:
  - adjacent pyrimidine dimer counting in the thermo kernel
  - sliding 3-window pyrimidine-run exclusion in admissibility
- complement-visible chemistry laws showing that Watson-Crick complement:
  - preserves the strong/weak channel
  - flips the purine/pyrimidine channel
- a sheet-space chemistry Hamiltonian surface with:
  - signed `U/V` sheet coordinates
  - per-band transition energy
  - cross-band coupling energy
  - a packaged chemistry Hamiltonian over those sheets
- a supervoxel admissibility/checksum surface with:
  - paired voxel packaging
  - reverse-complement supervoxel involution
  - a typed checksum owner surface
  - a theorem-thin admissibility contract
- a streaming encoder surface with:
  - typed encoder state
  - generic admissible-next-base screening
  - update and checksum surfaces
- an eigenclass/macro-adjacency surface with:
  - one concrete `DNA3` eigenclass classifier
  - a scan-order type
  - a first six-line macro-adjacency score
- a channel-integration surface with:
  - inner-code boundary
  - outer recovery-code boundary
  - physical-channel risk surface
  - integrated emission/recovery interface

What is not implemented:

- stronger proofs on the new theorem-thin surfaces, especially:
  - supervoxel involution closure under the full reverse-complement pairing law
  - stronger checksum/eigen-check invariants
  - richer encoder correctness statements beyond the current typed update spec
- a longer-window reverse-complement or hairpin law beyond the current 6-window
  screen
- richer GC-window theorems beyond the current 4-window extreme ban
- dimer theorems beyond the current local UV-aware refinement
- a full external DNA storage codec with real synthesis/sequencing channel logic
- any connection to the physics closure bundle

## Next step

The next honest move is no longer missing owner surfaces.
It is to strengthen or prove the new ones, for example by adding:

- a stronger supervoxel admissibility theorem under reverse-complement pairing,
- a longer-window reverse-complement exclusion law,
- a stronger GC-window constraint,
- a richer hairpin/dimer kernel,
- or a more realistic channel/error-correction instance beneath the new
  integration interface.

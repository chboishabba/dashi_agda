# Brain-DNA / Codec / Channel Crossover Status

## Scope

This note is the compact local status surface for the brain-DNA / codec /
channel crossover lane shown on:

- `Docs/PhysicsUnificationMap.puml`
- `Docs/PhysicsRealityRoadmap.puml`

The governing boundary is the same one used there and in
`Docs/PhysicsGuide.md`:

- this lane has partial local owner, compatibility, law, and consumer surfaces,
- it has stronger archive-backed design pressure than older docs implied,
- it is not current theorem evidence for physics closure,
- and it is not yet a localized brain theorem lane in this repo.

## Current local owner surfaces

The crossover lane is only partially local, but it now has its own local
surfaces plus several DNA-side owners that form the relevant bridge boundary.

Local crossover surfaces:

- `Ontology/BrainDNA/PacketCodecBridge.agda`
  - line-major packet boundary
  - typed token/packet/state/emit surface
  - bounded encode/emit/admissibility attachment points
- `Ontology/BrainDNA/BrainVocabularyPacketCompatibility.agda`
  - typed adapter from local brain vocabulary into the crossover packet surface
  - exact width/order/emission compatibility witnesses
- `Ontology/BrainDNA/BrainSummaryPacketCompatibility.agda`
  - typed summary-level view over the packet boundary
  - exact width/layer/activity/order/emission-width compatibility witnesses
- `Ontology/BrainDNA/BrainStateCrossoverLaws.agda`
  - exact brain-origin admissibility, emit-output admissibility, and
    emitted-length laws at the local crossover boundary
- `Ontology/BrainDNA/BrainSummaryEigenclassCompatibility.agda`
  - representative-only bridge into the local DNA eigenclass and
    macro-adjacency summary boundary
  - exact order, line-admissibility, coupled-adjacency, and score witnesses
- `Ontology/BrainDNA/BrainSummaryChemistryCompatibility.agda`
  - summary-side bridge into the local DNA chemistry-sheet boundary
  - exact width/order/sheet-coordinate/cross-band/Hamiltonian witnesses
- `Ontology/BrainDNA/BrainSummaryStructuralCompatibility.agda`
  - bounded local composition of the summary-side eigenclass and chemistry
    bridges
  - exact structural order, adjacency-score, sheet, cross-band, and
    Hamiltonian witnesses on the current carrier
- `Ontology/BrainDNA/BrainSummaryStructuralConsumer.agda`
  - bounded downstream consumer over the composed structural-summary package
    and current state-origin crossover laws
  - exact order, emitted-length, admissibility, adjacency, and
    chemistry/Hamiltonian consumer witnesses on the current carrier
- `Ontology/BrainDNA/BrainCodecAdmissibilityBridge.agda`
  - theorem-thin codec bridge over the current state-origin crossover laws
    and DNA attachment/recovery boundary
  - exact emitted admissibility, emitted-length, packetized-emission, and
    recovered-emission shape witnesses
- `Ontology/BrainDNA/BrainCodecDepthLaws.agda`
  - bounded codec depth surface over the current state-origin crossover laws
    and DNA attachment/recovery boundary
  - exact emission identity, packetize/recover normalization, recovery
    stability, and recovery-boundary witnesses
- `Ontology/BrainDNA/BrainCodecSemanticDepth.agda`
  - bounded codec semantic-depth surface over the current codec bridge and
    depth owners
  - exact emitted-width/admissibility, packetized/recovered canonical-shape,
    and recovery-boundary witnesses
- `Ontology/BrainDNA/BrainExtractionChemistryConnector.agda`
  - explicit theorem-thin connector from the local brain extraction owner into
    the current DNA/chemistry boundary
  - exact extraction-to-summary and extraction-to-chemistry compatibility
    witnesses
- `Ontology/BrainDNA/BrainSummaryStructuralDepth.agda`
  - bounded downstream structural-summary depth surface over the current
    structural-summary consumer and state-origin crossover laws
  - exact order, width, admissibility, adjacency, cross-band, and Hamiltonian
    witnesses
- `Ontology/BrainDNA/BrainExtractionConnectorDepth.agda`
  - bounded extraction-aware connector depth surface over the extraction
    connector and structural-summary depth surfaces
  - exact extraction-width/emitted-width stability, admissibility coherence,
    and chemistry/Hamiltonian alignment witnesses
- `Ontology/BrainDNA/BrainExtractionConnectorSemantics.agda`
  - bounded extraction-aware connector semantics surface over the local
    extraction owner, invariant owner, connector, and connector-depth owners
  - exact invariant, width/layer/activity, admissibility, and
    chemistry/Hamiltonian semantic witnesses
- `Ontology/BrainDNA/BrainCodecSemanticLaws.agda`
  - bounded codec semantic-law surface over the local codec semantic-depth and
    codec-depth owners
  - exact semantic width, admissibility, recovery-collapse, and
    recovery-boundary witnesses
- `Ontology/BrainDNA/BrainCrossoverAbstractComposition.agda`
  - bounded composed abstraction surface over the local codec semantic-depth,
    structural-summary depth, extraction-aware connector depth, and DNA
    abstract crossover/channel law owners
  - exact order, width, admissibility, adjacency, chemistry, Hamiltonian,
    recovery-boundary, and abstract-channel reapplication witnesses
- `Ontology/BrainDNA/BrainCodecPayloadRecoveryBridge.agda`
  - bounded payload-recovery/channel contract surface over the local codec
    bridge, semantic-depth, semantic-law, and recovery boundary owners
  - exact source/emitted/recovered payload and recovery-boundary witnesses
- `Ontology/BrainDNA/BrainStructuralConsumerSemantics.agda`
  - bounded structural-consumer semantics surface over the local
    invariant-depth, extraction semantics, structural consumer, and abstract
    composition owners
  - exact bounded invariant-depth, order, width, admissibility, chemistry,
    Hamiltonian, and recovery-boundary witnesses
- `Ontology/BrainDNA/BrainThemeConnectorSurface.agda`
  - bounded connector surface consuming the four local brain theme owners into
    the current BrainDNA extraction/packet side
  - exact theorem-thin transport witnesses for region, visual, learning,
    morphospace, extraction, and packet order/width alignment
- `Ontology/BrainDNA/BrainChemistryCodecConsumer.agda`
  - bounded codec/chemistry consumer over payload recovery, structural
    consumer semantics, semantic checksum, and long-window chemistry owners
  - exact recovery-boundary, recovered-width, admissibility, thermo-checksum,
    and Hamiltonian-checksum consumer witnesses
- `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda`
  - bounded local handoff from the explicit brain-DNA connector chain into the
    physics-facing chemistry carrier
  - exact order, width, chemistry, Hamiltonian, and recovery-boundary handoff
    witnesses
- `Ontology/BrainDNA/BrainConnectorSemanticDepth.agda`
  - bounded semantic-depth surface over the explicit consumed connector chain
    and physics-facing handoff owners
  - exact theme-width, recovered-width, admissibility, chemistry, Hamiltonian,
    and handoff-depth witnesses
- `Ontology/BrainDNA/BrainDnaRepresentationMap.agda`
  - bounded brain-to-DNA representation owner and representation-semantics
    surface over the landed theme connector, packet compatibility, state
    crossover, and DNA attachment owners
  - exact profile-order, width, encoded/emitted admissibility, and
    state-crossover compatibility witnesses
- `Ontology/BrainDNA/BrainRepresentationTransportLaws.agda`
  - bounded end-to-end representation transport law surface over the current
    representation, connector-depth, chemistry-consumer, and handoff owners
  - exact order, width, admissibility, and recovery-boundary transport
    witnesses across the current connector chain
- `Ontology/BrainDNA/BrainThemeChemistryChannelTransport.agda`
  - bounded theme-to-chemistry/channel/handoff transport surface over the
    four localized brain theme owners, theme connector, chemistry consumer,
    and atomic chemistry handoff owners
  - exact region/motif, width, recovery-boundary, cross-band, and Hamiltonian
    transport witnesses on the current carrier
- `Ontology/BrainDNA/BrainRepresentationSemanticDepth.agda`
  - bounded representation semantic-depth surface over the current
    representation owner, representation transport-law, connector
    semantic-depth, and atomic chemistry handoff owners
  - exact order, width, admissibility, visual-class, cross-band,
    Hamiltonian, and recovery-boundary semantic-depth witnesses
- `Ontology/BrainDNA/BrainThemeSemanticTransportLaws.agda`
  - bounded semantic/law deepening over the current
    theme-to-chemistry/channel/handoff transport surface
  - exact lens/motif, width, recovery-boundary, thermo-checksum,
    Hamiltonian, and cross-band transport witnesses
- `Ontology/BrainDNA/BrainThemeEndToEndSemanticDepth.agda`
  - bounded end-to-end semantic-depth surface keyed by the localized brain
    themes over the current theme transport and connector chain
  - exact lens/motif, width, recovery-boundary, thermo-checksum,
    Hamiltonian, and cross-band end-to-end semantic-depth witnesses
- `Ontology/BrainDNA/BrainRepresentationSemanticLaws.agda`
  - bounded semantic/law deepening over the current representation owner,
    transport-law, semantic-depth, and end-to-end connector semantic-depth
    surfaces
  - exact order, width, admissibility, recovery-boundary, and visual-class
    semantic-law witnesses
- `Ontology/BrainDNA/BrainRepresentationConsumerSemantics.agda`
  - bounded downstream representation-consumer semantics surface over the
    current representation semantic/law, chemistry-consumer, and handoff
    owners
  - exact order, width, encoded/emitted admissibility, recovery-boundary,
    and visual-class consumer witnesses
- `Ontology/BrainDNA/BrainRepresentationConsumerLaws.agda`
  - bounded downstream representation-consumer law surface over the current
    representation consumer-semantics chain
  - exact order, width, encoded/emitted admissibility, recovery-boundary,
    and visual-class consumer-law witnesses
- `Ontology/BrainDNA/BrainRepresentationIntegratedSemantics.agda`
  - bounded integrated representation semantics surface over the current
    representation consumer chain
  - exact order, width, encoded/emitted admissibility, recovery-boundary,
    and visual-class integration witnesses
- `Ontology/BrainDNA/BrainConnectorEndToEndSemanticLaws.agda`
  - bounded end-to-end semantic/law surface over the consumed connector chain
  - exact/coherence witnesses over representation, theme, chemistry/channel,
    and handoff alignment on the current carrier
- `Ontology/BrainDNA/BrainThemeConsumerSemantics.agda`
  - bounded downstream theme-consumer semantics surface over the localized
    theme lane and the current chemistry/channel/handoff boundaries
  - exact lens/motif, visual/learning/morph semantic, width,
    recovery-boundary, thermo/Hamiltonian, and cross-band consumer witnesses
- `Ontology/BrainDNA/BrainThemeConsumerLaws.agda`
  - bounded downstream theme-consumer law surface over the localized theme
    lane
  - exact lens/motif, visual/learning/morph semantic, width,
    recovery-boundary, thermo/Hamiltonian, and cross-band consumer-law
    witnesses
- `Ontology/BrainDNA/BrainThemeIntegratedSemantics.agda`
  - bounded integrated theme semantics surface over the localized brain
    themes
  - exact lens/motif, visual/learning/morph semantic, width,
    recovery-boundary, thermo/Hamiltonian, and cross-band integration
    witnesses
- `Ontology/BrainDNA/BrainConnectorConsumerSemantics.agda`
  - bounded downstream connector-consumer semantics surface over the consumed
    connector chain
  - exact order, width, emitted admissibility, recovery-boundary,
    thermo/Hamiltonian, and cross-band consumer witnesses
- `Ontology/BrainDNA/BrainConnectorConsumerLaws.agda`
  - bounded downstream connector-consumer law surface beyond the current
    connector-consumer semantics layer
  - exact order, width, emitted admissibility, recovery-boundary,
    thermo/Hamiltonian, and cross-band consumer-law witnesses
- `Ontology/BrainDNA/BrainConnectorIntegratedConsumerSemantics.agda`
  - bounded integrated whole-chain consumer semantics surface over the
    consumed connector chain
  - exact order, width, emitted admissibility, recovery-boundary,
    recovered-width, thermo/Hamiltonian, and cross-band integration
    witnesses

Local crossover-facing DNA surfaces:

- `Ontology/DNA/StreamingEncoderSurface.agda`
  - typed encoder state
  - admissible-next-base screening
  - update/checksum surface
- `Ontology/DNA/ChannelCodingSurface.agda`
  - inner-code boundary
  - outer recovery-code boundary
  - physical-channel risk surface
  - integrated emission/recovery interface
- `Ontology/DNA/EigenclassSurface.agda`
  - local eigenclass classifier
  - macro-adjacency score surface
  - scan-order boundary
- `Ontology/DNA/SupervoxelAdmissibility.agda`
  - reverse-complement-aware paired packaging
  - checksum/admissibility owner surface
- `Ontology/DNA/ChemistrySheetHamiltonian.agda`
  - signed `U/V` sheet coordinates
  - band/cross-band energy surface
- `Ontology/DNA/CrossoverAttachmentSurface.agda`
  - single crossover attachment package over streaming/channel/eigen/admissibility
- `Ontology/DNA/CrossoverAttachmentLaws.agda`
  - exact emit/admissibility and length coherence above the attachment package
- `Ontology/DNA/CrossoverChannelDepth.agda`
  - exact emitted-state, prefix, admissible-next-base, and checksum coherence
    above the crossover attachment package
- `Ontology/DNA/CrossoverAbstractChannelLaws.agda`
  - bounded abstract crossover/channel law surface over the current
    attachment-law and crossover-depth owners
  - exact emit, admissibility, streaming-state, and checksum canonicality
    witnesses
- `Ontology/DNA/CrossoverSemanticChecksumLaws.agda`
  - bounded semantic checksum law surface over the current abstract
    crossover/channel and channel-depth owners
  - exact thermo/Hamiltonian checksum-pair and next-step admissibility
    canonicality witnesses
- `Ontology/DNA/SupervoxelChemistryLongWindowLaws.agda`
  - bounded longer-window chemistry-facing supervoxel law surface over the
    current streaming checksum and supervoxel admissibility owners
  - exact left/right streaming thermo-Hamiltonian, supervoxel checksum
    convolution, and reverse-complement chemistry witnesses
- `Ontology/DNA/SynthesisSequencingRiskSurface.agda`
  - bounded synthesis/sequencing realism owner surface over the current
    streaming, channel, and crossover chemistry boundaries
  - exact theorem-thin error-mode, read/write-risk, and channel-side realism
    packaging witnesses
- `Ontology/DNA/SynthesisSequencingRealismLaws.agda`
  - bounded synthesis/sequencing realism consumer/law surface over the
    current risk owner, streaming/channel owners, and semantic-checksum laws
  - exact write/read length, payload, state, prefix, risk, and next-step
    admissibility realism witnesses
- `Ontology/DNA/SynthesisSequencingRealismDepth.agda`
  - bounded synthesis/sequencing realism-depth surface over the current
    risk owner and realism-law owners
  - exact emitted width, risk-level, checksum-pair, recovery-boundary, and
    next-step admissibility depth witnesses
- `Ontology/DNA/SynthesisSequencingRealismSemantics.agda`
  - bounded synthesis/sequencing realism semantics surface over the current
    risk owner, realism-law, and realism-depth owners
  - exact emitted payload, risk/recovery, checksum-pair, and next-step
    admissibility semantic witnesses
- `Ontology/DNA/SynthesisSequencingRealismConsumer.agda`
  - bounded downstream synthesis/sequencing realism consumer surface over the
    current realism semantics and channel boundary owners
  - exact emitted payload, recovery-boundary, checksum-pair, and emitted
    admissibility consumer witnesses
- `Ontology/DNA/SynthesisSequencingConsumerLaws.agda`
  - bounded downstream synthesis/sequencing consumer-law surface over the
    localized realism consumer semantics layer
  - exact emitted width/payload, recovery-boundary, checksum-pair, and
    emitted admissibility consumer-law witnesses
- `Ontology/DNA/SynthesisSequencingIntegratedRealism.agda`
  - bounded downstream synthesis/sequencing integrated-realism surface over
    the localized realism semantics and consumer-law layers
  - exact emitted width/payload, recovery-boundary, checksum-pair, and
    emitted admissibility integration witnesses

These are the right local code owners for the crossover lane because they are
the places where the repo already talks about:

- sequence packaging,
- channel/error exposure,
- higher-order local structure,
- chemistry-visible constraints,
- and bounded recovery interfaces.

## What is local vs adjacent

### Local now

What is honestly local in this repo:

- a DNA-first carrier and chemistry stack under `Ontology/DNA/`
- theorem-thin brain vocabulary and coarse-summary surfaces under `Ontology/Brain/`
- theorem-thin crossover packet/compatibility surfaces under `Ontology/BrainDNA/`
- theorem-thin summary-level and state-origin crossover law surfaces under
  `Ontology/BrainDNA/`
- theorem-thin structural-summary bridges, one composed structural-summary
  package, and one downstream structural-summary consumer under
  `Ontology/BrainDNA/`
- one theorem-thin codec bridge surface under `Ontology/BrainDNA/`
- one bounded codec-depth law surface under `Ontology/BrainDNA/`
- one bounded codec semantic-depth surface under `Ontology/BrainDNA/`
- one explicit theorem-thin extraction-aware brain->DNA->chemistry connector
  under `Ontology/BrainDNA/`
- one bounded extraction-aware connector depth surface under
  `Ontology/BrainDNA/`
- one bounded extraction-aware connector semantics surface under
  `Ontology/BrainDNA/`
- one bounded downstream structural-summary depth surface under
  `Ontology/BrainDNA/`
- one bounded codec semantic-law surface under `Ontology/BrainDNA/`
- one bounded composed crossover abstraction surface under `Ontology/BrainDNA/`
- one bounded payload-recovery/channel contract surface under `Ontology/BrainDNA/`
- one bounded structural-consumer semantics surface under `Ontology/BrainDNA/`
- one bounded brain-theme connector surface under `Ontology/BrainDNA/`
- one bounded codec/chemistry consumer surface under `Ontology/BrainDNA/`
- one bounded physics-facing chemistry handoff surface under `Ontology/BrainDNA/`
- one bounded representation semantic-depth surface under `Ontology/BrainDNA/`
- one bounded theme semantic-transport law surface under `Ontology/BrainDNA/`
- one bounded theme end-to-end semantic-depth surface under `Ontology/BrainDNA/`
- one bounded representation semantic-law surface under `Ontology/BrainDNA/`
- one bounded connector end-to-end semantic-law surface under `Ontology/BrainDNA/`
- one bounded abstract crossover/channel law surface under `Ontology/DNA/`
- one bounded semantic checksum law surface under `Ontology/DNA/`
- one bounded longer-window supervoxel chemistry law surface under `Ontology/DNA/`
- one bounded synthesis/sequencing realism-depth surface under `Ontology/DNA/`
- one bounded synthesis/sequencing realism semantics surface under `Ontology/DNA/`
- several of the newer depth/semantic surfaces are now explicitly crosslinked
  rather than standing as theorem islands:
  - `BrainInvariantDepth` feeds `BrainExtractionConnectorSemantics`
  - `BrainExtractionConnectorSemantics`, `BrainCodecSemanticLaws`, and
    `CrossoverSemanticChecksumLaws` feed
    `BrainCrossoverAbstractComposition`
  - `BrainInvariantDepth`, `BrainExtractionConnectorSemantics`,
    `BrainSummaryStructuralConsumer`, and `BrainCrossoverAbstractComposition`
    feed `BrainStructuralConsumerSemantics`
  - `BrainCodecSemanticDepth`, `BrainCodecSemanticLaws`, and
    `BrainCodecAdmissibilityBridge` feed
    `BrainCodecPayloadRecoveryBridge`
  - the four local brain theme owners feed `BrainThemeConnectorSurface`
  - `BrainCodecPayloadRecoveryBridge`,
    `BrainStructuralConsumerSemantics`,
    `CrossoverSemanticChecksumLaws`, and
    `SupervoxelChemistryLongWindowLaws`
    feed `BrainChemistryCodecConsumer`
  - `BrainThemeConnectorSurface`,
    `BrainChemistryCodecConsumer`, and
    the local chemistry-facing integration surfaces
    feed `BrainAtomicChemistryHandoff`
  - `BrainThemeConnectorSurface`,
    `BrainChemistryCodecConsumer`, and
    `BrainAtomicChemistryHandoff`
    feed `BrainConnectorSemanticDepth`
  - `BrainThemeConnectorSurface`,
    `BrainVocabularyPacketCompatibility`,
    `BrainStateCrossoverLaws`, and
    DNA crossover attachment owners
    feed `BrainDnaRepresentationMap`
  - `BrainDnaRepresentationMap`,
    `BrainConnectorSemanticDepth`,
    `BrainChemistryCodecConsumer`, and
    `BrainAtomicChemistryHandoff`
    feed `BrainRepresentationTransportLaws`
  - `BrainDnaRepresentationMap`,
    `BrainRepresentationTransportLaws`,
    `BrainConnectorSemanticDepth`, and
    `BrainAtomicChemistryHandoff`
    feed `BrainRepresentationSemanticDepth`
  - the four localized brain theme owners,
    `BrainThemeConnectorSurface`,
    `BrainChemistryCodecConsumer`, and
    `BrainAtomicChemistryHandoff`
    feed `BrainThemeChemistryChannelTransport`
  - `BrainThemeChemistryChannelTransport`
    feeds `BrainThemeSemanticTransportLaws`
  - `BrainThemeSemanticTransportLaws`
    feeds `BrainThemeEndToEndSemanticDepth`
  - `BrainRepresentationSemanticDepth` and
    `BrainConnectorEndToEndSemanticDepth`
    feed `BrainRepresentationSemanticLaws`
  - `BrainRepresentationSemanticDepth`,
    `BrainThemeSemanticTransportLaws`, and
    `BrainConnectorEndToEndSemanticDepth`
    feed `BrainConnectorEndToEndSemanticLaws`
- bounded streaming/channel owner surfaces
- bounded structural summaries such as eigenclass and macro-adjacency
- typed interfaces where a later codec or brain-side mapping could attach
- exact attachment-law surfaces above the current crossover package

### Still adjacent

What remains mostly adjacent rather than localized here:

- deeper brain-native structural formalization
- brain-side extraction or coarse-graining semantics beyond the current theorem-thin summaries
- richer theorem-owned brain-to-DNA representation semantics beyond the new bounded transport law
- realistic synthesis/sequencing channel semantics beyond the new bounded realism law
- a full codec from brain-side structure into DNA-side admissible carriers

So the current crossover lane is best read as:

- `partial local owner/compatibility/law/consumer surfaces + archive design`

not as:

- a finished brain-DNA formal subsystem,
- a local closure theorem lane,
- or evidence that the physics spine has absorbed the brain/crossover program.

## Current claim boundary

The repo is currently entitled to say only this:

- the DNA lane already exposes owner surfaces that are suitable attachment
  points for a future brain-DNA / codec / channel bridge,
- the repo now also has theorem-thin local brain and crossover surfaces that
  make that bridge partially local rather than purely archival,
- the repo now has an explicit local extraction-aware connector from the brain
  lane into the current DNA/chemistry boundary,
- archive and sibling-repo material give that bridge program a sharper design
  direction than "missing from zero",
- but the crossover lane is still mostly a design and interface pressure lane,
  not a theorem-closing lane.

## Current Explicit Connector Path

The cleanest currently local connector path is:

1. `Brain`
   - `Ontology/Brain/BrainExtractionSurface.agda`
   - `Ontology/Brain/BrainInvariantSurface.agda`
   - `Ontology/Brain/BrainInvariantDepth.agda`
2. `Brain -> BrainDNA connector`
   - `Ontology/BrainDNA/BrainExtractionChemistryConnector.agda`
   - `Ontology/BrainDNA/BrainExtractionConnectorDepth.agda`
   - `Ontology/BrainDNA/BrainExtractionConnectorSemantics.agda`
3. `BrainDNA codec / structural carrier`
   - `Ontology/BrainDNA/BrainThemeConnectorSurface.agda`
   - `Ontology/BrainDNA/BrainDnaRepresentationMap.agda`
   - `Ontology/BrainDNA/BrainRepresentationTransportLaws.agda`
   - `Ontology/BrainDNA/BrainRepresentationSemanticDepth.agda`
   - `Ontology/BrainDNA/BrainRepresentationSemanticLaws.agda`
   - `Ontology/BrainDNA/BrainRepresentationConsumerSemantics.agda`
   - `Ontology/BrainDNA/BrainRepresentationConsumerLaws.agda`
   - `Ontology/BrainDNA/BrainRepresentationIntegratedSemantics.agda`
   - `Ontology/BrainDNA/BrainCodecSemanticDepth.agda`
   - `Ontology/BrainDNA/BrainCodecSemanticLaws.agda`
   - `Ontology/BrainDNA/BrainCodecPayloadRecoveryBridge.agda`
   - `Ontology/BrainDNA/BrainSummaryStructuralConsumer.agda`
   - `Ontology/BrainDNA/BrainStructuralConsumerSemantics.agda`
   - `Ontology/BrainDNA/BrainConnectorSemanticDepth.agda`
   - `Ontology/BrainDNA/BrainThemeChemistryChannelTransport.agda`
   - `Ontology/BrainDNA/BrainThemeSemanticTransportLaws.agda`
   - `Ontology/BrainDNA/BrainThemeEndToEndSemanticDepth.agda`
   - `Ontology/BrainDNA/BrainConnectorEndToEndSemanticLaws.agda`
   - `Ontology/BrainDNA/BrainThemeConsumerSemantics.agda`
   - `Ontology/BrainDNA/BrainThemeConsumerLaws.agda`
   - `Ontology/BrainDNA/BrainConnectorConsumerSemantics.agda`
   - `Ontology/BrainDNA/BrainConnectorConsumerLaws.agda`
   - `Ontology/BrainDNA/BrainThemeIntegratedSemantics.agda`
   - `Ontology/BrainDNA/BrainConnectorIntegratedConsumerSemantics.agda`
4. `DNA / chemistry boundary`
   - `Ontology/DNA/CrossoverAbstractChannelLaws.agda`
   - `Ontology/DNA/CrossoverSemanticChecksumLaws.agda`
   - `Ontology/DNA/SupervoxelChemistryLongWindowLaws.agda`
   - `Ontology/DNA/SynthesisSequencingRiskSurface.agda`
   - `Ontology/DNA/SynthesisSequencingRealismLaws.agda`
   - `Ontology/DNA/SynthesisSequencingRealismDepth.agda`
   - `Ontology/DNA/SynthesisSequencingRealismSemantics.agda`
   - `Ontology/DNA/SynthesisSequencingRealismConsumer.agda`
   - `Ontology/DNA/SynthesisSequencingConsumerLaws.agda`
   - `Ontology/DNA/SynthesisSequencingIntegratedRealism.agda`
   - `Ontology/DNA/ChemistrySheetHamiltonian.agda`
5. `Physics-facing chemistry carrier`
   - `DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda`

This is an explicit local connector path.

It is now also explicitly consumed by:

- `BrainThemeConnectorSurface.agda`
- `BrainDnaRepresentationMap.agda`
- `BrainRepresentationTransportLaws.agda`
- `BrainRepresentationSemanticDepth.agda`
- `BrainRepresentationSemanticLaws.agda`
- `BrainRepresentationConsumerSemantics.agda`
- `BrainRepresentationConsumerLaws.agda`
- `BrainRepresentationIntegratedSemantics.agda`
- `BrainChemistryCodecConsumer.agda`
- `BrainAtomicChemistryHandoff.agda`
- `BrainConnectorSemanticDepth.agda`
- `BrainThemeChemistryChannelTransport.agda`
- `BrainThemeSemanticTransportLaws.agda`
- `BrainThemeEndToEndSemanticDepth.agda`
- `BrainConnectorEndToEndSemanticLaws.agda`
- `BrainThemeConsumerSemantics.agda`
- `BrainThemeConsumerLaws.agda`
- `BrainConnectorConsumerSemantics.agda`
- `BrainConnectorConsumerLaws.agda`
- `BrainThemeIntegratedSemantics.agda`
- `BrainConnectorIntegratedConsumerSemantics.agda`

It is still bounded and theorem-thin:

- it does not yet provide richer end-to-end brain-to-DNA representation
  semantics beyond the current bounded semantic-law, consumer-law, and
  integrated-semantics layers
- it does not yet provide richer synthesis/sequencing realism beyond the
  current bounded realism-semantics, consumer-law, and integrated-realism
  layers
- it does not yet transport the richer brain themes into the physics-facing
  chemistry carrier with richer end-to-end consumer semantics beyond the
  current bounded transport, semantic-depth, semantic-law, consumer-law, and
  integrated-semantics layers

The repo is not currently entitled to say:

- that brain structure is localized in Agda here,
- that a brain-to-DNA encoding theorem exists,
- that synthesis/sequencing recovery is modeled realistically here,
- or that this lane contributes current closure evidence on the physics spine.

## Notebook-Confirmed Brain Themes Not Yet Localized Through The Crossover

The notebook/archive confirms four richer brain-side themes:

- brain-region automaton mapping
- Klüver form constants / hallucination geometry / log-polar V1/V2
- grokking / eigenbasis / Fourier-basis phase transition
- gap junctions / morphospace error correction

Current local owner status for those themes:

- localized locally:
  - `BrainRegionAutomatonSurface.agda`
  - `BrainVisualFormConstantSurface.agda`
  - `BrainLearningEigenbasisSurface.agda`
  - `BrainMorphospaceGapJunctionSurface.agda`
- all four notebook-confirmed themes now have bounded local owner surfaces

The crossover lane does not yet carry those themes as theorem-owned semantics.
The current local connector reaches:

- extraction
- bounded brain-theme transport
- bounded representation semantics
- bounded representation transport laws
- bounded representation semantic-depth
- bounded representation semantic-laws
- packet/codec/channel boundaries
- structural summaries
- chemistry/Hamiltonian boundaries
- bounded theme-to-chemistry/channel/handoff transport
- bounded theme semantic-transport laws
- bounded theme end-to-end semantic-depth

The current local connector does not yet provide:

- richer theorem-owned end-to-end representation integration laws
- a richer visual-geometry-to-chemistry integrated consumer bridge
- a richer learning/eigenbasis-to-codec integrated consumer bridge
- a richer morphospace/gap-junction-to-channel integrated consumer bridge

These are real blockers, not just omitted narrative.

## Four concrete next bridge targets

### 1. Richer brain->DNA representation semantics beyond the now-landed bounded transport, semantic-depth, semantic-law, consumer-semantics, consumer-law, and integrated-semantics surfaces

The notebook-backed reading is that a strict
`"no theorem-owned brain->DNA representation map"` label is too strong.
What already exists locally is:

- `BrainVocabularyPacketCompatibility.agda`
- `BrainStateCrossoverLaws.agda`
- `BrainThemeConnectorSurface.agda`
- `BrainDnaRepresentationMap.agda`
- `BrainRepresentationTransportLaws.agda`
- `BrainRepresentationSemanticDepth.agda`
- `BrainRepresentationSemanticLaws.agda`
- `BrainRepresentationConsumerSemantics.agda`
- `BrainRepresentationConsumerLaws.agda`
- `BrainRepresentationIntegratedSemantics.agda`

So the honest local blocker is not absence from zero, but lack of richer
semantic transport beyond the current bounded owner, transport-law,
semantic-depth, semantic-law, consumer-semantics, consumer-law, and
integrated-semantics surfaces.

Target shape:

- one richer downstream consumer/semantic surface over the existing
  representation owners
- exact profile/order/width/admissibility/recovery/theme alignment transport
- no claim of realistic biological encoding or complete payload semantics

### 2. Richer theme-specific end-to-end semantics beyond the now-landed bounded theme transport, semantic-law, end-to-end semantic-depth, consumer-semantics, consumer-law, and integrated-semantics surfaces

What already exists locally is:

- `BrainThemeChemistryChannelTransport.agda`
- `BrainThemeSemanticTransportLaws.agda`
- `BrainThemeEndToEndSemanticDepth.agda`
- `BrainThemeConsumerSemantics.agda`
- `BrainThemeConsumerLaws.agda`
- `BrainThemeIntegratedSemantics.agda`

So the honest local blocker is not absence from zero, but lack of richer
theme-specific downstream semantics beyond the current bounded transport,
semantic-law, end-to-end semantic-depth, consumer-semantics, and
consumer-law, and integrated-semantics surfaces.

Target shape:

- one richer downstream consumer/semantic surface over the existing theme
  transport owners
- exact theorem-thin alignment from:
  - region automaton
  - visual form-constant geometry
  - learning/eigenbasis phase profiles
  - morphospace/gap-junction profiles
  into the chemistry/channel/handoff boundaries
- no strong neuroscience or biological completeness claim

### 3. Richer synthesis/sequencing realism beyond the now-landed bounded realism-law, realism-depth, realism-semantics, realism-consumer, consumer-law, and integrated-realism surfaces

The notebook-backed reading is also that a strict
`"no bounded synthesis/sequencing realism surface yet"` label is now outdated.
What already exists locally is:

- `SynthesisSequencingRiskSurface.agda`
- `SynthesisSequencingRealismLaws.agda`
- `SynthesisSequencingRealismDepth.agda`
- `SynthesisSequencingRealismSemantics.agda`
- `SynthesisSequencingRealismConsumer.agda`
- `SynthesisSequencingConsumerLaws.agda`
- `SynthesisSequencingIntegratedRealism.agda`

So the honest local blocker is not total absence, but lack of richer
wet-lab-facing synthesis/sequencing semantics beyond the current bounded risk
owner, realism-law, realism-depth, realism-semantics, realism-consumer, and
consumer-law, and integrated-realism surfaces.

Target shape:

- one richer downstream consumer/law surface over the existing risk owner
- one richer downstream consumer/semantic surface over the current realism
  owners
- explicit dependence on:
  - `StreamingEncoderSurface.agda`
  - `ChannelCodingSurface.agda`
  - `CrossoverSemanticChecksumLaws.agda`
  - `SynthesisSequencingRiskSurface.agda`
- no claim yet of external empirical validity or realistic lab calibration

### 4. Richer whole-chain semantics beyond the now-landed connector semantic-depth, end-to-end semantic-law, consumer-semantics, consumer-law, and integrated-consumer-semantic surfaces

What already exists locally is:

- `BrainRepresentationSemanticDepth.agda`
- `BrainRepresentationSemanticLaws.agda`
- `BrainThemeSemanticTransportLaws.agda`
- `BrainThemeEndToEndSemanticDepth.agda`
- `BrainConnectorEndToEndSemanticDepth.agda`
- `BrainConnectorEndToEndSemanticLaws.agda`
- `BrainConnectorConsumerSemantics.agda`
- `BrainConnectorConsumerLaws.agda`
- `BrainConnectorIntegratedConsumerSemantics.agda`

So the honest local blocker is no longer missing chain structure. It is lack of
richer whole-chain downstream semantics beyond the current bounded end-to-end
semantic-law, consumer-semantics, consumer-law, and integrated-consumer
semantic surfaces.

Target shape:

- one richer downstream consumer/semantic surface over the existing connector
  end-to-end owners
- exact theorem-thin coherence across:
  - representation
  - theme transport
  - chemistry/channel consumers
  - physics-facing handoff
- no closure claim, no biological completeness claim

## Status reading

- `DNA`: real local formal lane
- `Brain`: adjacent lane with theorem-thin local owner/summary surfaces
- `Brain-DNA / codec / channel crossover`: partially localized with owner,
  compatibility, law, and consumer surfaces; still interface-first,
  archive-guided, and not theorem-closing

That is the strict local reading consistent with the updated diagrams and with
`Docs/PhysicsGuide.md`.

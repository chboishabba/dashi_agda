# Magpie Vocal Language Atlas — Design

Date: 2026-09-15
Branch: `agent/birdsong-youtube-seeds`
Primary PR: #933
Runtime companion: `chboishabba/animalexic` PR #6

## Purpose

Build a provenance-bound, append-only atlas of observed Australian magpie vocal behaviour that can support progressively stronger questions:

1. What recurrent acoustic/motor motifs are observed?
2. Which motifs are associated with particular behavioural and social contexts?
3. Which call families recur across individuals, groups and regions?
4. Which parts of a call family are species-wide versus group-, region- or individual-specific?
5. When evidence is sufficient, which call/sequence families support a stable functional or referential interpretation?

The system is designed so that a future user could ask human-readable questions such as “what is the closest supported magpie analogue of a greeting here?” or “how is this functional call realized by Brisbane versus Melbourne populations?” without allowing embedding similarity, geography, or a model prediction to manufacture semantic truth.

The same architecture should later generalize to other vocal-learning social birds, including corvids, while keeping species-specific semantics and evidence separate.

## Core scientific object

Each observed vocal event is an append-only situated observation:

`VocalEvent = acoustic form × audiovisual/motor state × behavioural context × geography × physical time × environment × social state × provenance`

The implementation should preserve these fibres independently rather than forcing them into one opaque latent vector.

A useful conceptual decomposition is:

`z_observed = semantic-core ⊗ geographic-realization ⊗ group-syntax ⊗ individual-voice ⊗ situated-context ⊗ environment ⊗ recording-provenance`

This is a factorized design principle, not a claim that the representation must be additive or Euclidean.

## Observation hierarchy

The atlas must support the following containment hierarchy:

`segment -> call -> call-sequence -> bout -> interaction-episode -> group-repertoire -> regional-repertoire -> species-wide-atlas`

Every promoted higher-level object must retain the identities of its lower-level observations and their source receipts.

## Event record

The minimal formal/runtime event carrier should expose:

### Source and time

- `eventId`
- `sourceId`
- `mediaId`
- `startTime`
- `endTime`
- source-relative PTS/audio clock references
- media/source provenance
- byte identity when available
- acquisition method

### Biological identity

- species identity status
- individual identity status
- group identity status
- sex/age class only when source-bound

Unknown identity is first-class and must not be guessed.

### Geography and environment

- location value
- location precision class
- location provenance
- region/population label
- habitat/context
- date/time-of-day/season when known
- weather or broad environmental context when known
- surrounding animals/humans/predators where observed

Location precision is typed: country, region, city, site, approximate coordinates, exact coordinates. A title such as “Melbourne magpie” cannot be promoted to exact coordinates.

### Acoustic form

- candidate acoustic embedding
- pitch/fundamental-frequency contour where measurable
- spectral envelope/centroid/band structure
- duration
- temporal envelope
- call/segment rhythm
- syllable/segment sequence
- RMS digital amplitude proxy
- timbre/breathiness descriptors

Raw digital amplitude remains distinct from calibrated sound pressure level and radiated acoustic power.

### Visible motor/display state

- beak/head/body motion
- posture
- approach/withdrawal
- stepping/bobbing/dance-like movement
- visible interaction partners

Visible motion remains distinct from biomechanical work, metabolic expenditure, heart rate, respiratory pressure or airflow.

### Behaviour and social context

Candidate observation labels may include:

- feeding/foraging
- vigilance/alarm
- approach/contact
- begging
- courtship/display
- aggression/territorial interaction
- play/social interaction
- flock/group coordination
- human-directed interaction
- predator-related context

These are observational/context labels, not semantic meanings unless promoted by independent evidence.

### Governance

- candidate call family
- candidate functional context
- candidate semantic family
- decision/status
- confidence/residual
- provenance
- receipt IDs
- reopening dependencies

## Hierarchical latent architecture

The scientific core should use a hierarchical/factorized latent atlas, not one giant embedding.

### Acoustic-form fibre

Represents recurring call/segment form and sequence structure.

### Semantic/function fibre

Represents hypothesized function or referential class only after appropriate semantic payments.

### Geographic-realization fibre

Represents population/region-conditioned variation in an already defined call/function family.

### Group-syntax fibre

Represents socially learned repertoire/sequence variation associated with a group.

### Individual-voice fibre

Represents stable individual realization differences when individual identity is paid.

### Context/environment fibre

Represents behavioural, social and environmental conditions that may explain apparent variation.

### Recording/provenance fibre

Represents microphone, codec, source platform, channel/uploader, distance, background noise and other acquisition effects so they cannot silently masquerade as biology.

## Semantic promotion ladder

Human-readable semantic labels such as “hello”, “keep watch”, “food here”, or “danger” are late-stage interpretations.

The staged ladder is:

`observed vocal event`
-> `acoustic/motor candidate cluster`
-> `cross-recording recurrent motif`
-> `context-associated call family`
-> `cross-individual/group functional family`
-> `cross-population candidate semantic invariant`
-> `validated functional/referential class`

A semantic promotion must retain the independent evidence that paid it. Examples of acceptable payments include repeated production context, receiver response, longitudinal within-group use, playback/intervention experiments, published ethology, or another source-bound behavioral test.

No single embedding, classifier confidence, source title, geographic predictability, or repeated model self-agreement is sufficient.

## Universal core and accent/dialect model

The atlas should support the query:

`same supported functional/semantic family + different regional/group realization`

For a semantic/function family `F`, regional realization fibres may be represented as `F(region)` without implying that region created the function.

A future “Brisbane accent vs Melbourne accent” claim requires evidence that variation remains after controlling for recording provenance, environment, group/individual composition and context.

Required firewall:

`region predictable from acoustic observation != regional dialect`

Similarly:

- channel/uploader predictability != population effect
- background species/noise != dialect
- codec/microphone signature != dialect
- individual identity != regional accent
- group syntax != population-wide dialect automatically
- semantic invariance != acoustic invariance
- acoustic invariance != semantic invariance

## Consumer-relative questions

The atlas should be able to answer distinct consumer-indexed questions without one observer being treated as universally adequate:

- acoustic-nearest-neighbour retrieval
- same-call-family retrieval
- same-context retrieval
- same-group sequence comparison
- regional realization comparison
- individual voice comparison
- semantic/function candidate retrieval
- source/provenance audit

A representation adequate for acoustic similarity may be inadequate for semantic identity or geographic comparison.

## Runtime data flow

The first runtime path reuses Animalexic rather than creating a separate ingestion stack:

`YouTube source`
-> `yt-dlp transient URL resolution`
-> `ffmpeg audio/video clocks`
-> `source-bound frame/audio observations`
-> `candidate call segmentation`
-> `candidate acoustic/motor features`
-> `append-only VocalEvent records`
-> `candidate latent atlas`

The three initial seed sources are acquisition observations, not semantic labels.

## Initial empirical target

The first real-data milestone is deliberately modest:

1. acquire synchronized audio/video observations from the three seed videos;
2. segment candidate vocal events;
3. derive acoustic feature trajectories and visible-motion proxies;
4. discover recurrent motifs across sources;
5. retain source/context/geography identity separately;
6. test which motif differences may be explained by recording/context versus biological factors.

No “universal hello” claim is expected from the initial three videos.

## Cross-species extension

The architecture should be generic enough to support crow/corvid use cases later, but the current formal owners remain magpie-specific.

A future crow atlas could support a practical interaction loop such as:

`observe local crow repertoire -> identify supported context/function families -> play or synthesize a candidate signal -> observe receiver response -> update evidence`

However, synthesis/playback is an intervention lane and must remain separate from passive semantic inference. A system must not claim “the crow said yes” or generate an instruction-like vocalization merely because a latent model predicts such a label. Interaction claims require receiver-response evidence and appropriate animal-welfare/safety constraints.

## Formal owners proposed

After this design is approved, the first implementation plan should create a small set of owners rather than one large ontology:

1. `DASHI/Biology/MagpieVocalAtlasObservationExact.agda`
   - event hierarchy and append-only situated observation carrier;
   - typed identity/location/provenance boundaries.

2. `DASHI/Biology/MagpieVocalAtlasLatentExact.agda`
   - separated semantic/geographic/group/individual/context/recording fibres;
   - consumer-relative projection adequacy;
   - no single scalar “meaning score”.

3. `DASHI/Biology/MagpieSemanticPromotionExact.agda`
   - semantic promotion ladder;
   - independent evidence payments;
   - explicit nonfactorability/firewalls for latent similarity and region predictability.

4. Thin imports into the current birdsong/Animalexic validation roots.

Runtime companion changes belong in Animalexic PR #6 and should emit candidate-only events through the existing trajectory/governance machinery.

## Required formal firewalls

The initial formalization must include explicit blockers for:

- `latentSimilarity -> sameMeaning`
- `sameAcousticCluster -> sameFunction`
- `regionPredictability -> dialect`
- `groupSequenceDifference -> regionalDialect`
- `sourceTitle -> exactLocation`
- `videoSpeciesLabel -> individualIdentity`
- `rawAmplitude -> calibratedSPL`
- `visibleMotion -> biomechanicalWork`
- `AVSynchrony -> causality`
- `semanticCandidate -> interventionAuthority`
- `modelPrediction -> animalIntent`
- `repeatedSelfPrediction -> independentCorroboration`

## Reopening semantics

The atlas is append-only. Later evidence may refine or reopen:

- source/media identity
- species/individual/group identity
- event segmentation
- location precision
- call-family membership
- functional/context interpretation
- geographic realization
- semantic promotion

New evidence does not erase the historical candidate state or retroactively make an earlier coarse observer adequate.

## Attribution and scientific-status boundary

Every external source retains author/title/publication/DOI/URL/source kind/formalisation relationship where available. Citation does not import proof or authority.

Observed YouTube clips, published ethology, runtime-derived embeddings and DASHI theorems are separate source roles.

Empirical claims remain empirical; Agda formalizes the evidence/dependency/adequacy architecture and does not prove that a real magpie call has a particular meaning.

## Success criteria for the first tranche

The first implementation tranche is successful when:

- the three proposed Agda owners exist and are imported by focused validation roots;
- an observed event cannot be promoted to semantic identity using acoustic similarity alone;
- region predictability is formally insufficient for dialect status;
- group/individual/geography/context/recording factors remain separately recoverable;
- source/location precision and provenance are explicit;
- Animalexic can emit candidate observations compatible with the event carrier;
- exact-head certification status is reported separately from source-written status.

## Non-goals for this tranche

- claiming a decoded magpie dictionary;
- synthesizing or broadcasting bird calls;
- claiming animal intent, consent, promises or contractual-like meaning;
- estimating heart rate, metabolism or respiration from ordinary video without a validated measurement model;
- using geographic labels as ground-truth semantics;
- building a new global planner or replacing existing Animalexic/DASHI governance machinery.

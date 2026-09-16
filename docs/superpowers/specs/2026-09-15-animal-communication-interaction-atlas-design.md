# Animal Communication / Interaction Atlas — Design

Date: 2026-09-15
Branch: `agent/animal-communication-interaction-atlas`
Parent: merged magpie atlas PR #933
Runtime companion: `chboishabba/animalexic`

## Purpose

Generalize the existing magpie vocal-language atlas into a species-agnostic communication and interaction architecture while preserving species-local signal structure, provenance, multimodal observation, consumer-relative adequacy, and fail-closed semantic promotion.

The target use case is BirdNET-like scene understanding extended in two directions:

1. detect and track multiple simultaneous animals/signallers in a real scene, including overlapping chorus events;
2. infer evidence-bounded communicative function from signal, addressee, context, history, and receiver response rather than stopping at species identification.

The architecture must support birds, cetaceans, bats, primates and other communicative animals without forcing them into one universal acoustic ontology or one universal latent space.

## Scope decomposition

This design is the first of two architectural subprojects.

### Subproject A — formal communication/interaction core

This spec owns the generic Agda model:

- scene observations;
- multiple simultaneous candidate emitters;
- sender/addressee identity status;
- signal modality and species-local signal reference;
- pre-state/context;
- receiver/world response;
- interaction turns and temporal ordering;
- cross-species relational analogies;
- semantic evidence/payment boundaries;
- adapter interface for existing magpie owners.

### Subproject B — runtime multi-emitter audiovisual decomposition

A later spec will own concrete Animalexic runtime implementation for:

- overlapping audio-event detection/source separation;
- visual animal detection/tracking;
- audiovisual emitter association;
- simultaneous species hypotheses;
- per-emitter signal/event segmentation;
- same-scene interaction graph production.

Subproject A defines the receipt/interface that Subproject B must eventually emit. It does not invent or assume a particular source-separation model.

## Core scene object

The generic object is a scene rather than a single call clip.

`AnimalCommunicationScene = source/time/environment × candidate participants × emitted signals × interaction turns × provenance`

A scene may contain zero, one, or many simultaneous candidate emitters. Overlapping signals are first-class and must not be flattened into one canonical emitter merely because one classifier has the highest score.

Each participant keeps independent identity coordinates:

- species identity status;
- individual identity status;
- group/population identity status;
- spatial/visual track identity status;
- acoustic/source-stream identity status.

Cross-modal association is separately receipted.

## Generic event object

The generic event is conceptually:

`E_i = (S_i, P_i, R_i, C_i, B_i^-, B_i^+, G_i, T_i, Env_i, M_i, V_i)`

where:

- `S_i`: emitted signal or multimodal display;
- `P_i`: producer/sender identity/status;
- `R_i`: receiver/addressee set and identity/status;
- `C_i`: social/behavioural context;
- `B_i^-`: relevant pre-event state/history;
- `B_i^+`: receiver/world response after the event;
- `G_i`: group/population/geographic context;
- `T_i`: source time, physical ordering, duration and lag coordinates;
- `Env_i`: environmental/surrounding context;
- `M_i`: multimodal bodily state;
- `V_i`: provenance/measurement/recording state.

The event carrier is append-only. Unknown sender, receiver, species, function or source association remain explicit rather than guessed.

## Signal modalities

The shared core must not assume that communication is acoustic.

Initial modality vocabulary:

- acoustic/vocal;
- visual gesture/posture/display;
- locomotor/movement display;
- substrate vibration;
- electric;
- chemical/olfactory;
- tactile/contact;
- multimodal composite;
- unresolved/other.

Species adapters define their own signal hierarchy and feature carriers.

Examples:

- magpie: `segment -> call -> sequence -> bout`;
- sperm whale: `click -> coda -> coda sequence -> exchange`;
- humpback whale: `unit -> phrase -> theme -> song`;
- dolphin: `whistle/click train -> exchange`;
- bat: `syllable -> call sequence -> dyadic interaction`;
- primate: `call -> call combination -> interaction turn`.

These are adapters/refinements, not declarations that the underlying cognitive mechanisms are identical.

## Multi-emitter scene semantics

A scene may contain simultaneous animal sources:

`Scene_t -> {EmitterCandidate_1, ..., EmitterCandidate_n}`

Each emitted event carries zero or more candidate emitter associations with provenance/residuals.

The formal layer must preserve at least these distinctions:

- detected acoustic event != identified animal;
- identified species != identified individual;
- visual track != acoustic source unless association is paid;
- loudest source != unique sender;
- temporal overlap != interaction;
- co-occurrence != addressee relation;
- classifier probability != canonical scene truth.

A future runtime may propose source separation, localization, tracking or audiovisual association, but formal promotion requires receipts compatible with Animalexic candidate/promote/abstain/reject governance.

## Interaction turns

The universal interaction object is:

`InteractionTurn = sender × receivers × signal × preState × response × deltaT × nextTurn × context × provenance`

A receiver set may be empty, one receiver, multiple receivers, or unresolved.

`response` is a first-class observation, not merely a semantic annotation. It may include:

- receiver vocal response;
- receiver movement/posture change;
- approach/withdrawal;
- vigilance/alarm change;
- feeding/foraging response;
- group reconfiguration;
- human action where humans are participants;
- no detected response;
- unresolved response.

No detected response is not equivalent to no response unless observation coverage is sufficient.

## Interaction graph over time

Animal communication is represented as a time-indexed graph rather than a bag of isolated calls.

Nodes may represent participants, events or turns; edges represent source-bound temporal/interaction relationships such as:

- emitted-by;
- directed-to candidate;
- followed-by;
- responded-to;
- overlaps-with;
- same-bout/same-episode;
- same-group candidate;
- same-source-track candidate.

A graph edge is an observation/proposal with provenance, not automatic causal truth.

## Species-local atlas + cross-species relational schema

There is no single universal animal-language latent coordinate system.

The architecture is:

`species-local latent atlas + cross-species typed relational schema`.

Species-local atlases own signal form, repertoire structure, population/group variation and semantic/function evidence.

The cross-species schema allows structural comparisons such as:

- receiver-specific addressing;
- individual identity signalling;
- group/population dialect or culture;
- call combination/compositional candidates;
- turn-taking;
- receiver-response prediction;
- multimodal display;
- social learning.

Required firewall:

`structural analogy != same mechanism != same semantics`.

No cross-species relation transfers a semantic label, cognitive mechanism, authorship, truth or empirical authority.

## Generic latent fibres

The shared latent schema exposes independently recoverable/reopenable fibres:

- signal-form fibre;
- sender identity fibre;
- receiver/addressee fibre;
- interaction/turn fibre;
- response fibre;
- functional/semantic hypothesis fibre;
- group/population/geographic fibre;
- individual realization fibre;
- history/context fibre;
- environmental fibre;
- recording/measurement provenance fibre;
- modality-specific physical measurement fibre.

A downstream implementation may learn a joint representation, but canonical state must retain enough structure to audit and reopen these fibres separately.

## Semantic/function evidence ladder

The generic promotion ladder is:

`signal observed`
-> `recurrent form`
-> `context association`
-> `directed/addressee association`
-> `predictive receiver response`
-> `playback/intervention response`
-> `supported functional/reference class`
-> `candidate compositional semantics`.

The ladder is not mandatory. An application may stop at any scientifically supported level; e.g. a cultural song repertoire can be valuable without referential decoding.

Independent evidence coordinates include:

- repeated production context;
- addressee identity evidence;
- natural receiver response;
- longitudinal interaction history;
- controlled playback/intervention evidence;
- published ethology;
- same-object identity;
- provenance/custody;
- independent ancestry/corroboration.

## BirdNET-like consumer separation

Species detection and semantic/function inference are different consumers.

The architecture must support queries such as:

- which species/animals are present?
- which candidate emitter produced this event?
- which signals overlap in the chorus?
- what call/signal family is this?
- who is it directed toward?
- what receiver response follows?
- what function is supported by the evidence?
- does this group/region realize the same function differently?

Required query-indexed firewalls:

- species-classification adequacy != emitter-association adequacy;
- emitter-association adequacy != semantic adequacy;
- semantic adequacy != intervention authority;
- one consumer's promoted observation != promotion for every consumer.

## Local interaction protocol use case

The long-term crow/farm example is represented as a local learned interaction protocol, not a literal English translation.

The empirical object is:

`human action -> animal signal -> animal behaviour -> human response -> animal response`.

A human-readable gloss such as “food request”, “alarm/watch response”, or “contact/greeting” may be attached only at the strongest evidence level paid by repeated context/receiver-response/intervention evidence.

The core must explicitly block:

- functional gloss -> animal intent;
- response correlation -> promise/agreement;
- model-generated signal -> known animal meaning;
- successful one-off interaction -> stable protocol;
- reward association -> propositional negotiation.

## Relation to existing magpie owners

The merged magpie owners remain append-only and valid:

- `MagpieVocalAtlasObservationExact`;
- `MagpieVocalAtlasLatentExact`;
- `MagpieSemanticPromotionExact`.

The generic core is factored beneath them by adapters/embeddings rather than deleting or rewriting historical owners.

The intended relationship is:

`AnimalCommunication* generic core`
-> `Magpie* adapter/refinement`
-> existing magpie observations and semantic-promotion surfaces.

A magpie adapter must preserve all current magpie-specific identity/location/provenance and dialect firewalls.

## Proposed formal owners

The first implementation plan should create focused owners:

1. `DASHI/Biology/AnimalCommunicationSceneObservationExact.agda`
   - scene, participant, modality and simultaneous-emitter candidate carriers;
   - identity and cross-modal association receipts;
   - multi-emitter/non-collapse boundaries.

2. `DASHI/Biology/AnimalCommunicationInteractionExact.agda`
   - sender, receiver set, signal reference, pre-state, response, delta-time, next-turn and interaction graph relation carriers;
   - response/addressee as first-class fibres.

3. `DASHI/Biology/AnimalCommunicationLatentExact.agda`
   - generic independently reopenable fibres;
   - query-indexed consumer family;
   - exact finite counterexamples separating species detection, emitter assignment and semantic/function adequacy.

4. `DASHI/Biology/AnimalCommunicationSemanticEvidenceExact.agda`
   - generic semantic/function ladder;
   - evidence payments;
   - intervention/intent/promise firewalls.

5. `DASHI/Biology/MagpieAnimalCommunicationAdapterExact.agda`
   - embeds the existing magpie event/latent/promotion surfaces into the generic core without changing their historical meaning.

6. focused validation/static contract and rollup imports.

## Runtime handoff ABI

Subproject B should eventually emit candidate scene/event receipts compatible with the generic core. The formal interface requires at minimum:

- scene/source ID;
- source-relative and/or physical time;
- candidate emitter ID;
- candidate species identity/status;
- visual track ID/status where available;
- acoustic/source-stream ID/status where available;
- cross-modal association status/residual;
- signal/event interval;
- modality;
- observed context/environment;
- candidate receiver/addressee IDs;
- observed receiver response interval/type;
- provenance/measurement/source receipt;
- Animalexic decision state.

The ABI permits multiple candidate emitter rows for one event and multiple overlapping events in one scene.

## Reopening semantics

Later evidence may selectively reopen:

- species identity;
- individual/group identity;
- source separation;
- audiovisual association;
- event segmentation;
- sender/addressee assignment;
- response association;
- interaction-turn ordering;
- call/signal-family membership;
- geographic/population realization;
- functional interpretation;
- semantic promotion.

Reopening does not erase prior candidate receipts.

## Required formal firewalls

The initial generic core must block:

- `sceneContainsSpecies -> speciesProducedEvent`;
- `visualTrackNearby -> acousticEmitterIdentity`;
- `temporalOverlap -> interaction`;
- `coOccurrence -> addressee`;
- `loudestSignal -> uniqueSender`;
- `speciesClassifierConfidence -> semanticMeaning`;
- `signalSimilarity -> sameFunction`;
- `receiverPrediction -> causalMechanism`;
- `naturalResponseCorrelation -> playbackEffect`;
- `playbackEffect -> propositionalMeaning`;
- `functionalGloss -> animalIntent`;
- `response -> promiseOrAgreement`;
- `crossSpeciesStructuralAnalogy -> sameMechanism`;
- `crossSpeciesStructuralAnalogy -> sameSemantics`;
- `oneConsumerPromotion -> allConsumerPromotion`.

## Testing / validation strategy

Use repository-native RED-first source/static contracts.

The focused static contract should require all five owners and check named boundaries/counterexamples before production owners land.

Finite fixtures should include:

1. evening chorus: two species present, one event unresolved between emitters — species presence does not assign emitter;
2. audiovisual crossing: visual track and acoustic event co-occur but association differs between worlds — proximity does not determine source identity;
3. addressee collision: same signal and sender, different receiver-directed context — signal form alone does not determine addressee;
4. response collision: same signal/context, different downstream receiver responses — signal/context alone does not determine function;
5. semantic collision: same predictive receiver-response surface, one world is recording/context confounded — predictability alone does not establish meaning;
6. magpie adapter fixture showing the current magpie objects embed without gaining new semantic authority.

Exact-head Agda/kernel certification remains a separate status coordinate.

## Attribution boundary

Animalexic/DASHI owns the generic schema, finite counterexamples, adapters, proof structure and governance.

External ethology sources pay only source-bounded empirical premises for their species/system.

A dolphin, whale, bat, primate, bird or other animal study does not donate its mechanism or semantics to another species merely because the generic interaction schema can represent both.

Citation imports neither proof nor authority.

## Success criteria for Subproject A

The formal tranche is successful when:

- the generic scene/interaction/latent/semantic owners exist;
- simultaneous candidate emitters are representable without forced collapse;
- addressee and receiver response are first-class coordinates;
- species presence cannot determine emitter identity by theorem;
- emitter identity cannot determine semantic/function identity by theorem;
- overlapping/co-occurring events cannot manufacture interaction/addressee relations;
- cross-species analogies cannot transfer mechanism or semantics;
- existing magpie owners embed through an adapter without being rewritten;
- a stable runtime handoff ABI for Subproject B is declared;
- exact-head certification status is reported separately from source-written status.

## Non-goals for Subproject A

- implementing source separation or computer vision models;
- claiming BirdNET-equivalent species-classification performance;
- building a universal cross-species latent embedding;
- decoding any animal language into English;
- synthesizing or broadcasting animal signals;
- claiming animal intent, consent, promises or agreements;
- estimating unobserved physiology from ordinary audiovisual data;
- replacing existing Animalexic candidate/promote/abstain/reject governance;
- rewriting historical magpie owners.

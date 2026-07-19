# ITIR / TiRCorder / SensiBlaw / Streamline boundary

This tranche formalises the responsibility and provenance boundaries discussed
across the ITIR, TiRCorder, SensiBlaw, Streamline, external-ontology, CRM, and
Pol.is design threads.

## Canonical ownership split

- **TiRCorder** owns recording, file handling, transcription, diarisation,
  segmentation, word/utterance timing, source hashes, and replayable packet
  emission.
- **SensiBlaw** owns the canonical text substrate and every downstream semantic
  operation: tokenisation, NLP, concepts, actor resolution, event construction,
  claims, harms, wrongs, protected interests, value frames, rule atoms, graph
  projection, policy evaluation, finance reconciliation, persisted joined
  caches, and Streamline materialisation.
- **Streamline** is a visual projection over generation-stamped persisted cache
  rows. A ribbon or siphon is not causal proof.
- **Pol.is** remains a sidecar deliberation engine. It owns atomic statements,
  agree/disagree/pass votes, participant-by-statement matrices, clusters, and
  bridge statistics. It does not use semantic NLP to determine consensus.
  ITIR maps imported results to ontology nodes only after deliberation.

## Identity spine

`ActorIdentity` contains only a stable identifier, actor kind, and display name.
Person, organisation, institution, address, contact, alias, and merge data live
in separate typed rows with distinct provenance and merge semantics. A CRM may
supply selected fields through `CRMConnectorMapping`; it is never canonical
identity authority.

## Dataflow

1. TiRCorder emits capture/transcript packets.
2. SensiBlaw builds documents, sentences, tokens, phrases, utterances, actors,
   and polymorphic events.
3. Human-reviewed semantic layers add versioned claims, harms, evidence,
   protected interests, value frames, and legal candidates.
4. Provisions decompose into rule atoms, conditions, exceptions, and wrong
   element requirements.
5. Immutable finance postings reconcile into separately confidence-bearing
   transfer inferences.
6. Canonical relational rows project into typed temporal graph rows.
7. Expensive joins materialise into generation-stamped Streamline cache rows.
8. Corrections remain append-only and exports may be sealed into tamper-evident
   receipt packs.
9. External ontologies are advisory concept references, never normative or
   legal authority.
10. Pol.is outputs are empirical community observations, never moral, factual,
    causal, or legal truth.

## Agda modules

- `DASHI.Interop.ITIRActorIdentitySpine`
- `DASHI.Interop.TiRCorderSensiBlawConnectorBoundary`
- `DASHI.Interop.PolisITIRDeliberationBoundary`
- `DASHI.Interop.ITIRSensiBlawStreamlineArchitecture`
- `DASHI.Interop.ITIRSensiBlawArchitectureRegression`

These are candidate-only architecture boundaries. They type responsibility,
provenance, and non-promotion invariants; they do not certify the truth of any
recording, transcript, actor resolution, financial inference, legal
classification, community preference, or real-world outcome.

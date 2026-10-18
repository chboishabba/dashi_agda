# Agda : SLR : JMD Lean BIDI Bridge Design

## Purpose

Agda is the golden semantic contract, SLR is the production runtime, and the JMD/Aristotle Lean Wikidata machine is the executable getter/elaborator/tester/prover. The systems exchange typed receipts; none silently inherits another system's authority.

## Golden ownership

Agda owns the meaning of the shared interfaces:

- world observation and getter parity;
- source/revision/digest identity;
- Lean encoding/import/freshness/elaboration/kernel/report status;
- same-object/relation attachment;
- SLR -> Lean challenge and Lean challenge resolution;
- observed world delta and frontier recomputation boundary;
- attribution and non-promotion firewalls.

SLR may implement its own getter so long as it inhabits the same observation contract. JMD Lean may fetch, encode, elaborate, typecheck, prove, query and render reports, but kernel success does not create external-world truth, legal authority, P7 admission, or residual payment.

## Attribution

All JMD/Aristotle claims in this tranche are source-bounded to the uploaded archive already pinned by `DASHI.Wikimedia.AristotleNativeModelSourceExact`:

- archive: `ae06ae06-2580-422a-8fc3-92aeaaca8762-aristotle (2).tar.gz`
- SHA-256: `924400c414d9d7e3d416bded3a016a891e348ab3177d9d1552be669f1a72e455`
- inspected source role: methodology / executable-model donor, not live Wikidata authority;
- DOI: none supplied by the archive; do not invent one.

The bridge must reuse `DASHI.Core.AttributedSourceCore`; citation/source identity imports neither proof nor authority. The archive source proposition, DASHI reconstruction, runtime parity receipt, and downstream authority remain distinct.

## Data model

A canonical world observation retains request, object, relation/property, source/provider, source revision, content digest, observed value, retrieval status, freshness status, and provenance class. Lean-getter and SLR-getter observations project into that common carrier.

A Lean verification receipt retains the observed object/relation/source coordinates plus independent statuses for encoding, freshness, import, elaboration/typecheck, kernel check, same-object/relation alignment, and report generation. Statuses must not be flattened into a single verified Boolean.

A same-object/relation attachment receipt relates a Lean verification receipt to an external P7 candidate without equating representation identity with world-object identity. Exact same object, same object/different representation, related object, wrong type, ambiguous, and unresolved remain distinct.

A challenge from SLR to Lean is candidate-only and may represent a counterexample candidate, same-object challenge, freshness challenge, type mismatch, premise challenge, or relation-alignment challenge. Lean returns a resolution such as reproduced, not reproduced, statement too strong/weak, wrong type/object, stale import, encoding defect, premise mismatch, or unresolved. A counterexample candidate is not a formal refutation.

## BIDI recurrence

The production recurrence is:

`ProofFrontier -> ExpansionCandidate -> reviewed admission -> WorldObservation -> optional LeanVerification/Challenge -> observed WorldDelta -> posterior ProofFrontier`.

Predicted residual contraction is a scheduling estimate and is not observed contraction. Source/history growth is append-only, while current conclusions and applicability may reopen when source revisions change.

## P7 external-object accounting

Normal P7 external candidates remain acquired/reviewable external objects. Lean verification receipts annotate/check them and do not count as new external-world objects merely because a theorem/query exists. Representation strings do not define novelty; same-object identity classes must be kept separate from QID/article/provider identifiers.

## Required firewalls

- retrieved != imported != derived theorem;
- imported faithfully != world true;
- kernel passed != fresh;
- fresh != typechecked;
- generated report != kernel passed;
- same representation != same world object;
- same world object != same relation;
- Lean verification receipt != ExpansionCandidate;
- counterexample candidate != formal refutation;
- runtime admission != claim truth;
- runtime/Lean receipt != Agda proof;
- source citation != proof or authority;
- predicted contraction != observed contraction;
- derivational novelty != external-world novelty.

## Reuse constraints

Reuse rather than replace:

- `AttributedSourceCore` for attribution;
- `AristotleNativeModelSourceExact` for the uploaded JMD/Aristotle source pin;
- `SLRWikimediaHandoffABIExact` for SLR ownership/non-promotion boundaries;
- `MaboResidualDrivenProducerAdaptersExact` / P7d owners for world-expansion parity;
- SensibLaw `ProofFrontier`, parsed reasoning delta, immutable source revision, append-only world, and research-compounding owners for P7d.2/P7d.3 semantics.

No new planner or parallel evidence ontology is introduced.
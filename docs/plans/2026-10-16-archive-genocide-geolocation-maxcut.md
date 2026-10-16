# Archive Genocide geolocation × DASHI max-cut receipt

Date: 2026-10-16
Branch: `codex/archive-genocide-geolocation-maxcut`
Base: `master`

## Goal

Formalise the useful epistemic shape exposed by Archive Genocide's public geolocation/node-map methodology without importing unsupported factual claims or operational targeting capability.

The intended same-object weld is:

`evidence state -> coarse/fine observation -> consumer sufficiency -> minimum sufficient disclosure -> provenance/review/origin preservation -> anti-targeting authority boundary`.

The implementation deliberately contains no coordinate solver, identity-resolution algorithm, target-selection rule, live-tracking path, or weapon-employment mechanism.

## Existing owners reused

- `DASHI.Core.ConsumerDescentMinimalObserverExact`
  - `FactorsThrough`
  - `ConsumerSufficient`
  - `LeastSufficientConsumerObserver`
  - `ConsumerNonDescentWitness`
- `DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact`
  - canonical anti-panopticon boundary
  - observation is not intervention authority
- `DASHI.Core.AttributedSourceCore`
  - public-source attribution without theorem/authority promotion

This avoids introducing a duplicate `JCoarse/JFine` or anti-panopticon ontology.

## New owners

### `ArchiveGenocideGeolocationAntiTargetingExact.agda`

Provides:

- explicit location precision, review state, event-time basis, geolocation origin, subject-protection, and temporal coordinates;
- a literal coarse/fine witness where two distinct fine states agree after coarse projection;
- `ConsumerNonDescentWitness` showing coarse location cannot satisfy an identity/fine-state consumer;
- canonical least-sufficient coarse consumer witness;
- indexed `EvidenceConsumer` with no operational-targeting constructor;
- protected-person precision firewall;
- near-real-time disclosure firewall;
- `SafeDisclosureReceipt` requiring review completion, safe temporal class, safe protected-subject precision, provenance retention, conflict visibility, and non-reattribution of third-party origin;
- attribution/promotion firewalls;
- terminal boundary receipt.

### `ArchiveGenocideGeolocationPrecisionDisclosureExact.agda`

Provides:

- explicit `PrecisionRefines` relation from town/city through neighbourhood and building to exact coordinate;
- transitivity of refinement;
- `DisclosureView` for minimised presentation;
- proofs that provenance, origin, review state, event-time basis, and corroboration reference survive minimum disclosure;
- witnesses that review status does not determine location precision;
- witnesses that review status does not collapse third-party geolocation into archive authorship;
- terminal precision/disclosure boundary.

### `ArchiveGenocideGeolocationAntiTargetingValidation.agda`

Replays the critical theorems independently, including:

- rival fine-state coarse agreement;
- rival fine-state distinctness;
- coarse-consumer sufficiency;
- fine-consumer non-descent;
- targeting-consumer impossibility;
- protected near-real-time exact-release impossibility;
- precision transitivity;
- review/precision independence;
- third-party credit separation;
- provenance preservation under minimum disclosure.

## Attribution boundary

Archive Genocide is cited only for the public methodology inspected on 2026-10-16. DASHI owns all dependent-type constructions, consumer-descent interpretations, precision-order definitions, minimum-observer statements, and anti-targeting theorems.

Public reference surfaces:

- https://archivegenocide.com/geolocation
- https://archivegenocide.com/nodes/

No claim is made that Archive Genocide endorses, authored, or proved the DASHI formalisation.

## VILYA / anti-panopticon cross-pollination

The current `master` exposes the God’s-Eye proof-carrying world ontology as the stable same-object anti-panopticon seam. Recent VILYA material is associated with the long-lived `agent/epstein-psychedelic-network-maxcut-20261012` line and PR #1190's unusual merge-forward topology rather than a stable master import.

Therefore this branch anchors to the shared God’s-Eye owner and remains mergeable on current `master`; it does not create a hidden cross-branch dependency. A future VILYA promotion can import this module or provide an additional anchor after the VILYA owner is stable on the target base.

## Remaining physical/external boundary

The formalisation proves structure and release constraints; it does not independently verify every geolocation in the external archive, establish legal admissibility in a particular jurisdiction, or certify the archive's operational security. Those remain external evidence/governance questions rather than holes in the dependent-type kernel.

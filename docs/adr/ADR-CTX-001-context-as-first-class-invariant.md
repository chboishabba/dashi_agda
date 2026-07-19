# ADR-CTX-001: Context as a First-Class Invariant

- Status: Proposed
- Date: 2026-07-19
- Scope: ITIR, SB/StatiBaker, SensibLaw projections, clinical and advocate handoffs, affidavit generation, journalism, and public administration

## Context

The originating use case is a protected subject whose experience may be fragmented, approximate, disputed, non-linear, or presently unsafe to recall. Systems that demand a complete timeline or a single coherent narrative can overwrite ambiguity, convert uncertainty into false precision, and reproduce institutional harm.

The same failure appears at public scale. Recorded conversations are clipped into new audiences; comedy is presented as literal policy; public commitments are separated from jurisdiction, attempts, blockers, and delivery evidence; and private identity is flattened into a public role.

## Decision

Context is part of the formal carrier rather than optional metadata.

A renderable artifact is a `ContextBoundArtifact`, containing both a canonical artifact and a `ContextEnvelope`. A derived account is a `NarrativeProjection`, which must be explicitly requested, non-canonical, context-retaining, purpose-scoped, and accompanied by a declared loss profile.

The system preserves these separations:

1. canonical artifact versus projection;
2. what was known then versus what became known later;
3. observed, reported, inferred, and unknown claims;
4. personal, clinical, advocate, journalistic, and administrative audiences;
5. direct authority, coalition-dependent authority, obstruction, attempt, and outcome;
6. macro commitments and small promises that accumulate or erode trust.

## Invariants

- No context-free rendering.
- No automatic narrative authority.
- No diagnosis authority from the record.
- No automatic legal characterisation.
- No forced exposure or graphic retelling.
- Ambiguity and incomplete chronology remain valid terminal states.
- Later facts do not overwrite the contemporaneous epistemic state.
- Role access is consented, minimum-necessary, purpose-limited, logged, scoped, and revocable.
- Exports retain context references and disclose compression loss.
- A public clip is not the whole person.
- Failure is not automatically moralised; attempt, authority, and evidenced obstruction remain visible.

## Formal modules

- `DASHI.Context.ContextEnvelopeInvariant`
- `DASHI.Context.NarrativeProjectionBoundary`
- `DASHI.Context.RoleScopedAccessContract`
- `DASHI.Context.TraumaSafeAffidavitBoundary`
- `DASHI.Context.PublicPowerContextBridge`
- `DASHI.Context.ContextInvariantTests`
- `DASHI.Context.All`

## User-story traceability

### Protected subject

A user may record an empty or partial fragment with approximate or unknown time, preserve contradictory accounts, seal detail, and stop without interpretation or closure.

### Clinician

A clinician receives only the minimum care-planning view, cannot infer diagnosis from the record, cannot force exposure, and cannot export a legal bundle by default.

### Advocate

An advocate receives chronology and evidence views, while clinical notes remain hidden by default. Legal conclusions must be user-authored or explicitly approved, and chronology may remain approximate.

### Affidavit preparation

Each clause retains its source and context reference, distinguishes observed/reported/inferred/unknown status, allows sealed annexes, preserves uncertainty, and does not require graphic retelling.

### Journalist or comedian

A reused excerpt retains original venue, audience, capture conditions, and any comedic frame. The excerpt remains explicitly non-canonical and cannot stand for the whole person or full conversation.

### Mayor or public team

Promises are represented with authority mode, delivery state, evidence, blockers, and trust scale. Direct powers and coalition-dependent work are not conflated. Small unresolved promises remain visible because micro-delivery supports or erodes confidence in macro programmes.

## Consequences

The stack will be slower and less compatible with context-free viral sharing. That cost is accepted. Context expansion should be easy; context removal should be explicit, logged, and loss-declaring.

## Non-goals

This formal lane does not diagnose, determine credibility, establish guilt, infer motive, resolve contradictory memories, or provide a canonical political or therapeutic narrative.

# Sparse Fibred Frontier Formalisation

## Runtime correspondence

This note started with SensibLaw migrations 062 and 063. The active delta-native refinement now includes migrations 202 through 209. The formal owner remains:

```text
DASHI.Cognition.PNF.SparseFibredFrontier
```

The runtime and proof share the following contract:

```text
closed child graph
-> admitted sparse boundary
-> constrained parent reconciliation
-> root-only searchable projection
```

## Closed-interior exclusion

`OutsideObservation` is indexed by `BoundaryAdmission`. Constructors exist only
for `admittedBoundary` and the four supported boundary carriers:

- promoted exports;
- actor/action summaries;
- unresolved demands; and
- explicit scopes or definitions.

There is no constructor for `rejectedInterior`. Therefore:

```text
closedInteriorCannotEscape :
  OutsideObservation rejectedInterior carrier -> bottom
```

This states the central fibre invariant without claiming that child evidence is
deleted. `ClosedFibreBoundary` separately retains `ChildEvidenceState`.

## Typed holes and compressed actors

`TypedBoundaryDemand` records the demand identity and numeric constraints for:

- target kind;
- object kind;
- role;
- factor type;
- predicate;
- residual class; and
- scope class.

`ActorActionSummary` records an abstract actor's kind, role, factor
participation, predicate and occurrence interval. `Compatibility` requires
witnessed equality of the demanded relational dimensions and the summary.

`WitnessedActorBinding` then carries:

- a compatibility witness;
- a concrete `ResolvedTarget`; and
- equality between the resolved identity and the summary actor identity.

The parent therefore answers a narrow typed question. It does not receive a
proof object authorising unrestricted search over the document interior.

## Multiplicity-preserving resolution

`FrontierOutcome` is indexed by `WitnessMultiplicity`:

```text
noWitness          -> noLocalWitness
oneWitness         -> resolvedUniqueWitness target
severalWitnesses   -> ambiguousWitnesses
```

Only the `oneWitness` constructor carries a `ResolvedTarget`.

The following impossibility witnesses are explicit:

- `noWitnessCannotClaimUniqueResolution`
- `severalWitnessesCannotClaimUniqueResolution`

At the root:

- no witness maps to `deferredWorldDemand`;
- one witness maps to `resolvedDemand`; and
- several witnesses remain `openDemand`.

## Root-only lookup authority

`GlobalLookupPermission` has exactly one constructor:

```text
documentFrontierMayIndex :
  GlobalLookupPermission closedDocumentFrontier
```

There is no permission constructor for `closedInteriorAuthority`, giving:

```text
closedInteriorCannotEnterGlobalLookup :
  GlobalLookupPermission closedInteriorAuthority -> bottom
```

This matches the runtime change from all-closed-interface global lookup to a
projection of the closed document frontier only.

## Reduction certificate

`SparseFrontierCertificate` records:

```text
parentFrontierCount <= childBoundaryCount
rootLookupCount <= parentFrontierCount
```

These inequalities describe the admitted boundary and lookup projection. They
do not bound the retained immutable provenance stored inside child fibres.

## Aggregate check

The module is publicly imported by:

```text
DASHI.Cognition.PNF.NumericPNFHyperfabricEverything
```

and is included in the focused Agda 2.9 workflow. No successful typecheck is
claimed until that workflow result is observed.


## Relation-delta owner routing

The active parent candidate path has one mutation owner.

The runtime route is:

- affected parent demand keys;
- one desired candidate relation;
- one current candidate relation;
- exact add, remove, replace, and unchanged partitions;
- one reconciliation receipt;
- no private delete and reinsert path.

The formal owner is `DASHI.Cognition.PNF.RelationDeltaReconciliationExact`.

`RelationDeltaOwnerRouting` requires one candidate mutation owner, zero private bypasses, one hot-path reconciler owner, and one matching receipt owner.

`RelationDeltaAuthorityBoundary` composes that routing law with `AuthorityNonPromotionCore`. Runtime execution evidence therefore remains non-authoritative.

The runtime witness is SensibLaw migration 209. It routes `reduce_numeric_pnf_parent_frontier_affected` through `reconcile_numeric_pnf_parent_candidates`. Migration 208 remains the document-level compatibility reconciler.

## ZKP O/R/C/S/L/P/G/F frame

The canonical frame reuses `DASHI.Interop.IntrospectiveProofLoopExact.ZKPFrame`.

- O: SensibLaw strict numeric PNF candidate reconciliation.
- R: route active candidate membership mutation through one desired/current reconciler.
- C: migration 209 plus the relation-delta and affected-boundary formal owners.
- S: affected parent demand keys, current candidate fibre, desired candidate fibre, reconciliation receipt.
- L: exact relation-delta partition plus sparse affected-key lattice.
- P: one mutation owner; retain unchanged rows; emit only real relation deltas.
- G: preserve semantic authority with zero private bypass and zero manufactured unchanged transitions.
- F: duplicate owners + private bypasses + unchanged rewrites + missing hot-path reconciliation receipts.

## Preconditions

- The child boundary is closed and sparse.
- Affected demand keys are explicit.
- Desired and current candidate rows share one stable semantic key.
- Candidate execution payload equality is exact for the declared fields.

## Invariants

- Unchanged keyed rows cause zero physical candidate writes.
- Reconsideration is not a semantic transition.
- A private candidate mutation path is forbidden.
- Diagnostic and reconciliation receipts do not gain runtime, theorem, legal, or empirical authority.
- Parent work does not reopen rejected child interior state.

## Postconditions

- The active parent candidate phase delegates to one relation-delta owner.
- The owner emits only add, remove, and replacement transitions.
- Unchanged rows stay physically untouched.
- The resulting candidate relation is the desired relation for the affected demand fibre.
- Publication beyond the parent follows the existing change-sensitive delta and fixed-point laws.

## C4 execution view

The C4 boundary is simple: the strict numeric compiler is the system, the affected parent reducer is the container-level owner, the relation reconciler is the component-level candidate mutation owner, and PostgreSQL is the durable authority boundary.

A PlantUML rendering should preserve this direction:

- parser and local solver emit typed deltas;
- affected-key transport selects parent fibres;
- the parent reducer calls the one candidate reconciler;
- the reconciler writes durable candidate state and non-authoritative receipts;
- changed parent boundary values alone propagate upward.

The diagram must not show PostgreSQL as the mandatory sentence-local execution bus.

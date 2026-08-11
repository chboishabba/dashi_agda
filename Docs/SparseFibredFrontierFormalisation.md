# Sparse Fibred Frontier Formalisation

## Runtime correspondence

This note corresponds to SensibLaw migrations 062 and 063 and the module:

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

# Sparse Frontier Constraint Formalisation

## Runtime correspondence

This note corresponds to SensibLaw migrations 066 and 067 and the module:

```text
DASHI.Cognition.PNF.SparseFrontierConstraints
```

The runtime first creates a bounded candidate relation from a compressed parent
frontier. It then evaluates typed positive and negative constraints over only
those candidates. The formalisation excludes global document inventory as an
authorised carrier for this operation.

## Typed constraints

`TypedFrontierConstraint` records:

- constraint kind;
- two numeric key dimensions; and
- polarity (`requirePresent` or `forbidPresent`).

The formal constraint kinds correspond to the executable target properties:

- factor type;
- object kind;
- canonical lexical identity or predicate;
- actor/factor role;
- definition key; and
- scope key.

Residual class remains part of demand strategy. It is deliberately not
formalised as a property the target candidate must possess.

## Actor profile families

A single actor identity may have several compressed summaries corresponding to
different actions or roles. `ActorProfileFamily` records the actor and profile
count. `ConstraintEvidence` selects a bounded profile ordinal from that family.

This permits a conjunction such as:

```text
actor kind = person
role = addressee
participates in notice
predicate = must respond
```

to be witnessed across the actor's compressed profile family without reopening
any child proposition graph.

## Conjunction and negation

`ConstraintVerdict` has two constructors:

- `requiredWitness` carries evidence for a required-positive constraint;
- `forbiddenAbsence` carries a proof that forbidden evidence cannot be
  produced.

`SatisfiesConstraintChain` is inductive conjunction: every constraint in the
chain must receive a verdict before a candidate is admitted.

## Bounded filtering authority

`ConstraintFilteringPermission` has exactly one constructor:

```text
filterBoundedFrontierCandidates :
  ConstraintFilteringPermission boundedFrontierCandidates
```

There is no constructor for `globalDocumentInventory`, giving:

```text
globalInventoryCannotFilterTypedHole :
  ConstraintFilteringPermission globalDocumentInventory -> bottom
```

`BoundedCandidateSet` additionally carries the executable cost witness:

```text
candidateCount <= candidateLimit
```

An `AdmittedConstrainedCandidate` therefore contains both:

- permission to filter the bounded frontier relation; and
- evidence that the actor profile family satisfies the complete constraint
  chain.

## Aggregate check

The module is publicly imported by:

```text
DASHI.Cognition.PNF.NumericPNFHyperfabricEverything
```

and is included in the focused Agda 2.9 workflow. No successful typecheck is
claimed until that workflow result is observed.

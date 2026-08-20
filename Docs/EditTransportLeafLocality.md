# Edit-transport leaf locality

This note records the Agda reference introduced after the SensibLaw small-edit audit correctly returned `indeterminate` for a fixture with many non-unique source anchors.

The runtime lesson is that a lexical/content anchor is not an occurrence identity. A source edit can move an unchanged occurrence, and repeated text can create several leaves with the same local anchor. The formal reference therefore separates:

1. **edit transport** of source coordinates;
2. **provenance-bearing occurrence identity**;
3. **semantic value** carried by the occurrence;
4. **reverse-dependency closure** predicted from the edited source atoms.

The core module is:

`DASHI/Cognition/PNF/EditTransportLeafLocalityExact.agda`

## Transported occurrence identity

An `OccurrenceSignature` contains numeric coordinates for:

- leaf family;
- source occurrence;
- ordered source-support occurrences;
- structural position;
- provenance path.

`TransportedOccurrenceMatch` requires the source coordinate and every support coordinate to be carried through an `EditTransport`, while structural/provenance coordinates remain equal.

The semantic value is deliberately outside the occurrence signature. Therefore matching does not assume semantic equality before testing whether a leaf changed.

## Unique correspondence is evidence

`UniqueMatch` requires one target occurrence plus a proof that every other matching target is equal to it. `VerifiedLeafCorrespondence` requires that evidence for every eligible source leaf.

`ambiguityRefutesVerifiedCorrespondence` proves that two distinct matching targets contradict a verified correspondence certificate. This is the formal fail-closed boundary corresponding to runtime `indeterminate`: an audit may not choose between structurally indistinguishable leaves merely to establish locality.

## Dependency-closure soundness versus precision

For edited source atoms and their reverse-dependency reachability relation:

- `ClosureSound` means every actually changed leaf belongs to the predicted dependency closure;
- `ClosureExact` means every predicted leaf actually changes.

`ExactClosureLocality` contains both directions, and `exactClosureImpliesSound` forgets precision safely.

The distinction matters operationally. A conservative reverse-dependency graph can be semantically sound while reopening far more work than necessary. Thus a successful locality theorem does not, by itself, establish an efficient/minimal frontier.

## Full locality certificate

`VerifiedEditLocality` requires both:

- unique transported leaf correspondence;
- changed-leaf inclusion in the edited reverse-dependency closure.

It exposes two independent falsifiers:

- an ambiguous transported match refutes verified correspondence;
- one changed leaf outside the predicted closure refutes locality soundness.

The regression module

`DASHI/Cognition/PNF/EditTransportLeafLocalityRegression.agda`

contains two finite witnesses:

1. the same transported occurrence can carry a different semantic value, demonstrating that identity and value are not conflated;
2. a sound closure can include an unchanged extra node, demonstrating that locality soundness does not imply closure precision.

No external mathematical source is asserted for this exact construction. It is an internal ITIR/PNF formalization extracted from the runtime audit and the existing provenance/reopenability architecture.

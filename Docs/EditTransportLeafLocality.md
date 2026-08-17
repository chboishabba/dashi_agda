# Edit-transport leaf locality

This note records the Agda reference introduced after the SensibLaw small-edit audit correctly returned `indeterminate` for a fixture with many non-unique source anchors.

The runtime lesson is that a lexical/content anchor is not an occurrence identity. A source edit can move an unchanged occurrence, and repeated text can create several leaves with the same local anchor. The formal reference therefore separates edit transport, provenance-bearing occurrence identity, semantic value, and reverse-dependency closure.

The core module is `DASHI/Cognition/PNF/EditTransportLeafLocalityExact.agda`.

`OccurrenceSignature` contains numeric leaf-family, source occurrence, ordered support occurrence, structural-position and provenance-path coordinates. `TransportedOccurrenceMatch` carries source/support coordinates through an `EditTransport` while preserving the structural/provenance coordinates. Semantic value is deliberately outside the occurrence signature, so matching does not assume semantic equality before testing change.

This is an audit projection rather than a second token authority. `NumericOccurrenceFibre` remains the existing token-occurrence carrier; the locality module supplies the generic extra coordinates needed to compare parser/object/factor/residual/export/proof leaves.

`UniqueMatch` requires one target plus a proof that every other matching target is equal to it. `ambiguityRefutesVerifiedCorrespondence` proves that two distinct matching targets contradict a verified correspondence certificate. Runtime ambiguity must therefore remain indeterminate rather than being resolved by lexical/content similarity alone.

For reverse dependencies, `ClosureSound` means every actually changed leaf is inside the predicted closure. `ClosureExact` means every predicted leaf actually changes. These are deliberately distinct: a conservative dependency graph can be semantically sound while reopening unnecessary work.

`VerifiedEditLocality` requires both unique transported correspondence and changed-leaf inclusion in the reverse-dependency closure. One ambiguous match or one changed leaf outside that closure is a direct falsifier.

`DASHI/Cognition/PNF/EditTransportCompositionExact.agda` adds the revision-lineage algebra needed by long-lived documents and chats. Edit transports have an identity, compose coordinatewise, satisfy left/right identity and associativity pointwise, and therefore support a version chain

```text
v0 -> v1 -> ... -> vn
```

without requiring a new global `v0 <-> vn` matching problem after every revision. The same module proves dependency-closure monotonicity under enlarged edit sets / reachability: adding edited source atoms cannot make an already predicted affected leaf disappear when the reverse-dependency relation is fixed or enlarged.

`DASHI/Cognition/PNF/DependencyDerivedOccurrenceIdentityExact.agda` covers source-free leaves such as exports and proofs. Their occurrence identity is the producer family/slot together with the ordered occurrence identities of their dependencies. The produced semantic value is a separate field and is not a correspondence premise. The module also proves transitivity of this dependency-derived match across a revision lineage.

This matches the runtime rule now used by the numeric leaf audit: producer-authored trigger/target/evidence occurrence provenance establishes residual identity; exports and proofs then inherit correspondence from uniquely paired dependencies plus stable producer structure. Post-resolution target/state, ranks/scores, selected identity entities and final semantic digests remain value rather than occurrence identity.

`DASHI/Cognition/PNF/EditTransportLeafLocalityRegression.agda` contains finite witnesses that the same transported occurrence may carry a changed semantic value and that sound closure locality does not imply precision/minimality.

No external mathematical source or DOI is asserted for this exact construction. It is an internal ITIR/PNF formalization extracted from the runtime audit and existing provenance/reopenability architecture.
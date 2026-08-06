# Round Five attached formalism

The four supplied attachments are integrated as a finite exact theorem layer rather than copied as unchecked declarations.

## History, orientation, weights, and observer access

```text
FiniteHistoryOrientationExact.agda
HistoryWeightFiltrationExact.agda
```

These modules separate:

```text
history index from physical time;
internal conjugation from reversal of a complete history;
filtering from future-boundary smoothing;
Gibbs weights from quantum phases and MDL priors;
future-conditioned hidden histories from past-accessible signalling;
entropy from description length.
```

The finite action is invariant under the declared reversal, the reversal is involutive, and the canonical future-boundary choices leave the past-accessible record unchanged.

## Formal evidence hierarchy

`FormalReceiptBoundaryExact.agda` distinguishes:

```text
mathematical intention;
formal source;
kernel-checked theorem;
reproducible receipt.
```

It also proves the declared four-stage automaton has period four and gives a total finite threshold classifier. Neither result is promoted to a paraconsistent logic or physical overflow theory.

## Ternary kernel and quotient dynamics

```text
FiniteWeightedTernaryKernelExact.agda
TernaryKernelQuotientLyapunovExact.agda
```

The first module proves one symmetry-compatible finite kernel commutes with coordinate exchange and sign involution, while explicit asymmetric weights and a fixed bias supply counterexamples to automatic equivariance.

The second defines an exact kernel on the five global-inversion orbits of the existing nine-sheet carrier. It proves quotient descent by construction, exhibits a nontrivial period-two kernel, and separately proves that a ranked kernel reaches the zero orbit in at most two steps.

Thus:

```text
finite state space -> eventual periodicity;
strict finite rank -> fixed-class convergence.
```

Fixed-point status and MDL optimality remain distinct predicates.

## Statistical filtration and Reeb analogue

```text
FiniteStatisticalFiltrationExact.agda
ProbabilityDecoratedReebExact.agda
```

Physical states, probability laws, and model parameters are distinct types. A finite statistical distance, non-injective coarse projection, and persistent-feature interval are checked explicitly.

The Reeb analogue contains one split and one merge. It proves conservation of denominator-six mass and current, types semantic transition labels independently of topology, requires explicit embeddings before calling the merge preserving, and compares shallow versus split/merge models by two-part description length.

The model is deliberately called a finite probability-decorated Reeb analogue. It is not promoted to the Reeb graph of an unspecified manifold, a quantum amplitude, or a universal 3-6-9 transition law.

## Sources

`AttachedFormalismSourceAtlas.agda` records author, title, venue, year, DOI or explicit no-DOI marker, imported role, and excluded promotion for six sources covering causality, information theory, Reeb quotients, persistent topology, cobordism, and algorithmic statistics.

## Validation

The modules are scanned for holes, postulates, unsafe options, and placeholders, then included in:

```text
DASHI/Physics/Foundations/Round5AttachedFormalismRegression.agda
DASHI/Physics/Foundations/Round5FullBoundary.agda
DASHI/Physics/Foundations/Everything.agda
DASHI/Unified/Everything.agda.
```

A formal source becomes a proof receipt only after the pinned Agda workflow succeeds.

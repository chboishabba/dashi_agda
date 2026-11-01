# Round Five attached formalism

The four supplied attachments are integrated as finite exact theorem layers rather than copied as unchecked declarations. The implementation follows the attachments' corrections: objects that require continuum, probabilistic, causal, or proof-assistant authority remain explicit obligations instead of being silently identified with finite tables.

## History, orientation, weights, and observer access

```text
FiniteHistoryOrientationExact.agda
HistoryWeightFiltrationExact.agda
FiniteHistoryFunctionalExact.agda
```

These modules separate:

```text
history index from physical time;
internal conjugation from reversal of a complete history;
charge conjugation from temporal reversal;
filtering from future-boundary smoothing;
Gibbs weights from quantum phases and MDL priors;
phase labels from observed probabilities;
future-conditioned hidden histories from past-accessible signalling;
entropy from description length.
```

The finite reversal is involutive and preserves the declared transition action. A second module treats admissible histories as primitive, includes two histories sharing one initial state, supplies one reversible deterministic subsystem, makes action a functional of the complete history, checks a finite stationary candidate, and implements two-boundary pruning without promoting it to controllable retrocausal signalling.

## Formal evidence hierarchy

`FormalReceiptBoundaryExact.agda` distinguishes:

```text
mathematical intention;
formal source;
kernel-checked theorem;
reproducible receipt.
```

It also proves the declared four-stage automaton has period four and gives a total finite threshold classifier. Neither result is promoted to a paraconsistent logic or physical overflow theory.

## Residue cycles, reachability, and p-adic boundary

`FiniteResidueCycleReachabilityExact.agda` replaces ambiguous `Base6` and `Base9` aliases with explicit finite residue carriers. It proves six- and nine-step cycle return, terminal reachability in two transitions, and the finite identities

```text
1 + 3 + 9 + 27 = 40
2 * 40 + 1 = 81.
```

A separate `PadicCompletionObligation` records the still-missing complete non-Archimedean field, norm, Cauchy, and infinite-limit proofs. Finite partial sums are not called a proof that the geometric series converges in `Q_3`.

## Ternary kernel, quotient dynamics, and multiscale compatibility

```text
FiniteWeightedTernaryKernelExact.agda
TernaryKernelQuotientLyapunovExact.agda
FiniteMultiscaleKernelCompatibilityExact.agda
```

The weighted-kernel module proves one symmetry-compatible finite kernel commutes with coordinate exchange and sign involution, while explicit asymmetric weights and a fixed bias provide counterexamples to automatic equivariance.

The quotient module defines an exact kernel on the five global-inversion orbits of the existing nine-sheet carrier. It proves quotient descent by construction, exhibits a nontrivial period-two kernel, and separately proves that a ranked kernel reaches the zero orbit in at most two steps:

```text
finite state space -> eventual periodicity;
strict finite rank -> fixed-class convergence.
```

The multiscale module supplies an exactly commuting fine/coarse pair, an incompatible pair with explicit nonzero defect, quotient-valued compatibility that preserves orbit labels rather than representatives, and a nontrivial kernel fibre. Fixed-point status, exact compatibility, approximate compatibility, quotient descent, and MDL optimality remain distinct predicates.

## Statistical filtration, Reeb analogue, and ultrametric flow

```text
FiniteStatisticalFiltrationExact.agda
ProbabilityDecoratedReebExact.agda
FiniteUltrametricReebFlowExact.agda
```

Physical states, probability laws, and model parameters are distinct types. A finite statistical distance, non-injective coarse projection, and persistent-feature interval are checked explicitly.

The Reeb analogue contains one split and one merge. It proves conservation of denominator-six mass and current, types semantic transition labels independently of topology, requires explicit embeddings before calling the merge preserving, and compares shallow versus split/merge models by two-part description length.

The ultrametric extension adds depth-two ternary addresses, separates the local chart from the hierarchical address, normalises the declared split transition row, forms finite path weights by products, attaches temporal-thickness labels to transitions, and defines a finite weighted topological current. None of these tables is promoted to smooth spacetime, quantum amplitudes, relativistic proper time, or a universal 3-6-9 law.

## Cumulative boundaries and regressions

```text
Round5AttachedFormalismBoundary.agda
Round5AttachedFormalismRegression.agda
Round5AttachedCompletionBoundary.agda
Round5AttachedCompletionRegression.agda
Round5CompleteBoundary.agda
```

`Round5CompleteBoundary.agda` combines the earlier foundations boundary, the full attached-completion boundary, and the collider boundary into one final typed root.

## Sources

`AttachedFormalismSourceAtlas.agda` records author, title, venue, year, DOI or explicit no-DOI marker, imported role, and excluded promotion for six sources covering causality, information theory, Reeb quotients, persistent topology, cobordism, and algorithmic statistics.

## Validation

The modules are scanned for holes, postulates, unsafe options, unsolved metas, and placeholders, then included in the focused Agda targets:

```text
DASHI/Physics/Foundations/Round5AttachedFormalismRegression.agda
DASHI/Physics/Foundations/Round5AttachedCompletionRegression.agda
DASHI/Physics/Foundations/Round5CompleteBoundary.agda
DASHI/Physics/Foundations/Round5FullBoundary.agda
DASHI/Physics/Foundations/Everything.agda
DASHI/Unified/Everything.agda.
```

A formal source becomes a proof receipt only after the pinned Agda workflow succeeds.

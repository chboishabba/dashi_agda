# Optimisation economy

`DASHI.Cognition.PNF.OptimizationEconomyExact` formalises the optimisation phase
that follows semantic correctness: once two implementations are semantically
comparable, ask whether the computation is expressed through the cheapest
consumer-sufficient representation.

The central separation is:

```text
semantic admissibility/parity
≠ runtime economy
≠ implementation/change economy
```

## Delta projection

`DeltaProjectionExact` states the preferred law directly:

```text
projectDelta (deltaOf history) == projectHistory history
```

The accumulated history carrier is therefore not automatically execution
authority when a finite changed fibre determines the same observation.

`ChildFibreClosureExact` is the hierarchy-specific version:

```text
closeFromChildren (childFibre accumulated)
== closeFromAccumulated accumulated
```

This is the theorem boundary for replacing a growing self-read/group/upsert
parent-close implementation with direct bounded child-fibre composition.

## Amplification

`AmplificationReceipt` records exact natural-number counts:

```text
touchedSemanticRows
historyRowsExamined
attemptedWrites
semanticallyNewWrites
```

`AmplificationBound receipt h w` avoids floating-point ratios and states:

```text
historyRowsExamined <= h * touchedSemanticRows
attemptedWrites     <= w * semanticallyNewWrites
```

The runtime may report the corresponding empirical ratios; Agda retains the
exact cross-multiplied/bounded obligation.

## Runtime and architecture economy

`RuntimeEconomy` contains physical cost coordinates such as wall ticks, semantic
work, memory, I/O, history reads and write attempts.

`ArchitectureEconomy` separately records:

```text
new primitives
new semantic authority surfaces
new execution engines
new persistent schemas
explicit duplicated capabilities
reused generic capabilities
retired compatibility surfaces
```

The formal object deliberately does not make LOC an authority coordinate.

`noveltyBurden` accepts explicit weights and computes a review-oriented burden;
the weights are policy, while the underlying counts remain visible.

## Pareto improvement

`NonWorseningEconomy` requires every runtime and architecture cost coordinate to
be non-increasing while compatibility retirement is non-decreasing.

`StrictImprovement` requires at least one actual improvement. Therefore equality
is not silently promoted to an optimisation.

`ParetoImprovement` combines both conditions.

A faster implementation that creates an additional semantic authority or
execution engine is therefore not automatically a Pareto improvement; it is a
tradeoff until that new degree of freedom is independently justified.

## Semantic parity gate

`SemanticallyComparableOptimization` keeps semantic observation equality outside
the performance vector:

```text
afterObservation source == beforeObservation source
```

`optimizationCannotBuySpeedWithSemanticDrift` merely exposes that field as the
non-negotiable prerequisite.

## Composition-first maturity

`CompositionDominated` states a deliberately modest architectural maturity
signal:

```text
newPrimitives <= reusedCapabilities
```

It is not an LOC theorem. It captures the expectation that mature new features
increasingly compose existing carriers, projections, scheduler/reopening laws and
receipt/persistence surfaces, adding only irreducible domain novelty.

The SensibLaw executable counterpart is
`src/runtime/optimization_economy.py`; its evidence-backed physical antipattern
catalogue is `docs/architecture/PERFORMANCE_SIN_BIN.md`.

# Consumer-indexed relevance, Cantor compression and runtime throughput

## Purpose

This note hardens two boundaries needed before the Agda layer is used as the
specification/oracle for the next SensibLaw/ITIR Python/PostgreSQL sprint:

1. a normalized mass of `1` is **consumer/model-relative relevance accounting**,
   not objective truth or proof that the represented candidate universe is
   complete;
2. semantic correctness is not enough for archive-scale use: post-parser
   execution must be measured and driven low enough that spaCy remains the
   dominant expensive stage without being artificially slowed.

The result is a stronger compression contract:

```text
represented fine carrier
    -> consumer-indexed relevance accounting
    -> bounded active P + reopenable residual Q + outside-model residual
    -> consumer-specific projection
    -> dynamic trace-congruence proof before discarded distinctions may vanish
```

## Three different normalized units

`DASHI.Core.ConsumerIndexedRelevanceMeasure` explicitly distinguishes three
model-level interpretations:

```text
candidateWeightMass
representedProvenanceMass
consumerRelevanceMass
```

A chosen measure has

```text
relevanceMass : Consumer -> Region -> Mass
normalizedWhole : relevanceMass consumer wholeRegion = unitMass
```

The distinguished `unitMass` means only "all mass represented by this chosen
measure on the current epistemic carrier".

It does not mean:

```text
unitMass = objective truth
candidate weights sum to unitMass => candidate universe is complete
current PNF carrier = latent world object
```

Both attempted promotions are constructorless in Agda.

## Open-world accounting and world coverage

The core accounting object retains three regions:

```text
A = retained region
R = represented/model-internal residual
O = outside-model residual / explicit ignorance
```

with an application-supplied accounting receipt of the form

```text
mass_C(A) + mass_C(R) + mass_C(O) = unitMass.
```

The concrete mass algebra is intentionally application supplied.  It may be a
count, fixed-point weight, rational mass, provenance measure or another exact
carrier.  The formal layer does not manufacture a probability interpretation.

This is the preferred PNF reading of normalization.  Even when a runtime says

```text
mass_C(A) = unitMass
```

that remains a statement about the chosen consumer/model.

World completeness is represented separately by:

```text
WorldCoverageSystem
WorldCoverageWitness
```

whose application supplies a relation of the form

```text
Coverage_C(model, world).
```

No normalized relevance measure can construct that witness.  In many PNF uses
there is no available `World` carrier at all, which is exactly why model-relative
normalization must remain epistemically weaker.

## Cantor/refinement reference

`DASHI.Foundations.CantorConsumerRelevanceReference` reuses the existing finite
ternary/polar address construction.

At depth `d`:

```text
ambient ternary cells   = 3^d
surviving polar cells   = 2^d
```

and at depth three the existing repository theorems give exactly:

```text
ambient cells   = 27
surviving cells = 8.
```

The reference consumer assigns unit task mass to the surviving region and zero
task mass to the removed region.  Thus the finite carrier can become much
smaller in ordinary combinatorial volume while retaining all relevance for that
specific query.

This module is deliberately **not** a proof of the limiting Cantor function,
Lebesgue measure zero, Hausdorff dimension or classical Cantor measure.  Its job
is to make the ITIR analogy exact at the finite refinement level without
smuggling in stronger analysis.

The runtime interpretation is:

```text
small ambient carrier != small task relevance
locally inactive       != globally absent
zero task mass for C   != semantic falsity for every consumer
```

## Relevance mass is weaker than dynamic safety

`DASHI.Core.ConsumerProjectionSufficiency` separates:

```text
ConsumerMassCertificate
```

from

```text
DynamicConsumerSafety.
```

The stronger compression certificate contains both.

`DASHI.Cognition.PNF.RelevanceMassDynamicSafetyRegression` then constructs a
literal counterexample using the existing residual terminalisation system:

```text
retained task mass = unitMass
```

while the same projection still has a `TerminalisationDefect`.

Therefore:

```text
mass_C(retained) = 1
    does not imply
consumer-safe quotient.
```

A distinction may have zero current relevance mass and still be causally
relevant to later admissible evolution.  The final permission to forget it is
the dynamic congruence theorem:

```text
project x = project y
and both execute the same admissible trace
=> their future projections remain equal.
```

This is the operational boundary between safe Cantor-like compression and
terminalisation.

## Bounded execution with explicit ignorance

`BoundedExecutionCarrier` keeps its existing closed/two-way `SplitMeasureReceipt`
for callers that genuinely have a closed represented universe.

It now additionally exposes:

```text
ConsumerMeasuredReopenableExecutionPartition
```

which combines:

```text
P = active bounded execution carrier
Q = semantically possible reopenable residual
consumer-indexed relevance measure
open-world mass accounting
```

The intended runtime invariant remains:

```text
LIMIT bounds execution, not semantics.
```

A candidate outside the active beam may be low-weight, inaccessible or currently
irrelevant without becoming refuted.

## Archive-scale throughput constitution

The target workload is not a handful of legal documents.  The architecture must
remain viable for very large personal/corpus archives, including long-lived chat
histories.  That changes the performance standard: every expensive operation
after the NLP parser must justify itself as a tightly bounded/indexed operation.

`DASHI.Cognition.PNF.RuntimeThroughputConstitution` therefore adds empirical
receipts rather than pretending Agda proves PostgreSQL timings.

### Stage receipt and workload identity

Each measured stage records:

```text
workload id
input units
output units
work units
elapsed units
peak-memory units.
```

Before/after parser timings and parser/post-parser timings may only be compared
when their workload identifiers are proved equal.  This blocks a fast small
sample from being compared with a slower large one and called an optimisation.

### Explicit work envelope

A single claimed work-bounded point may supply:

```text
work <= slope * representedCarrier + intercept.
```

The represented carrier is application chosen: tokens, unresolved demands,
bounded candidates, interface rows, or another justified execution carrier.

A single point does **not** prove scaling.  `ArchiveScaleReceipt` therefore
requires a non-empty scaling series and an `AllWithinAffine` witness showing
every observed point lies inside the declared envelope.

This does not magically establish asymptotic complexity; it is the exact
receipt expected from the runtime benchmark series before the implementation
may describe that observed range as fitting the declared work envelope.

### Parser-dominance receipt

A runtime target supplies a minimum dominance factor `k`.  A successful
optimisation receipt proves:

```text
same workload before/after
parser_after <= parser_before
```

for elapsed/work units, so parser dominance was not obtained by making spaCy
slower; and

```text
same workload parser/post-parser
k * post_parser_after <= parser_after.
```

Thus the intended end state is:

```text
spaCy remains the slowest stage
because everything after spaCy is blazing fast.
```

The factor is deliberately not hard-coded in Agda.  Benchmark policy chooses it
and the runtime must earn the receipt.

### Why this matters for lifetime-scale corpora

The practical target is that once a text has paid the relatively expensive NLP
observation cost, the rest of the semantic compiler mostly performs:

```text
integer-key probes
small sparse joins
set-based updates
bounded candidate enumeration
incremental reopening
local fixed-point closure
one ordered publication.
```

Expensive whole-document or whole-corpus recomputation should be recovery/audit
behaviour, not the ordinary response to new evidence.

Pairwise or higher-order work is acceptable only when that execution surface is
explicitly represented or bounded before ranking/materialisation.  A `LIMIT`
after a quadratic join does not satisfy the constitution merely because the
returned row count is small.

Performance receipts have no semantic authority.

## Runtime consequence

The desired hot path is therefore:

```text
spaCy observations
    -> numeric occurrences
    -> PostgreSQL-native cheap narrowing
    -> sparse candidate/evidence fibres
    -> H3 local evidence
    -> H6 only if unresolved
    -> H9 only if unresolved
    -> bounded active P + reopenable Q
    -> proof-relevant admission
    -> parser/argument structural support
    -> factor substitution
    -> one ordered document commit.
```

Once parser output exists, ordinary work should be integer-keyed, set-based,
sparse, bounded before ranking/materialisation, and incremental.  Whole-document
reparsing or whole-corpus rescans should be exceptional recovery operations, not
normal semantic reconsideration.

The combined constitutional target is:

```text
preserve all consumer-relevant distinctions,
retain explicit ignorance,
separate model normalization from world coverage,
prove dynamic safety before forgetting hidden state,
and make every post-parser operation cheap enough to disappear beneath parsing.
```

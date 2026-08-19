# Top-down observation / fibre / residual calculus

This note records the generic theorem spine now exposed by PR #582.  It is a reorganisation of existing DASHI projection, future-language, provenance, hyperfabric and authority machinery plus a small set of missing generic owners.  It is not a new parallel framework and it does not identify ontology, ternary geometry and arithmetic-geometry carriers.

## 1. Problem statement

The top-down problem is:

> Given a fine object observed through context-dependent partial surfaces, what is the least information required by a declared consumer; when may a quotient be used safely; and what residual structure must survive when the consumer does not descend?

For one context the primitive data are

```text
fine state  X
observer    O : X -> Y
consumer    F : X -> Z.
```

The central theorem is the fibre criterion:

```text
F factors through O
        =>
O(x)=O(y) -> F(x)=F(y).
```

For a sectioned projection the converse is constructive as well:

```text
O(x)=O(y) -> F(x)=F(y)
        =>
exists Fbar : Y -> Z, F = Fbar o O.
```

`DASHI.Core.ConsumerDescentMinimalObserverExact` owns this theorem.  It also records the deterministic least-sufficient observer: the consumer map itself is sufficient for that consumer, and every other sufficient observer refines it in DASHI's information order.

This is consumer-indexed deterministic minimality.  It is deliberately not promoted to statistical likelihood sufficiency or world-complete semantics.

Classical calibration:

- David Blackwell, **Equivalent Comparisons of Experiments**, *Annals of Mathematical Statistics* 24(2), 1953, DOI `10.1214/aoms/1177729032`.
- Patrick Cousot and Radhia Cousot, **Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints**, POPL 1977, DOI `10.1145/512950.512973`.
- E. L. Lehmann and George Casella, **Theory of Point Estimation**, 2nd ed., Springer, 1998, DOI `10.1007/b98854`.

The stronger dynamic version was already in the repository: `FutureObservationLanguageQuotientExact`, `MinimalSufficientObservationGovernanceExact`, and `CanonicalFutureMinimalDynamicalRealizationExact` construct the canonical quotient for a declared future action/observation language and prove its factorisation/minimality among the stated sectioned safe representations.

Hence:

```text
static consumer minimality
!=
future-language dynamical minimality.
```

The latter may require distinctions irrelevant to one present consumer.

## 2. Four different optimisation obligations

The top-down calculus keeps four questions distinct.

```text
consumer sufficiency
  Does the declared outcome descend through the surface?

exact reconstruction
  Does the retained code separate/reopen the fine state?

operation locality
  Does the fine operation descend to a surface operation?

representation economy
  How much storage/compute/local mutation does the chosen encoding require?
```

`TopDownObservationCalculusExact` proves exact reconstruction implies adequacy for every consumer, but the converse fails.  Its finite two-bit product witness has a public coordinate that is sufficient for its declared consumer and supports a descended update while still collapsing a hidden coordinate.

So there is no theorem saying one representation is globally optimal for all four objectives.

## 3. Context-indexed observation

`ContextIndexedObservationFibrationExact` places the observer over an existing DASHI `ProjectionCategory` of contexts.

For each context `c` it carries

```text
Fine c
Surface c
observe c : Fine c -> Surface c.
```

A context change has contravariant fine/surface restriction maps.  Identity and composition are explicit laws and observation is natural with respect to restriction.

The chosen restriction presentation supplies canonical split cartesian lifts and a stagewise factorisation equation.  `ContextIndexedObservationFibrationRegression` constructs a literal two-context example in which a public restriction is sufficient for the public consumer but the same surface form is not sufficient for a situated hidden-coordinate consumer.

Source calibration:

- Jean Bénabou, **Fibered Categories and the Foundations of Naive Category Theory**, *Journal of Symbolic Logic* 50(1), 1985, 10--37, DOI `10.2307/2273784`.
- Saunders Mac Lane, **Categories for the Working Mathematician**, 2nd ed., Springer, 1998, DOI `10.1007/978-1-4757-4721-8`.

The current Agda is a strict split indexed presentation.  It does not claim the complete Grothendieck correspondence between fibrations and pseudofunctors, nor that every existing DASHI context carrier already satisfies the required laws.

## 4. Collision fibres and residual symmetry

If `O : X -> Y` is not separating, the next top-down question is not automatically "add another scalar".  Ask what structure acts within

```text
O^-1(y).
```

`ResidualSymmetryCollisionFibreExact` proves that any explicitly supplied invertible symmetry preserving `O` acts internally on every observation fibre.  If a typed residual sector label distinguishes a pair inside one coarse fibre, pairing that sector with the original observer is a strict refinement.

`ResidualSymmetryCollisionFibreRegression` instantiates the theorem on the signed-centre ternary carrier.  The strict antipode acts inside the coarse noncentral pole class; the residual sign distinguishes the two poles.

Representation-theory calibration:

- Jean-Pierre Serre, **Linear Representations of Finite Groups**, Springer, 1977, DOI `10.1007/978-1-4684-9458-7`.

The generic core intentionally stops before a double-centralizer theorem.  A symmetry commuting with an operator family does not, on the present set-level hypotheses alone, construct joint spectral labels, prove semisimplicity, establish `A'' = A`, or yield an isotypic tensor decomposition.  Those are obligations of a richer linear instance.

This is the safe generic theorem shape behind the more specific marked-Hecke/deck examples developed on the arithmetic branches: a coarse observable can have a multiplicity/collision sector on which additional genuine symmetry data acts.  #582 imports the theorem shape, not those Moonshine carriers.

## 5. Exact residuals and the 369 laboratory

When exact reopening is required, `DependentRecoverableProjectionExact` uses a state-dependent residual family

```text
Residual : Y -> Set
```

and an exact code

```text
Sigma (y : Y), Residual y.
```

This is stronger than forcing all strata into one fixed padded residual product.

The balanced-ternary antipodal bridge is the exact finite model:

```text
27 -> 14
centre residual       : singleton
noncentral residual   : direct | counter.
```

Across three 27-state blocks the fine carrier is

```text
27^3 = 3^9 = 19683
```

with blockwise coarse carrier

```text
14^3 = 2744
```

and residual fibre sizes

```text
1, 2, 4, 8
```

by stratum.  Quotient plus dependent residual round-trips exactly.  The quotient alone is not granted reconstruction authority.

`WikidataTernaryFibreRegression` now expresses the original binary/ternary issue in the same top-down language:

```text
positiveOnly(-1) = positiveOnly(0)
```

is a direct non-descent witness for the consumer that needs the signed/neutral coordinate itself, while the exact antipodal quotient-plus-dependent-residual code is sufficient even for fine-state identity.

## 6. Dependent definitions rather than Cartesian overgeneration

`DependentDefinitionFibreExact` is the finite ontology-side example.  A flat

```text
Make x FlatModel
```

constructs combinations that subsequently need Boolean rejection.  The dependent carrier

```text
Sigma (make : Make), Model make
```

contains only compatible children of each selected parent coordinate.  The Toyota/Fiesta flat pair exists and is rejected post hoc; no corresponding dependent section exists.

This is not a claim that all positive definitions are invalid.  It formalises the narrower point that a dependent carrier can encode compatibility in the type itself instead of constructing a Cartesian ambient space and validating afterward.

## 7. Canonical top-down workflow

The current generic calculus is therefore:

```text
1. declare fine carrier, context, observer and consumer;
2. prove descent / fibre constancy if possible;
3. if descent fails, exhibit the collision witness;
4. characterize the collision fibre and any genuine symmetry/residual structure;
5. refine only enough for the declared consumer/future language;
6. retain an exact dependent residual only when reopening is actually required;
7. prove operations commute with the chosen surface when operational locality matters;
8. keep authority/world-completeness as a separate theorem layer.
```

Compactly:

```text
observe
 -> locate collision
 -> characterize fibre
 -> exploit genuine symmetry
 -> retain minimal relevant residual
 -> prove descent.
```

The full aggregate is `DASHI.EverythingTopDownObservationCalculus`.

## 8. Non-promotions

The top-down calculus does **not** prove any of the following merely from a collision/refinement theorem:

```text
mathematical separation = world identity
sector separation = semantic completeness
consumer sufficiency = exact reconstruction
static sufficiency = future-language safety
fibration vocabulary = every context system is a fibration
commuting symmetry = double-centralizer theorem
same finite cardinality = same algebra/action
369 finite geometry = Moonshine theorem
quotient = permission to erase provenance.
```

Those boundaries are intentional.  The point of the top-down reorganisation is to identify the exact obligation at each projection boundary and stop recomputing domain-specific versions of the same theorem shape.

# Top-down observation / fibre / residual calculus

This note records the generic theorem spine now exposed by PR #582. It is a reorganisation of existing DASHI projection, future-language, provenance, hyperfabric and authority machinery plus a small set of missing generic owners. It is not a new parallel framework and it does not identify ontology, ternary geometry and arithmetic-geometry carriers.

## 1. Problem statement and canonical consumer quotient

The top-down problem is:

> Given a fine object observed through context-dependent partial surfaces, what is the least information required by a declared consumer; when may a quotient be used safely; and what residual structure must survive when the consumer does not descend?

For one context the primitive data are

```text
fine state  X
observer    O : X -> Y
consumer    F : X -> Z.
```

The central fibre criterion is

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

`DASHI.Core.ConsumerDescentMinimalObserverExact` owns this theorem.

The stronger static quotient owner is now `DASHI.Core.ConsumerKernelQuotientPresentationExact`. It presents the canonical deterministic equivalence

```text
x ~F y  iff  F(x)=F(y)
```

by a quotient code whose equality is sound and complete for the consumer kernel. Agda does not provide raw quotient types definitionally, so this follows the same presentation discipline as `FutureObservationLanguageQuotientExact`.

The canonical consumer code is sufficient for `F`, and every **sectioned sufficient observer** factors onto it. Thus the top-down least-information statement is now an explicit universal property rather than merely the observation that `F` can itself be used as an observer.

This is deterministic consumer-indexed minimality. It is deliberately not promoted to statistical likelihood sufficiency or world-complete semantics.

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

`TopDownObservationCalculusExact` proves exact reconstruction implies adequacy for every consumer, but the converse fails. Its finite two-bit product witness has a public coordinate that is sufficient for its declared consumer and supports a descended update while still collapsing a hidden coordinate.

The binary/ternary analysis now also has an exact finite result rather than only one-codec evidence. `TernaryNineOptimalBinaryDilationExact` constructs an injective

```text
T^3 -> B^5
```

codec with primitive nearest-transition Hamming dilation at most two. Three blockwise copies give

```text
T^9 = (T^3)^3 -> (B^5)^3 = B^15
```

with exact round trip and the same dilation-two bound.

At the all-neutral `T^9` state there are 18 primitive neighbour directions, whereas a 15-bit word has only 15 one-bit coordinate directions. Finite pigeonhole therefore proves that one-bit centre locality is impossible at 15 bits.

So the correct finite conclusion is:

```text
15-bit exact storage is possible;
15-bit primitive dilation <= 2 is possible;
15-bit one-bit primitive locality is impossible;
18-bit per-trit simulation is not storage minimal;
compact binary does not imply unbounded locality distortion.
```

This deliberately falsifies the stronger earlier conjecture that storage-optimal binary must be severely/unboundedly nonlocal. Representation economy and operational locality are separate objectives.

Graph-embedding calibration:

- Zevi Miller, Dan Pritikin and I. H. Sudborough, **Embedding multidimensional grids into optimal hypercubes**, *Theoretical Computer Science* 552 (2014), DOI `10.1016/j.tcs.2014.07.026`.
- R. Sundara Rajan et al., **Lower bounds for dilation, wirelength, and edge congestion of embedding graphs into hypercubes**, *Journal of Supercomputing* 77 (2021), DOI `10.1007/s11227-020-03420-w`.

## 3. Context-indexed observation and consumer base change

`ContextIndexedObservationFibrationExact` places the observer over an existing DASHI `ProjectionCategory` of contexts.

For each context `c` it carries

```text
Fine c
Surface c
observe c : Fine c -> Surface c.
```

A context change has contravariant fine/surface restriction maps. Identity and composition are explicit laws and observation is natural with respect to restriction.

The chosen restriction presentation constructs canonical split lift arrows, the exact stagewise factorisation equation, and the factor-through-lift arrow for a composite restriction. `ContextIndexedObservationFibrationRegression` constructs a literal two-context example in which a public restriction is sufficient for the public consumer but the same surface form is not sufficient for a situated hidden-coordinate consumer.

`ConsumerQuotientBaseChangeExact` now adds the missing **consumer-minimal transport law**. For

```text
restrict  : FineD -> FineC
consumerD : FineD -> OutcomeD
consumerC : FineC -> OutcomeC
```

the canonical consumer quotient can transport only if

```text
consumerD(x)=consumerD(y)
  ->
consumerC(restrict x)=consumerC(restrict y).
```

Any explicit base-change map implies this fibre compatibility. Conversely, with a section of the source consumer projection, compatibility constructs

```text
OutcomeD -> OutcomeC
```

and the commuting square. Identity and composition are proved. `ConsumerQuotientBaseChangeRegression` gives both a compatible public-coordinate restriction and an incompatible hidden-coordinate restriction.

Thus:

```text
context-local adequacy
!=
automatic natural/base-change transport.
```

Source calibration:

- Jean Bénabou, **Fibered Categories and the Foundations of Naive Category Theory**, *Journal of Symbolic Logic* 50(1), 1985, DOI `10.2307/2273784`.
- Saunders Mac Lane, **Categories for the Working Mathematician**, 2nd ed., Springer, 1998, DOI `10.1007/978-1-4757-4721-8`.

The current Agda is deliberately a strict split indexed/fibration-shaped presentation. It proves the existence/factorisation side of its chosen lifts, but it does **not** claim proof-level uniqueness for arbitrary total arrows, the complete Bénabou cartesian universal property, or the Grothendieck equivalence between fibrations and pseudofunctors.

## 4. Collision fibres and residual symmetry

If `O : X -> Y` is not separating, the next top-down question is not automatically "add another scalar". Ask what structure acts within

```text
O^-1(y).
```

`ResidualSymmetryCollisionFibreExact` proves that any explicitly supplied invertible symmetry preserving `O` acts internally on every observation fibre. A nontrivial observer-preserving symmetry move itself constructs an `ObserverCollision`. If a typed residual sector label distinguishes the pair, pairing that sector with the original observer is a strict refinement.

`ResidualSymmetryCollisionFibreRegression` instantiates the theorem on the signed-centre ternary carrier. The strict antipode acts inside the coarse noncentral pole class; the residual sign distinguishes the two poles.

Representation-theory calibration:

- Jean-Pierre Serre, **Linear Representations of Finite Groups**, Springer, 1977, DOI `10.1007/978-1-4684-9458-7`.

The generic core intentionally stops before a double-centralizer theorem. A symmetry commuting with an operator family does not, on the present set-level hypotheses alone, construct joint spectral labels, prove semisimplicity, establish `A'' = A`, or yield an isotypic tensor decomposition.

## 5. Orbit/stabilizer residuals and exact reopening

When exact reopening is required, `DependentRecoverableProjectionExact` uses a state-dependent residual family

```text
Residual : Y -> Set
```

and an exact code

```text
Sigma (y : Y), Residual y.
```

`OrbitStabilizerResidualPresentationExact` now explains the symmetry case generically. Given an explicitly presented group action and orbit quotient, the residual over one orbit is presented by equality of group elements **after acting on the chosen orbit representative**:

```text
g ~ h  iff  g.rep = h.rep.
```

This is the action-kernel/coset equivalence associated with the stabilizer. A representative group element for each residual code then gives an exact dependent reopening

```text
State ~= Sigma Orbit Residual
```

and the combined orbit-plus-residual code is separating. The module intentionally does not pretend that raw quotient/coset types are definitional Agda objects.

`BalancedTernaryOrbitStabilizerResidualBridgeExact` instantiates this on the `C2` antipodal action of the 27-state ternary cube. The centre has stabilizer `C2` and a singleton residual; every noncentral orbit has trivial stabilizer and a two-state orientation residual. Thus

```text
27 = 1 + 13*2
```

is now explained by isotropy rather than being only a hand-built codec count.

Across three 27-state blocks the existing fine carrier remains

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

by stratum. Quotient plus dependent residual round-trips exactly. The quotient alone is not granted reconstruction authority.

`WikidataTernaryFibreRegression` expresses the original binary/ternary issue in the same top-down language:

```text
positiveOnly(-1) = positiveOnly(0)
```

is a direct non-descent witness for the consumer that needs the signed/neutral coordinate itself, while the exact antipodal quotient-plus-dependent-residual code is sufficient even for fine-state identity.

## 6. Dependent definitions rather than Cartesian overgeneration

`DependentDefinitionFibreExact` is the finite ontology-side example. A flat

```text
Make x FlatModel
```

constructs combinations that subsequently need Boolean rejection. The dependent carrier

```text
Sigma (make : Make), Model make
```

contains only compatible children of each selected parent coordinate. The Toyota/Fiesta flat pair exists and is rejected post hoc; no corresponding dependent section exists.

This is not a claim that all positive definitions are invalid. It formalises the narrower point that a dependent carrier can encode compatibility in the type itself instead of constructing a Cartesian ambient space and validating afterward.

## 7. Canonical top-down workflow

The current generic calculus is therefore:

```text
1. declare fine carrier, context, observer and consumer;
2. construct/use the canonical consumer-kernel quotient when minimality matters;
3. prove descent / fibre constancy if possible;
4. prove base-change compatibility before transporting the quotient across context;
5. if descent fails, exhibit the collision witness;
6. characterize the collision fibre and any genuine symmetry/residual structure;
7. for symmetry quotients, retain stabilizer-indexed residuals when reopening is required;
8. refine only enough for the declared consumer/future language;
9. prove operations commute with the chosen surface when operational locality matters;
10. optimize storage/locality separately and keep authority/world-completeness separate.
```

Compactly:

```text
consumer kernel
 -> minimal quotient
 -> compatible base change
 -> collision/orbit
 -> stabilizer-indexed residual
 -> exact reopening
 -> representation-cost analysis.
```

The full aggregate is `DASHI.EverythingTopDownObservationCalculus`.

## 8. Non-promotions

The top-down calculus does **not** prove any of the following merely from a collision/refinement theorem:

```text
mathematical separation = world identity
sector separation = semantic completeness
consumer sufficiency = exact reconstruction
static sufficiency = future-language safety
context-local adequacy = natural base change
indexed restriction laws = full Bénabou cartesian universality
fibration-shaped vocabulary = every context system is a fibration
commuting symmetry = double-centralizer theorem
orbit quotient = reconstruction without residual
same finite cardinality = same algebra/action
compact binary = necessarily high/unbounded locality distortion
369 finite geometry = Moonshine theorem
quotient = permission to erase provenance.
```

Those boundaries are intentional. The point of the top-down reorganisation is to identify the exact obligation at each projection boundary and stop recomputing domain-specific versions of the same theorem shape.

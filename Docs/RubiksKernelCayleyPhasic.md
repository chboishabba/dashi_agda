# Rubik kernel, Cayley graph, and phasic lift

## Scope

This package formalises the standard 3×3×3 Rubik configuration space as a finite kernel-internal automaton and records its lift through the DASHI M-level hierarchy.

The classical object is unchanged:

- vertices are legal cube states;
- generator edges are legal face turns;
- unit-cost shortest paths are Cayley-graph word geodesics.

DASHI adds explicit carriers, admissibility, higher cells, phasic interpolation, and scalar defect contraction around that classical core.

## State tuple

A legal discrete state consists of:

- a corner permutation;
- an edge permutation;
- eight corner twists in the third roots of unity;
- twelve edge flips in the second roots of unity;
- corner-twist closure;
- edge-flip closure;
- matched corner/edge permutation parity.

The continuous ambient lift replaces permutation vertices by assignment carriers and retains phases as an abstract `PhaseStructure`. No floating-point complex-number semantics are assumed by the Agda core.

## M hierarchy

- **M3**: local slot, identity mass, and phase.
- **M6**: pairwise assignment overlap and relative transport.
- **M9**: a closed four-edge boundary carrying holonomy and its contracted scalar defect.
- **M(3k)**: arbitrary finite-rank lifts, represented by `FiniteRankLift`; there is no formal rank ceiling.

The hierarchy therefore generalises finite puzzles and also admits Z^n local systems, cellular automata, SFTs, finite CSP/SAT restrictions, and operadic rewrite systems as special presentations.

## Kernel-internal automata

`KernelInternal` requires every generator to preserve the zero-defect shell. The carrier and transition family are not conflated with the kernel:

```text
carrier × generators × kernel-preservation proof
```

This makes the same definition usable for:

- Rubik face turns on the finite cube group;
- translation-invariant local updates on Z^n;
- SFT endomorphisms;
- finite SAT/CSP rewrite systems;
- hybrid phasic systems whose continuous lift projects back to discrete states.

## Holonomy contraction

The exact algebraic theorem records:

1. each selected M9 cell has a phase-valued holonomy;
2. the phase contracts to a nonnegative local defect;
3. zero total contraction is equivalent to selected-cell flatness.

A stronger curvature-to-edge coercivity claim is not automatic on a periodic torus. The formal boundary requires:

- a finite connected complex;
- compact phase carrier;
- gauge fixing or quotienting;
- control of global flat-cycle sectors;
- a discrete Poincaré estimate;
- a proved curvature-to-edge residual bound.

This corrects the tempting but false unrestricted inference that flat plaquette holonomy alone trivialises all transport on a torus.

## Control metric and Cayley restriction

A generator action supplies move costs and acts on the ambient state carrier. The control distance is the infimum of generated path costs. Under the discrete restrictions

- states lie on the legal roots-of-unity/permutation lattice;
- every generator preserves that lattice and the kernel;
- every generator has unit cost;

the control distance equals the classical Cayley shortest-word distance.

An admissible geodesic additionally records:

- shortestness among generated kernel-respecting paths;
- a scalar-defect budget;
- availability of a phasic interpolation;
- projection of that interpolation to the same move word.

## Comparison with existing standards

The formalism recovers standard cube-group and Cayley-graph theory exactly on the discrete shell. Its additional structure is:

- quotient graphs as explicit M-channel projections;
- higher cells filled by commuting or relator loops;
- phase-valued transport and holonomy;
- scalar kernel defect;
- weighted control/Finsler costs;
- rank-unbounded M lifts.

The novelty claim should therefore concern this structured unification and its preservation theorems, not the Cayley graph or Rubik group themselves.

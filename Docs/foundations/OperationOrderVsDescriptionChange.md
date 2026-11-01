# Operation order versus description change

This note records a narrow conceptual distinction and its current formal status in DASHI.
It is not a claim that either project has completed a derivation of physics.
## The two questions
A Wolfram-style causal-invariance question is:
> If the locally available operations happen in another order, is the same causal structure obtained?
A DASHI description-change question is:
> If the same state is rewritten more compactly, is the observable preserved and does a lawful continuation remain?
The first varies **which operation happens first**. The second varies **how the state is carried or normalised**.
For a discretised trajectory, these become:
- operation-order question: may independent local update atoms be reordered without changing which events can influence which others?
- description-change question: may the trajectory state be canonicalised, reduced, or compressed without changing the named physical observable or destroying the admitted next evolution?
These questions can overlap, but neither implies the other. A system may have a stable canonical form while remaining order-sensitive. A rewrite system may be causally invariant while retaining many inequivalent state descriptions.
## Why this is more than changing units
Changing metres to feet is an invertible relabelling; no information is discarded and the translation back is fixed.
The harder case changes the carrier itself. Examples include resolving carry structure, projecting to a reduced state, integrating out degrees of freedom, changing lattice resolution, or replacing a history with a canonical representative. Such a change must identify what is preserved and prove that the resulting state still belongs to the lawful domain.
The general DASHI test is therefore not merely:
> Can the old description be reconstructed?
It is:
> Does the description-changing operator preserve the named observable, preserve the admitted continuation, reach a canonical state, and become idempotent there?
This does not replace Nyquist theory, statistics, gauge theory, numerical analysis, or renormalisation. Those theories can supply particular preservation theorems. The DASHI layer packages the common proof obligation and keeps unsupported generalisation fail-closed.
## Current checked witness
`DASHI.Physics.Closure.DescriptionChangeLawPreservation` defines the generic proof surface and instantiates it with the existing arithmetic normaliser:
- state: `NormalizeAddState`;
- description-changing operator: `normalizeAdd`;
- observable: `lhs + rhs`;
- lawful continuation: the next normalised state is canonical;
- canonicality: `normalizeAddCanonical`;
- fixed-point law: applying `normalizeAdd` twice equals applying it once;
- MDL connection: `W9MDLTerminationSeamRoute.canonicalMDLTerminationSeamWitness`.
This is a small but real theorem-level example. It proves that one existing canonicalisation changes residue/carry bookkeeping while preserving the selected observable and its admitted canonical continuation.
It does **not** prove:
- arbitrary coarse-graining preserves physical law;
- arbitrary compressed states retain all lawful futures;
- causal invariance under reordered rewrite events;
- a universal renormalisation theorem;
- emergence or derivation of spacetime.
## Relationship to the existing repository
The module reuses rather than duplicates:
- `DASHI.Arithmetic.NormalizeAdd` for canonicalisation;
- `DASHI.Arithmetic.NormalizeAddState` for the state and canonical predicate;
- `DASHI.Arithmetic.NormalizeAddSumPreservation` for the preserved observable;
- `DASHI.Physics.Closure.W9MDLTerminationSeamRoute` for the accepted MDL termination seam and its non-promotion boundaries.
The next substantive extension would require a genuinely physical carrier and an explicit law-preservation theorem, for example a coarse/fine spacetime map that preserves a causal observable and admissible evolution. That extension should instantiate the same proof surface rather than promoting the arithmetic witness into physics by analogy.
# Operation order versus representation change
This note records a conceptual distinction and its current formal status in DASHI. It is not a claim that either DASHI or the Wolfram Physics Project has completed a derivation of physics.
The stronger DASHI representation question is:
> If the same system is carried at another resolution, in another basis, or through a reduced description, does the kernel still describe the same admissible evolution and the same dynamical shapes?
The first varies **which operation happens first**. The second varies **the form through which the state and its dynamics are represented**.
For a discretised trajectory:
- operation-order question: may independent update atoms be reordered without changing which events can influence which others?
- representation question: may the trajectory be projected, canonicalised, compressed, or refined while preserving the evolution law, admitted states, observables, and relevant fixed points or attractors?
These questions overlap but neither implies the other. A system may have a stable canonical representation while remaining order-sensitive. A rewrite system may be causally invariant while two coarse representations obey different effective dynamics.
## The real DASHI test is a commuting kernel square
The earlier narrow formulation asked whether a description change preserved one observable and a lawful continuation. That remains useful for one-state canonicalisation, but the full operator question is stronger:
```text
fine state  -- fine kernel -->  evolved fine state
    |                              |
 projection                    projection
    v                              v
coarse state -- coarse kernel -> evolved coarse state
```
The representation change preserves the law when the two routes agree, exactly or through a named residual/equivalence:
project (fineStep x)  =  coarseStep (project x)
This is already the central condition in `DASHI.Physics.Refinement`: its exact refinement step requires `project (step₁ x) ≡ step₀ (project x)`, while `ApproxRefinementStep` carries the same obligation through an explicit approximate relation.
This is why the DASHI question is not merely “can the original signal be reconstructed?” or “does a statistic remain close?” It asks whether the **operator itself survives the change of representation**.
Changing metres to feet is an invertible relabelling. The state space and the dynamics have not actually been reduced.
The harder changes include:
- projecting a fine field to a coarse field;
- integrating out degrees of freedom;
- changing lattice or refinement depth;
- replacing a state by a canonical quotient representative;
- retaining only support, sign, phase, residue, or another structured carrier;
- transporting a kernel between those carriers.
A lawful change must say what counts as the same physics and prove that the kernel respects that relation. Numerical closeness, reconstructability, statistical insignificance, or low description length do not establish this by themselves.
## Fixed points and attractors
Kernel compatibility gives a concrete structural payoff. If an admissible fine state is a fixed point,
fineStep x = x
and projection commutes with the kernel, then the projected state is a coarse fixed point:
coarseStep (project x) = project x
`DASHI.Physics.Closure.RepresentationKernelCompatibility.projectedFixedPoint` proves this elementary transport theorem.
This is the first rigorous part of the “shape” language: the preserved object is not merely a scalar measurement but a dynamical shape. Full attractor or basin preservation is stronger and still requires a metric, neighbourhood/basin definition, convergence law, and projection-stability theorem.
The uploaded attractor/retrocausality discussion is therefore relevant only at this bounded point: a future or terminal object can constrain the selected history through fixed-point, boundary, or admissibility structure without establishing literal retrocausal physical influence. The module explicitly does not promote retrocausality.
## Admissibility, equivalence, and MDL have different jobs
The cross-pollinated operator separates three layers:
1. **Admissibility** says which states and transitions belong to the lawful domain.
2. **Kernel compatibility** says whether evolution survives projection or redescription.
3. **MDL** chooses a cheaper canonical representative inside an equivalence class already shown to preserve the physics.
This order matters. MDL does not make two states physically equivalent merely because one is shorter. The new `MDLRepresentativeSelection` surface therefore requires:
- an explicit same-physics relation;
- preservation of that relation by canonical selection;
- non-increasing description cost;
- idempotence of the canonical representative.
That matches the existing repository split between checked invariance/closure claims and selection or termination seams.
## Current checked surfaces
`DASHI.Physics.Closure.DescriptionChangeLawPreservation` remains the small concrete one-state witness:
- canonicalisation: `normalizeAdd`;
- admitted continuation: the next state is canonical;
- fixed-point law: normalising twice equals normalising once;
`DASHI.Physics.Closure.RepresentationKernelCompatibility` adds the broader operator-level surface:
- exact fine/coarse kernel compatibility;
- admissibility transport;
- observable transport;
- projected fixed-point theorem;
- approximate compatibility through an explicit same-physics relation;
- MDL canonical representative selection only after equivalence is supplied.
The module cross-references rather than replaces `DASHI.Physics.Refinement`, whose project/evolve commuting law is the existing formal seed.
## What remains open
The new surface does **not** prove:
- every attractor or basin survives projection;
- reordered operations are causally invariant;
- emergence of spacetime or quantum mechanics;
- retrocausal influence;
- that minimum description length identifies physical truth.
A substantive physics instance now has a clear target: instantiate the compatibility square on a physical fine/coarse carrier, provide its admissibility and observable maps, state the exact or residual equivalence, and prove that the appropriate dynamics commute with projection.

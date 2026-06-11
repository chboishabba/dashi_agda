# 15. Cross-Domain Variational Spine

Status: `docs-only; structural bridge; non-promoting`

This section records a structural bridge exposed by
`DASHI.Physics.Closure.CrossDomainVariationalSpine`. It is useful for outside
readers because it gives one common typed shape for several domain-facing
theorem targets. It is not a closure theorem for chemistry, biology,
perception, or physics unification.

## Formal Model

O: The object is a cross-domain typed variational spine for comparing
domain-specific theorem targets.

R: The requirement is to state the shared structure safely: the paper may use
the bridge to organize projection, defect, observation, symmetry, and
local-minimum language across domains, but it may not promote empirical or
physical closure.

C: The controlling code surface is
`DASHI.Physics.Closure.CrossDomainVariationalSpine`, especially
`TypedVariationalObject`, `DomainSpineTarget`, and
`canonicalCrossDomainVariationalSpineBoundary`.

S: The current state is `spineTypedNonPromoting`. The common object and its
domain rows are present as a normalized theorem target, while calibration,
universality, tractability, empirical prediction receipts, and recovery
equivalence are explicitly missing.

L: The lattice has three relevant levels: shared formal schema, domain-specific
theorem target, and promoted domain result. This section occupies only the
first two levels.

P: Present the bridge as a controlled abstraction layer that helps a reader
see why the same formal vocabulary recurs in molecular, bonding, biological,
and perceptual targets.

G: The governance rule is fail-closed. Structural composability does not imply
chemistry closure, bonding closure, spectra, protein folding, biology
prediction, perception fit, or TOE promotion.

F: The remaining gaps are quantitative calibration, a universality proof,
computational tractability, chemistry/biology/perception empirical prediction
receipts, and cross-domain recovery equivalence.

## Typed Object

The common object is written in the Agda boundary as

```text
(X, delta, pi, defect, gate, observation, symmetry)
```

For outside readers, the fields have the following intended roles.

| Field | Outside-reader role |
|---|---|
| `X` | The carrier of states or configurations in the domain under discussion. |
| `delta` | A complexity, MDL, Lyapunov, energy, or variational functional on that carrier. |
| `pi` | A promoted projection or normal form map on the carrier. |
| `defect` | The residual information left after projection, represented in the domain's own carrier vocabulary. |
| `gate` | An admissibility relation that says which transitions or comparisons are allowed. |
| `observation` | A quotient, readout, or observable-facing map from the carrier. |
| `symmetry` | An action whose orbit classes supply invariants or equivalent readouts. |

The point of this tuple is not that all domains are literally the same kind of
object. The point is that several theorem targets can be written with the same
typed roles: a carrier, a functional, a projection, a residual defect, an
admissibility gate, an observation quotient, and a symmetry action. This makes
the bridge a formal normalization device rather than a metaphysical identity
claim.

## Shared Structures

The Agda surface records a small family of shared lawful structures:
admissible descent, projection-defect decomposition, symmetry-orbit
structure, scale-sensitive observability, non-collapse intermediate states,
and orbit-class invariants. These are paper-usable as organizing vocabulary.

The safe reading is structural. A local minimum in one domain and an orbit
class in another can be compared because both are being placed into a common
typed schema. The schema does not say that the domains have already been
calibrated against data, that their computations are tractable, or that a
domain-specific recovery theorem has been proved.

One useful sentence for the manuscript is:

> Stable scientific objects across the named domains can be represented as
> local-minimum or orbit-class targets of a shared typed projection-defect /
> MDL spine.

That sentence is safe only with the phrase "represented as" and only while the
bridge remains explicitly non-promoting.

## Domain Table

| Domain target | Carrier `X` | Functional `delta` | Projection / fixed point | Observation or invariant | Safe paper statement |
|---|---|---|---|---|---|
| Molecular PES | Nuclear configuration | Potential-energy surface `V(R)` | Local minimum `R*` | Energy-facing minimum structure | Molecular relaxation can be stated as admissible descent toward a PES minimum target. |
| Bonding | Density carrier | Density functional `V[rho]` | Promoted bonding density `rho*` | Projection-defect split between bonding density and antibonding residual | Bonding language can be staged as a projection-defect theorem target. |
| Resonance | Resonance-form family | MDL or compression cost over weighted forms | Weighted hybrid selected by an admissible compression rule | Compression invariant of the selected representation | Resonance can be described as constrained compression over projection families. |
| Biological | Sequence, fold, or biological state | Free-energy, likelihood, or MDL-style cost | Folded or quasispecies attractor target | Attractor or stable-state readout | Folding and quasispecies language can be staged through the local-minimum schema. |
| Developmental genomic inverse | Genome/regulatory/developmental carrier | Phenotype residual plus MDL, pleiotropy, and layer-constraint penalties | Candidate regulatory fibre / candidate genomic perturbation | Ranked inverse-search surface from phenotype or brain residuals | Developmental genomics can be staged as a non-promoting inverse-probe target, not a gene-causation result. |
| Perceptual | Phase carrier | Perceptual compression or orbit cost | Orbit-class attractor target | Kluver readout such as tunnel, spiral, lattice, or cobweb class | Perceptual form constants can be stated as symmetry-orbit quotient targets. |

The table is deliberately phrased as "target" language. It does not assert
that the corresponding domain theorem has been completed. It says that the
same typed spine is available for stating those targets without changing the
claim-governance rules used elsewhere in the manuscript.

## Allowed Claims

The following claims are allowed for Paper 1 if they remain tied to the
cross-domain boundary and are not used as empirical validation:

1. Physics, chemistry, biology, and perception can be organized by a shared
   typed projection-defect / MDL spine as a formal theorem target.
2. The cross-domain extension is structural and compositional.
3. Stable domain objects can be represented by a common local-minimum schema.
4. Kluver form constants can be stated as symmetry-orbit quotient targets.
5. Developmental-genomic inverse language may be staged as candidate-fibre
   ranking over typed developmental residuals.
6. The bridge clarifies paper vocabulary by separating common formal roles
   from domain-specific promoted results.

## Forbidden Claims

The following claims are not allowed from this bridge:

1. Chemistry closure has been proved.
2. Bonding-energy or molecular-spectrum prediction has been derived.
3. A protein-folding result, biological prediction, or evolutionary prediction
   has been established.
4. DNA encodes a brain snapshot, thought, percept, disease label, or
   one-gene-causes-condition result.
5. A perception or cortical-mechanism empirical fit has been established.
6. The molecular, bonding, biological, perceptual, and wave-function carriers
   are literally the same object.
7. Quantitative calibration, computational tractability, or cross-domain
   recovery equivalence has been closed.
8. A theory-of-everything, limited SM+GR, GRQFT, sourced GR, or physical
   calibration claim follows from the spine.

## Manuscript Use

This section is best used after the core formal-methods claim has already been
made. Its job is to explain why the same words recur across otherwise distant
surfaces: projection, defect, admissible descent, observation quotient,
symmetry orbit, invariant, and local minimum. Those words are not decorative
analogies. They are the fields and lawful structures of a typed theorem target.

The reviewer-facing boundary is equally important. The bridge can make the
paper easier to read by showing a common shape, but it cannot increase the
paper's positive theorem inventory. Any stronger domain statement must still
point to its own inhabited receipt, accepted authority token, or promoted
theorem surface.

# Unified Routes And Lanes Plan

Declared surface level: `architecture` and `roadmap`.

This plan generalizes the stellar-composition simulator pattern across the
repo.  It does not promote any lane.  It defines how every route should move
from existing carrier language to executable receipts, then to blocked or
promoted Agda guards.

## Core Pattern

Every route should be readable as the same six-stage pipeline:

```text
lane object
  -> canonical parent / carrier grammar
  -> bounded observable or theorem target
  -> executable or formal receipt
  -> Agda guard with explicit promotion flags
  -> adapter path toward theorem, authority, or empirical validation
```

The canonical theorem spine remains owned by `Docs/ClosurePipeline.md`.
Simulator execution remains owned by `Docs/SimulatorRoadmap.md`.  Lane maturity
and adapter boundaries remain owned by `Docs/PhysicsLaneMaturityMatrix.md`.
This file is the joining plan: it tells future work how to make the lanes
commute without strengthening claims by analogy.

## Lane Families

| Family | Current role | Next bounded slice | Promotion blockers |
|---|---|---|---|
| Canonical closure spine | Theorem route from projection defect through quadratic, signature, Clifford, and closure. | Keep one canonical import/citation path and expose receipt-facing summaries for downstream lanes. | Parallel emergence routes, stale imports, heavy aggregate validation. |
| Cross-scale simulator | Unified facade and executable bounded diagnostics. | Repeat the stellar pattern for atom, molecule, chemistry, cell, organism, and stellar observables. | Missing real physical model authorities and empirical validation receipts. |
| Maxwell / gauge | Bridged and partially packaged field-equation surfaces. | Bounded gauge-field diagnostic: carrier table -> finite curvature/source proxy -> receipt. | Metric/Hodge authority, matter-current extraction, calibration. |
| Yang-Mills / non-abelian | Clay-facing KP/Balaban and field-equation receipt stack. | Bounded finite-gauge worker receipts that separate actual polymer activity from proxy rho. | Actual Wilson polymer activity, Balaban RG transfer, continuum gap, external acceptance. |
| Schrodinger / dynamics | Bounded dynamics consumers and Hamiltonian-facing scopes. | Deterministic finite-state Hamiltonian proxy receipt with explicit no-derivation guard. | Hilbert representation, self-adjoint Hamiltonian, Born rule, calibration. |
| GR / curvature | Known-limits GR bridge plus weak-field external baseline. | Extend weak-field baseline receipts into a curvature/stress-energy blocker index. | Non-flat Levi-Civita law, Ricci/Einstein contraction, physical stress-energy, `G` normalization. |
| Empirical prediction | Provider intake, HEPData residual, comparison-law, and authority gates. | Standard empirical receipt harness: source checksum -> projection -> comparison law -> authority decision. | Accepted provider authority, covariance, transform law, calibration, holdout validation. |
| Biology / DNA / brain | Typed observation and chemistry/channel carriers. | Domain-specific bounded observation receipts that keep subject, source, and clinical authority separate. | Wet-lab/clinical authority, measurement provenance, biological causation, intervention validation. |
| PNF / ITIR / language | Runtime/parser/residual carrier surfaces. | Runtime receipt intake: source artifact -> parser projection -> residual table -> Agda non-promotion guard. | Runtime provenance, external execution receipts, semantic adequacy validation. |
| Arithmetic / moonshine / Gate 3 | Hecke, j, CM/atom grammar, finite frame, and barrier targets. | Bounded finite-frame diagnostics with CM/Hecke partition fences and no continuum promotion. | Density, Mosco recovery, no spectral pollution, mass-shell bridge. |

## Implementation Roadmap

1. Unify the receipt shape.
   - For each lane, create or identify one `...Receipt.agda` owner.
   - Each owner must expose status, artifact paths or formal inputs, blocker
     constructors, canonical receipt, and promotion guards.
   - Boolean guard names should follow the lane claim directly, for example
     `carrierInternalPrediction`, `stellarEvolutionPromoted`,
     `maxwellEquationPromoted`, or `empiricalAdequacyAccepted`.

2. Add bounded executable slices before real-model claims.
   - Prefer deterministic scripts in `scripts/` with JSON/CSV/Markdown outputs.
   - Every artifact must include `promotion_status = NO_PROMOTION` unless an
     accepted authority receipt is actually present.
   - Outputs should name both observed/proxy values and missing real-model
     receipts so the next step is mechanically visible.

3. Wire each lane into the unified facade.
   - Put shared parent objects under `DASHI.Unified` only when the lane can be
     described without importing heavy closure cones.
   - Keep theorem owners under their existing physics/ontology modules.
   - The unified facade may expose receipts, but it must not become the source
     of theorem promotion.

4. Build adapter packs by family.
   - Physics lanes need metric, representation, Born/statistics, and
     calibration adapters as named blockers.
   - Empirical lanes need source, checksum, transform, comparison-law,
     covariance, and authority adapters.
   - Biology/clinical lanes need subject/session provenance, measurement
     authority, causation boundaries, and intervention/clinical validation.
   - Runtime lanes need execution provenance, parser version, source checksum,
     residual policy, and replayability.

5. Promote only through explicit gates.
   - A bounded proxy can graduate to a real-model adapter only when it consumes
     named external or theorem receipts.
   - A real-model adapter can graduate to a promoted claim only when its Agda
     guard changes from false by construction to a consumed proof/authority
     token.
   - No lane may promote from another lane's analogy, naming overlap, or
     successful proxy diagnostic.

## Milestones

| Milestone | Deliverable | Validation |
|---|---|---|
| M0: Receipt schema discipline | One short checklist for new receipt modules and scripts. | `rg` check for required promotion fields in new artifacts. |
| M1: Physics bounded slices | Maxwell, Schrodinger, GR-curvature, and empirical diagnostics mirror the stellar slice. | Focused pytest plus targeted Agda receipt checks. |
| M2: Cross-scale matter ladder | Atom/molecule/cell/organism/stellar parent receipts share the same cross-scale surface. | `agda DASHI/Unified/CrossScaleMatterPhysics.agda`. |
| M3: Adapter blocker index | One queryable blocker index for metric, representation, Born/statistics, calibration, provenance, and validation gates. | Targeted Agda owner plus docs link checks. |
| M4: Empirical authority harness | Standard source-checksum/projection/comparison-law/authority runner. | Pytest with synthetic pass/fail fixtures. |
| M5: Route commutation audit | Audit that facade, theorem, empirical, and runtime lanes cite the same owner receipts. | Repo audit plus `Docs/AgdaValidationTargets.md` updates. |

## Claim Discipline

Defensible wording:

> DASHI lanes are being normalized into one receipt-gated architecture:
> carrier grammar, bounded observable, executable/formal receipt, explicit
> blocker set, and fail-closed promotion guard.

Non-defensible wording:

> DASHI has already derived all routes because the lanes share a vocabulary.

The route-unification work is successful only when it makes missing receipts
more visible, not when it hides them behind a larger facade.

## Immediate Next Work

Use the stellar slice as the template for the next three bounded lanes:

1. Maxwell/gauge finite curvature-source proxy.
2. Schrodinger finite Hamiltonian-evolution proxy.
3. Empirical authority harness for source checksum, transform, comparison law,
   and authority decision.

After those land, add the shared adapter blocker index and route commutation
audit so the rest of the biology, runtime, arithmetic, Gate 3, NS, and YM lanes
can join the same pattern without changing their current promotion status.

# 07-02 Physics Bridge Mapping (Closure → Physics)

Objective: define an adapter boundary that is explicitly centered on the existing seam
`DASHI/Physics/ClosureGlue.agda` (record `ClosureAxioms`) and the signature seam output
`DASHI/Physics/Signature31.agda` (identifier `sig31`).

This file is a mapping spec only. It deliberately avoids claiming that full GR/QFT
objects exist in Agda today, and it introduces no new dependencies.

## Bridge Positioning (Layering)

- Below: the core closure seam `DASHI/Physics/ClosureGlue.agda`.
- At: the signature forcing seam `DASHI/Physics/Signature31.agda` (with `sig31` and its
  current witness path).
- Above: thin adapter modules that expose stable names/types for future GR/QFT objects.
- Not included: any `Verification.*` surfaces; those are intentionally out-of-scope here.

## Mapping Table: `ClosureAxioms` Fields → Physics Concepts

Source record (real path): `DASHI/Physics/ClosureGlue.agda`

The bridge surface is anchored on these literal identifiers (from `ClosureAxioms`):
`S`, `U`, `T`, `sc`, `inv`, `iso`, `fs`.

| Closure concept (identifier) | Abstract physics concept (bridge target) | Status | Notes / adapter boundary |
|---|---|---|---|
| `S : Set` | Carrier of "states/events" (kinematic arena) | theorem-critical | Must remain an abstract carrier; bridges must not assume manifold structure. |
| `U : Ultrametric S` | Scale / locality structure (coarse causal neighborhood proxy) | stubbed/prototype | Treated as the minimal notion of neighborhood/scale; later may refine toward causal cones or topology. |
| `T : S → S` | Dynamics step (time evolution / update operator) | theorem-critical | Bridge treats this as the only required dynamics primitive; any Hamiltonian/Lagrangian comes later. |
| `sc : StrictContraction U T` | Well-posedness / convergence (existence + uniqueness of fixed point) | theorem-critical | This is the main "closure" guarantee; bridge modules may rely on derived facts like `fp`. |
| `inv : Involution S` | Discrete symmetry (C/P/T-like involution placeholder) | stubbed/prototype | Only requires involutive structure; does not claim any specific physical interpretation yet. |
| `iso : Isotropy U T` | Symmetry action preserving dynamics and locality | theorem-critical | This is the main symmetry seam. Bridges should expose an abstract "Lorentz-like" group action slot. |
| `fs : FiniteSpeed T` | Finite propagation / causality constraint | theorem-critical | Minimal causality constraint; later can become a lightcone or hyperbolicity-like condition. |

## Signature Seam: Where `sig31` Enters

Real path: `DASHI/Physics/Signature31.agda`

- `sig31` is the canonical signature target for the current classification stub.
- The current witness path is through
  `involution+isotropy+finiteSpeed⇒signature31` in `DASHI/Physics/Signature31.agda`.

Bridge modules must treat this as an attachment point only: they can *reference* the
signature seam, but should not import or define heavy geometry/GR/QFT structures.

## Adapter Contracts (What Bridge Modules Are Allowed To Do)

- Allowed: re-export `ClosureAxioms` and derived facts from `DASHI.Physics.ClosureGlue`.
- Allowed: define records of parameters that describe "GR-side" and "QFT-side" adapters
  in terms of closure data, without committing to concrete implementations.
- Allowed: mention the signature seam (`sig31`) as a target classification label.

- Avoid: postulating or importing full GR/QFT libraries; this phase only defines names
  and boundaries.
- Avoid: pulling in `Verification.*` modules.

## Notes For Future Phases (Non-binding)

- GR adapter likely refines `fs` (finite speed) into a causal structure and uses `iso`
  to constrain local symmetry.
- QFT adapter likely refines `inv` and `iso` into discrete/continuous symmetry data and
  interprets `T` as an evolution operator on states/observables.

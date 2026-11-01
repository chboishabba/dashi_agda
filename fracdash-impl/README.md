# FRACDASH Executable Witness/Status Reference

Purpose: document the FRACDASH-side executable witness/status layer so upstream `DASHI/Physics/Closure/*` can track how the compressed FRACTRAN bridge aligns with the authoritative execution-admissibility and family-classification witnesses.

## Scope
- `../dashi_agda` remains the semantic source of truth; this folder records how FRACDASH mirrors or approximates those witnesses in executable form.
- FRACDASH currently implements regime-class and well-formedness witnesses (contraction + bounded transmutation) for the closed bridge slices (`physics1`, `physics3`, `physics15`, `physics19`, `physics20`, `physics21`, `physics22`) but does **not yet** implement the upstream execution-admissibility or family-classification witnesses.
- Monster 10-walk intake for this repo is summarized in `MONSTER10WALK_INTAKE.md`;
  treat the pinned `monster/experiments/bott_periodicity/monster_walk.tex` as
  the upstream source and `../FRACDASH/MONSTER10WALK_CANONICAL.md` as the
  current local executable interpretation.

## Upstream surfaces to mirror
- `DASHI/Physics/Closure/MinimalCrediblePhysicsClosure.agda`: now exports `authoritativeExecutionAdmissibilityWitness` and `authoritativeFamilyClassificationWitness`.
- `DASHI/Physics/Closure/PhysicsClosureCoreWitness.agda`: includes `executionAdmissibilityWitness` and `familyClassificationWitness` alongside dynamics/observables.
- `DASHI/Physics/Closure/PhysicsClosureFullInstance.agda`: wires current-trace/current-family witnesses.
- `DASHI/Physics/Closure/ExecutionAdmissibilityWitness.agda`: vocabulary (`SomeExecutionAdmissibilityWitness`, `SomeFamilyClassificationWitness`).
- `DASHI/Physics/Closure/ExecutionAdmissibilityCurrentTraceWitness.agda`, `...CurrentFamilyWitness.agda`: concrete witnesses used by the minimal closure.

## FRACDASH executable counterparts (status)
- Structural regime layer lives in `formalism/GenericMacroBridge.agda` (regime class, contraction, bounded transmutation) and `formalism/BridgeInstances.agda` (slice proofs).
- Well-formedness of prime-state encodings is enforced per-slice via `wellFormed-preserved` in bridge records; no global admissibility hierarchy yet.
- No FRACDASH module currently exports an object that can be interpreted as `SomeExecutionAdmissibilityWitness` or `SomeFamilyClassificationWitness`.

## Proposed minimal mapping
- Add a FRACDASH-side record capturing executable status per slice:
  - `regimeClass : RegimeClass` (conservative vs transmuting contracting)
  - `wfY : WellFormedY` proof for the paired-prime state
  - `executionAdmissible : Set` (runtime predicate or proof stub)
  - `familyTag : Set` (small finite tag for the current slice family)
  - `evidence : executionAdmissible` constructed from the bridge proofs when available
- Treat this as an *executable surrogate*; it reports what the FRACTRAN bridge can currently guarantee, not the full upstream admissibility lattice.

## Intent for upstream reuse
- Keep upstream closure authoritative; this folder just documents the FRACDASH executable seam so upstream authors can see what needs to be proven or tightened.
- When FRACDASH grows explicit admissibility/family witnesses, mirror their shape here so the delta between executable status and upstream theorems stays visible.

# 07-01 Core Spine Diagram

This is the canonical “physics-critical” dependency diagram for the DASHI closure→signature seam.

## Minimal Chain (What Bridge Work Must Respect)

```
Ultrametric / contraction machinery
  └─ (StrictContraction fp/unique machinery)
       ↓
Closure interface seam
  └─ `record ClosureAxioms` (S, U, T, sc, inv, iso, fs)
       ↓
Real-operator layer (current concrete instance surface)
  ├─ `Pᵣ` (projection-like; currently concrete)
  ├─ `Cᵣ` (canonicalization/renormalization; currently identity)
  └─ `Rᵣ` (recovery; currently identity)
       ↓
Signature forcing seam (Stage B)
  └─ (cone + arrow + isotropy → shell action/orbit profile → sig31)
       ↓
Signature surface
  └─ `sig31` / `SignatureTheorem` (note: at least one trivial witness exists in `DASHI/Physics/Signature31.agda`)
       ↓
Canonical Stage C ladder / consumers
  └─ re-exported + documented by `DASHI/Physics/Closure/PhysicsClosureSummary.agda`
       ↓
Downstream bridges/consumers (future)
  └─ GR/QFT adapter modules must attach here, not inside core seam modules
```

## Frozen Interface Checklist

Treat these as the stable API surfaces that bridge work should depend on:
- `DASHI/Physics/ClosureGlue.agda` (`ClosureAxioms`)
- The minimal signature seam identifiers (e.g. `sig31`) as exposed by existing signature modules

Bridge work should NOT:
- modify `ClosureAxioms` fields without an explicit, deliberate interface migration
- pull `Verification/*` modules into the core seam
- rewrite the canonical Stage C ladder; instead attach adapters on top

## Notes

- The repo already has the correct abstraction boundary: `ClosureAxioms`.
- The “missing real operators” gap is operationally visible: `Cᵣ` and `Rᵣ` are identity in `DASHI/Physics/RealOperators.agda`.
- The signature seam exists, but parts of it may be prototype/trivial; tightening that is separate from the operator-substance plan.

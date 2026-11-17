# F13 dynamic dependency cone and multiple-source ownership — 17 November 2026

**PR #1524 — source-author proof candidate, independent exact Python/SymPy tests.**
The objective is to replace the older "untouched by every stage" frame with a mathematically correct **evolving dependency cone** for arbitrary ordered two-coordinate updates and source injections.

## Existing owners reused

- `SmithFilsingerIndexedFaceIncidenceExact.sameID`: existing decidable Nat coordinate identity
- `SmithFilsingerLocalCausalADEFrameExact.LocalPrimitive`, `applyPrimitive`, `outsidePrimitive`: existing two-coordinate update model
- `scripts/smith_filsinger_local_causal_ade_sympy.py`: actual local rational Cayley, heterogeneous Maxwell/Lorentz material and source/load work receipts
- `SmithFilsingerYeeCFLConeGuardExact`: physical-front/CFL logical firewall
- existing true pinned Agda 2.9 checker and separate exact SymPy checker

## New all-N Agda dynamic reach theorem

`DASHI/Physics/Motors/SmithFilsingerLocalCausalADEReachExact.agda` adds `ZeroPreserving z p`, with *two contentful proofs* that an actual primitive's two output functions map two zero inputs to zero. This is essential: locality without zero preservation permits arbitrary spontaneous activation and does NOT imply a source dependency cone.

The `reachStep` set-valued operator preserves existing reachability for an untouched coordinate. If an update touches the coordinate, it may be newly reached **only when at least one of the two previous input coordinates was already reachable**. Thus the reach set is a sound structural overapproximation of possible nonzero support, not necessarily the smallest set of actually nonzero values.

`oneStepOutsideZero` proves a source-free stage preserves zero outside the new set; `noSignalOutsideDynamicCone` proves this for **arbitrary finite noncommuting stage lists** by induction. It is a strengthened theorem compared with the previous `neverTouchedRetainsOriginal`.

**Newly found and repaired source-seeding problem:** the older Python `dependency_cone(initial_index,steps)` did not add a second natural/controller source injected at a previously disconnected cell. This could incorrectly understate the reachability support even when its work ledger was balanced. The new `dependency_cone` unconditionally seeds each explicitly tagged natural or controller injection. `verified_dependency_trace` checks *all intermediate states* for consecutiveness, exact zero outside the growing cone, and no mutation outside the declared primitive/source support. Untyped or forged source ownership is rejected. These are mathematical model traces, not authenticated meter receipts.

The Agda theorem also now handles **arbitrarily interleaved source injections**: `LocalEvent` distinguishes `propagate` from `injectAt naturalSource/controllerSource`, `seedReach` makes the injection coordinate an unconditional reachability root, `injectionOutsideZero` proves the source step cannot activate elsewhere, and `noSignalOutsideInterleavedSourceCone` establishes the all-stage invariant. Mere `naturalSource` tagging does NOT independently verify Sun–Earth source attribution.

## Actual exact arithmetic checks

The independent local source-equivalent suite, run with SymPy 1.14.0 and pytest 9.0.2, now passes **138/138 tests**: previous 131 tests plus seven new parameterized/adversarial cases for later disjoint source injection, staged cone growth, forged update support, untyped source ownership and source kicks that modify unrelated active cells.

The new Python source and tests are committed in the prior owners, not copied to a parallel algorithm. The Agda source has no explicit postulate or proof hole and is added to both lists in `scripts/check_smith_filsinger_formal_weld_agda29.sh`.

**Verification status:** Agda 2.9 and Nix are unavailable in the current runtime. The new source is an Agda *candidate*, not a typechecked proof. The 138 mathematical tests were run from the independent local source-equivalent package, not from a completed exact-head GitHub CI workflow. No claim about physical Maxwell front speed follows.

## Remaining highest-alpha welds

1. **D1:** run the existing pinned Agda 2.9 checker on the exact PR head; repair any scoping, reduction, termination or universe errors. An Agda source-level induction is not an accepted theorem until typechecked.
2. **F13 same-primitive:** realize the *actual rational two-coordinate Cayley matrix* as the `LocalPrimitive` update with `ZeroPreserving` proofs, and connect source-injection records, material weights and the original indexed face topology. The current Agda invariant is fully parametric and conditional on the individual primitive zero-preserving witness.
3. **F02/F13 physical:** mathematically and physically prove a real 3D Maxwell/dispersive retarded support and calibrate soil/air/ionosphere distances, time, full gyrotropic conductivity and open/radiating boundary. A finite event graph can cross several edges in an arbitrarily small physical macro-step; numerical graph support alone is NOT the physical light cone.
4. **F15:** independently observed original environmental natural work and terminal VI under the complete source/receiver/material/controller restoring cycle; cannot be obtained from these synthetic work receipts or positive source-injection fixtures.

No ESD edit; no unearned 100-fold/solar claim. Existing Green, Maxwell and user-origin Smith/Filsinger attribution retained.

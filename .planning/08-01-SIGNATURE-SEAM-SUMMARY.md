# 08-01 Signature Seam Plan Summary

## Accomplishments

- Mapped all signature seam entrypoints and classified trivial vs theorem-critical surfaces.
- Isolated the trivial `sig31` witness so it is explicitly prototype-only and cannot be mistaken for a canonical theorem surface.
- Made the canonical closure summary’s signature seam routing explicit (canonical = shift-orbit-profile theorem path).

## Files Modified

- `/home/c/Documents/code/dashi_agda/.planning/08-01-SIGNATURE-SEAM-INVENTORY.md`
- `/home/c/Documents/code/dashi_agda/DASHI/Physics/Signature31.agda`
- `/home/c/Documents/code/dashi_agda/DASHI/Physics/Closure/PhysicsClosureSummary.agda`

## Decisions Made

- Canonical signature source for the closure ladder is `DASHI/Physics/Signature31FromShiftOrbitProfile.agda` (realization-specific but theorem-critical).
- `DASHI/Physics/Signature31.agda` is explicitly prototype-only; its witness is named as such to avoid accidental canonical import.

## Issues Encountered

- `agda -i . -i /usr/share/agda/lib/stdlib DASHI/Everything.agda` does not currently typecheck on this tree (failure observed in `/home/c/Documents/code/dashi_agda/DASHI/Geometry/RealIsotropy/Instance/Core.agda:41`). This appears unrelated to the signature seam tightening edits (error is in geometry isotropy instance proof).

## Next Step

- Either (a) strengthen/generalize the theorem-critical signature bridge beyond the current shift realization, or (b) proceed with GR/QFT adapters using the now-explicit theorem-critical signature seam, while separately resolving the existing `RealIsotropy.Instance.Core` typecheck break.

# Continuum-Limit Requirements

Documenting the continuum-limit lane for the closure stack.

## O/R/C/S/L/P/G/F summary
O: You (lane owner) define the language for a future continuum-limit theorem.
R: Enumerate scaling parameters, limit objects, preserved invariants, and gaps in the repository that a continuum limit must bridge.
C: Docs-only; add a lane-specific note under `Docs/`.
S: Ambiguity medium; working from existing closure stack; no other lanes touch `Docs/ContinuumLimit.md`.
L: cheapest viable tier (`gpt-5.1-codex-mini`).
P: yourself as solo worker; no additional specialists.
G: Keep edits confined to this lane note; do not alter shared files. No tests.
F: Need clarity around what limit objects and invariants are already formalized.

## Continuum-Limit Theorem Ingredients
1. **Scaling parameters** – identify which discrete indices will tend to continuum objects:
   - shell depth `k` / scale in `TailCollapseProof`.
   - coarse length `m` vs. tail length `k`.
   - MDL levels `L`, Lyapunov `Δ` bounds.
2. **Limit objects** – specify the targets:
   - continuum carrier `R^n` emerging from discrete `Vec Trit`.
   - limit spectral signatures (Hecke/Monster invariants) as continuous measures.
3. **Preserved invariants** – state what must survive:
   - Lyapunov descent / MDL order.
   - cone structure `CMC.Cone` and `shiftCone`.
   - execution contract admissibility (arrow/Δ/Q).
   - RG observables (MDL, basin, signature, eigen/motif).
4. **Gaps in current repo** – note missing infrastructure:
   - no parameterized scaling record linking `m,k` to continuum coordinates.
   - no limit-level cone or quadratic (currently `shiftCone`, `shiftQuadratic` are discrete).
   - no continuum-side RG surface; currently all surfaces are finite-state.
   - projective invariants (Hecke/SSP) are tied to `Vec` states, not to a continuous spectrum.

## Current landed upgrade

The abstract bundle no longer treats the continuum lane as just a bare
`limitObservable`.

`AbstractGaugeMatterBundle.agda` now gives the continuum witness an explicit:

- limit carrier,
- scaling map into that carrier,
- limit observable map,
- limit-side MDL readout,
- limit-side cone witness,
- and compatibility obligations for observable, MDL, and cone structure.

The canonical bundle inhabits that stronger surface with the simplest honest
carrier: the transported `RGObservable` itself, obtained by scaling away the
bundle's gauge wrapper at the continuum layer.

## W1 Retargeted-Seam Boundary

`DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation`
records the current MDL/CR seam state after the repo accepted the retargeted
schedule-MDL channel by equality. The old current noncanonical carrier remains
obstructed; the remaining W1 work is a final retargeted-seam receipt plus
downstream handoff compatibility for that accepted target.

This does not prove the old carrier CR-flat, and it does not by itself supply a
continuum-limit theorem.

## Next steps
- Strengthen the current canonical continuum inhabitant beyond this first
  quotient-like carrier so the scaling map is no longer just “drop the gauge
  wrapper” on the transported finite observable.
- Connect this record to a future theorem showing that the discrete
  RG/MDL/Lorentz path converges to a nontrivial continuum carrier, not only to
  a repackaged finite witness.

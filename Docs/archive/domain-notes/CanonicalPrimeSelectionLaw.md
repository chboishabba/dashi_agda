# Canonical Prime-selection Rule (Lane 4)

This lane specifies the theorem target for the canonical prime-selection rule that underlies the Monster/prime bridge. The document stays in `Docs/` and avoids touching shared metadata.

**Objective**

Establish that the closure construction selects primes `p` that satisfy a property `P` defined entirely by the Dashi state geometry and MDL structure, without reference to external sporadic group data. Only after `P` is met may the bridge invoke any Ogg/Monster comparison.

**What `P` must look like**

1. `P` refers to the intrinsic `SSP` prime set and the `Vec15` signature extracted via `Docs/PhotonBridge.md` / `DASHI/Physics/Lorentz/Signature` modules.
2. `P` is a predicate on prime exponents such that: a) the prime appears in the `shiftPrimeEmbedding`, b) the MDL/Lyapunov orbit concentrates on that prime’s coefficient, and c) the ultrametric cone admits a nontrivial valuation drop along the projection for that prime.
3. `P` is monotonic under the existing `shiftCoarse` and `shiftExecutionAdmissible` dynamics, so the selected primes remain valid along admissible traces.

**Proof obligations before Monster comparison**

- `PrimeStability`: show `P` is preserved by `shiftCoarse` and `ShiftStep` (`shiftCoarseStep-commute` plus the `shiftCoarse-idem` lemma provide the skeleton).
- `PrimeWitness`: produce an explicit `Vec15` coordinate witness for the prime satisfying `P`, built from `shiftPrimeEmbedding` and `shiftDeltaEigenProfile`.
- `PrimeInvariance`: prove the MDL value for the prime decreases or stays fixed under the coarse evolution, ensuring the selection is meaningful rather than accidental noise.
- `PrimeIsolation`: demonstrate that any other prime falling outside `P` either loses volume under the MDL descent or violates the cone bound, keeping the selection canonical.

Only after these obligations are proved may downstream notes or modules compare the resulting prime selection with the Monster’s Ogg data.

## Current implementation boundary

The repo now has a lightweight bridge surface in
`DASHI/Physics/Closure/CanonicalPrimeSelectionBridge.agda`.
That module already packages the closure-side pieces that are truly landed:

- `PrimeWitness` on the current 15-lane carrier;
- coarse/step commutation lifted to the transported prime embedding;
- coarse/step commutation lifted to the transported Hecke signature;
- the current lower-bound bridge
  `illegalCount_chamber <= forcedStableCount_hist`.

The stronger clauses remain explicit targets there rather than hidden
assumptions:

- `PrimeInvarianceTarget` for the MDL-side concentration law;
- `PrimeIsolationTarget` for the full non-accidental cone/isolation reading.

On the runtime side,
`scripts/check_canonical_prime_selection_bridge.py`
provides the matching cheap subset/support check on a
`MoonshinePrimeState` JSON payload using the same canonical 15-prime basis.

The next light theorem layer is now split out into
`DASHI/Physics/Closure/CanonicalPrimeInvariance.agda`.
That module stays at support level rather than whole-vector equality:

- it proves support transport across the already-landed
  coarse/step commutation for the transported prime embedding;
- it already proves the current support-level no-growth statement on the
  present bridge surface;
- it keeps the same statement as an explicit named theorem surface
  (`primeSupport-no-growth-target`) phrased against the existing
  execution admissibility boundary rather than a new acceptance notion.

So the current selection gap is now sharply localized:
transport of prime support is landed;
support-level no-growth is landed on the current witness surface;
the remaining open work is the stronger MDL concentration / isolation story
beyond this support-level theorem.

The next light layer above support is now explicit in
`DASHI/Physics/Closure/CanonicalPrimeConcentration.agda`.
That module does not pretend the full selection theorem is solved.
Instead it introduces the stronger exponent-level notion that support could
not express:

- `PrimeWeight x p` for the canonical SSP coordinate weight;
- `PrimeDominates x p` for coordinatewise dominance on that 15-prime carrier;
- `PrimeConcentrated x p` for selected-and-dominant primes.

What is already landed there is still transport-level:

- prime weight transport across the existing coarse/step commutation law.

What remains explicit target surface there:

- existence of a concentrated prime at each state;
- no-loss / concentration preservation under admissible descent.

On the runtime side,
`scripts/check_canonical_prime_concentration.py`
now exposes the matching cheap dominant-prime check on a
`MoonshinePrimeState` JSON payload.

The next thin control surface is now explicit in
`DASHI/Physics/Closure/CanonicalPrimeSelector.agda`.
That module now lands a concrete finite selector on the canonical 15-prime
carrier and proves selector soundness. The selection rule is:

- highest exponent;
- lowest prime on ties.

The remaining theorem boundary is now:

- `selectPrime : ShiftContractState -> SSP`;
- `selector-sound`:
  the selected prime is actually concentrated;
- `selector-no-loss-target`:
  admissible descent does not lose the selected prime;
- `selector-step-coarse-target`:
  selector output commutes with the current coarse/step schedule.

The matching runtime helper
`scripts/select_canonical_prime.py`
implements the same explicit selector rule as the Agda surface.

For the still-open selector commutation claim, the cheap runtime probe is now
`scripts/check_selector_step_coarse.py`.
It does not prove the theorem. It compares two concrete
`MoonshinePrimeState` payloads already interpreted as
`coarse(step(x))` and `step(coarse(x))`, then checks whether the explicit
selector returns the same prime and selected weight on both sides.
So the Python layer can now quickly find a counterexample or provide bounded
positive evidence before any renewed Agda attempt.

The first repo-native way to materialize that probe bundle is now
`scripts/build_selector_step_coarse_bundle.py`.
It reuses the existing Agda-backed orientation-prime adapter from
`scripts/moonshine_prime_from_twined_trace_shift.py` and emits the required
`coarse_step` / `step_coarse` JSON shape directly.
This is intentionally a bridge-aligned runtime probe, not a full independent
evaluator of the live `shiftCoarse` / `shiftStep` schedule.

# J369 finite-field and transition atlas — 2026-10-07

This tranche turns the PR #1053 finite-field ticket and graph request into deterministic numerical outputs plus exact source-side recognition boundaries. It does **not** use generated imagery and does not promote cardinality coincidences to semantic identity.

## Reproducible generators

```bash
python3 scripts/j369_field_transition_atlas.py --outdir /tmp/j369-field-atlas
python3 scripts/j369_kernel_field_recognition.py --output /tmp/kernelFieldRecognition.json
python3 scripts/j369_maxcut_runtime_receipt.py --output /tmp/OggSSPMaxCutRuntimeGenerated.agda
./scripts/check_j369_field_transition_atlas.sh
```

The checker runs both Python test suites, regenerates the committed CSV/JSON certificates and both generated Agda receipts, and diffs them byte-for-byte.

## Field-bracket results

All 16 authoritative carrier rows are regenerated. Important exact numerical hits include

```text
196817 < 196830 < 196831,  196831 prime,
196830 = |GF(196831)*|,
80 = |GF(81)*|,
810 = |GF(811)*|.
```

The Frobenius-orbit hypotheses

```text
3  = orbits(GF(4)/GF(2))
6  = orbits(GF(9)/GF(3)) = orbits(GF(16)/GF(2))
10 = orbits(GF(16)/GF(4))
15 = orbits(GF(25)/GF(5))
24 = orbits(GF(81)/GF(3)) = orbits(GF(64)/GF(4))
```

are verified numerically. The two distinct realizations of 24 remain an explicit counterexample to orbit-count uniqueness.

## K4/K5/K6: F3 structure and selected fields

`OggSSPTriadicKernelF3LinearExact.agda` source-writes the coordinate `F3` operations on the existing `TriadicPAdicCodec.Kernel d` carrier with

```text
zer = 0, pos = 1, neg = 2 = -1.
```

The source proves the additive group laws, scalar identity/zero, both distributivity laws, scalar associativity, and

```text
scale(-1) = existing invertKernel.
```

The runtime recognizer exhaustively verifies selected irreducible polynomial presentations of `GF(3^4)`, `GF(3^5)`, and `GF(3^6)`. Every nonzero element has an inverse and primitive elements have orders

```text
80, 242, 728.
```

The Frobenius profiles are

```text
GF(81):  3 fixed + 3 two-cycles + 18 four-cycles
GF(243): 3 fixed + 48 five-cycles
GF(729): 3 fixed + 3 two-cycles + 8 three-cycles + 116 six-cycles.
```

For K4, the selected `GF(9)` subfield is exactly

```text
(a,b) |-> (a,b,-b,0),
```

which equals the `x^9=x` fixed set and is closed under the selected addition and multiplication. The naive prefix plane `(a,b,0,0)` is not that subfield.

## Existing Heisenberg action is welded to kernel addition

The repo already owns `X6 = F3^6`, six coordinate translations, and the exact chart

```text
X6 <-> Kernel 6.
```

`OggSSPKernelHeisenbergAdditiveIntertwinerExact.agda` proves that each old Heisenberg coordinate translation is addition of the corresponding F3 basis vector after that chart; the first four axes restrict to K4. The numerical verifier exhaustively checks all `729 * 6` K6 cases and all `81 * 4` restricted K4 cases.

## Stronger field no-go: the full standard Heisenberg structure is insufficient

The selected extension-field product is not determined by the paid additive data. Swapping the first two coordinates preserves addition and negation but changes the selected multiplication in degrees 4, 5 and 6.

The max-cut now goes further. `OggSSPHeisenbergSymplecticFieldNoGoExact.agda` applies the same coordinate swap to both halves of the existing

```text
X6 + X6*
```

Heisenberg quotient and proves:

- the X6 swap is involutive;
- X6 addition and negation are preserved;
- the actual six-coordinate `dot6` is preserved;
- the alternating `symplecticPair` is preserved;
- the actual Heisenberg central-extension `compose` law is preserved.

The deterministic numerical pass independently checks `dot6` preservation on all

```text
729 * 729 = 531441
```

X6 pairs. Yet the same X6 symmetry changes the selected `GF(3^6)` multiplication. Therefore **the whole currently paid standard finite-Heisenberg/symplectic structure cannot canonically select that field product**. A future positive field-recognition theorem must use richer prior DASHI action data that breaks this symmetry; more additive/Heisenberg computation cannot close the gap.

## The real 1,330-state legacy graph

`FRACTRANSSPTransitionExact.firstEnabledStep` on the nonnegative four-coordinate mass-18 slice has

```text
C(21,3) = 1330
```

states and 1,330 directed edges. This matches the supplied browser screenshot's node/edge counts but not its displacement statistic. The deterministic 37-column embedding gives 233 displacement vectors, and scanning widths `2..200` finds no 12-vector realization; the minimum is 196 at widths 173 and 189. Same-graph recognition is therefore rejected.

## Full signed-weave execution: semantic core now reconstructed

`SignedSSPWeaveProgramMachineExact.agda` gives a total program-counter machine over the existing `WeaveInstruction` / `applyInstruction` semantics.

`SignedSSPWeaveInstructionTraceExact.agda` then retains the exact executed instruction trace, so prime identity is no longer lost by the aggregate `WeaveEffect`. In particular the canonical virtual program retains exactly

```text
+59, -7, invariant-unit.
```

`SignedSSPWeaveSemanticCoreReplayExact.agda` goes further and replays arbitrary instruction streams into:

- the full fifteen-lane signed valuation;
- the invariant-unit count.

The canonical virtual program is proved pointwise to recover `virtualFiftyThreeValuation`, and the canonical geometric program is proved pointwise to recover the zero valuation. The Python receipt independently checks the same replay.

`SignedSSPWeaveCanonicalProjectionExact.agda` closes the rich-state projection for both existing canonical 53 programs.

## Only metadata dynamics remain for the arbitrary full rich graph

`SignedSSPWeaveRichMetadataCompilerExact.agda` isolates the genuinely missing data in one record:

```text
RichMetadataDynamics
```

containing only the dynamics for

- `address369`;
- `zeroApproachResidual`;
- `programLength`;
- `executionLength`;
- `normalFormLength`;
- `residualWitnessLength`.

Given that record, the repo now compiles a total rich program machine and its `SignedSSPExecutionState` projection definitionally. No additional scheduler, valuation, prime-identity, or invariant-unit socket remains.

The acquisition search also found useful prior pieces:

- `FRACTRANSSPTransitionExact` already proves legacy prime transport preserves the canonical 3/6/9 address;
- successful legacy prime transport records `Zero.fromPositive` residual direction;
- `SelfIndexingHyperfabricTetrationExact` already owns the typed program/execution/normal/residual complexity carrier.

`SignedSSPWeaveMetadataAcquisitionFrontierExact.agda` records those facts. The repo does **not** currently contain a general `WeaveInstruction -> FRACTRANRule` map, an address semantics for `refineAt369`, or per-instruction description-length dynamics, so those legacy pieces cannot honestly be promoted to a full arbitrary metadata policy.

## Current max-cut

Paid:

- deterministic T1–T6 field-bracket/candidate generation;
- explicit F3 vector-space structure on K4/K5/K6;
- source-level `-1 = invertKernel` seam;
- existing Heisenberg translations intertwined with F3 addition;
- selected finite-field multiplication, inverses, primitive elements, Frobenius profiles;
- selected `GF(3) < GF(9) < GF(81)` object maps;
- an exact no-go showing the full current finite-Heisenberg/symplectic structure does not select the chosen K6 field multiplication;
- the real 1,330-state legacy transition graph and 12-vector falsifier;
- total signed-weave program-counter machine;
- exact executed trace with prime identity;
- arbitrary-program fifteen-lane valuation + invariant-unit replay;
- exact rich projections for both canonical 53 programs;
- total arbitrary rich-state compiler conditional only on `RichMetadataDynamics`.

Still open:

1. **Field recognition:** an independently existing richer DASHI action that breaks the proved Heisenberg symmetry and canonically determines multiplication/Frobenius, followed by the remaining action/orbit/stabilizer recognition contract; or a stronger no-go for any additional candidate action family.
2. **Full arbitrary signed graph:** source the remaining `RichMetadataDynamics` (address/residual/length policy). Existing legacy address/residual and hyperfabric complexity owners are partial inputs, but no exact compiler from general `WeaveInstruction` is currently present.
3. **Compiler gate:** exact-head Agda typechecking of the new owners in an environment with Agda installed.

The numerical checks for the strengthened cut pass locally, including exhaustive field inverses/orbits, the `GF(9)` subfield, 531,441 X6 dot-pair preservation checks, signed semantic-core replay, and the 1,330-state displacement scan. Agda is not installed in the current execution environment, so no local Agda compiler-success claim is made.

# J369 finite-field and transition atlas — 2026-10-07

This tranche turns the PR #1053 finite-field ticket and graph request into deterministic numerical outputs plus exact source-side recognition boundaries. It intentionally does **not** use generated imagery and does not promote cardinality coincidences to semantic identity.

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

are verified numerically. The two distinct realizations of 24 are retained as a direct counterexample to orbit-count uniqueness.

## K4/K5/K6: F3 structure and selected fields

`OggSSPTriadicKernelF3LinearExact.agda` source-writes the coordinate `F3` operations on the existing `TriadicPAdicCodec.Kernel d` carrier with

```text
zer = 0, pos = 1, neg = 2 = -1.
```

The source proves the additive group laws, scalar identity/zero, both distributivity laws, scalar associativity, and

```text
scale(-1) = existing invertKernel.
```

The runtime field recognizer then exhaustively verifies selected irreducible polynomial presentations of `GF(3^4)`, `GF(3^5)`, and `GF(3^6)`. Every nonzero element has an inverse and primitive elements have exact orders

```text
80, 242, 728.
```

Frobenius profiles are

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

## Existing Heisenberg action now welded to kernel addition

The repo already owns `X6 = F3^6`, six coordinate translations, and an exact two-sided chart

```text
X6 <-> Kernel 6.
```

`OggSSPKernelHeisenbergAdditiveIntertwinerExact.agda` proves that each old Heisenberg coordinate translation is exactly addition of the corresponding F3 basis vector after the chart. The first four axes restrict to the canonical K4 slice. This independently anchors the additive structure to prior DASHI action semantics rather than merely to the selected field model.

The numerical verifier exhaustively checks all `729 * 6` K6 translation cases and the `81 * 4` K4 restricted cases.

## Explicit non-canonicity of the selected multiplication

The paid additive/negation structure still does **not** determine a unique extension-field product. Swapping the first two coordinates is an exact source-level automorphism of K4 addition and existing inversion. At runtime the same coordinate swap preserves addition and negation in degrees 4,5,6, but conjugating the selected multiplication through it changes the product in every degree.

For K4 one witness is

```text
a = b = (0,0,0,1)
original product        = (0,1,2,1)
swap-conjugated product = (1,0,2,1).
```

Analogous explicit witnesses are recorded for K5 and K6 in `kernelFieldRecognition.json`.

Therefore the already-paid additive / global-negation data cannot by itself select the chosen multiplication. This does **not** prove that no richer existing DASHI action can select one; `OggSSPTriadicKernelCanonicalFieldActionFrontierExact.agda` isolates exactly that remaining richer-action socket.

## The real 1,330-state legacy graph

`FRACTRANSSPTransitionExact.firstEnabledStep` on the nonnegative four-coordinate mass-18 slice has

```text
C(21,3) = 1330
```

states and, because the step is total on the slice, exactly 1,330 directed edges.

This matches the supplied browser screenshot's node/edge counts but not its displacement statistic. The deterministic 37-column embedding gives 233 displacement vectors. Exhaustively scanning all row-major widths `2..200` finds no 12-vector realization; the minimum is 196 at widths 173 and 189. Same-graph recognition is therefore rejected.

## Full signed-weave execution: scheduler paid, projection still open

`SignedSSPFRACTRANWeaveExact` already owns the fifteen-lane signed valuation carrier and the weave instruction language. The summary record `SignedSSPExecutionState`, however, stores only aggregate lengths and does **not** retain the remaining instruction list, so it cannot determine a unique next instruction by itself.

`SignedSSPWeaveProgramMachineExact.agda` now constructs the maximal canonical executable state:

```text
ProgramMachineState = remaining program + accumulated WeaveEffect.
```

Its total step pops the first instruction and uses the pre-existing `applyInstruction`; the halted state is a fixed point. The machine is proved to agree with existing `executeProgram`, and both canonical 53 programs terminate with the existing canonical final effects.

The remaining graph seam is now narrower than “find a scheduler.” `WeaveEffect` counts prime introductions but does not retain which prime was introduced, while `SignedSSPExecutionState` additionally carries address, zero-residual direction, and length metadata. `ProgramMachineToSignedStateProjection` is the exact missing information-preserving bridge.

## Current max-cut

Paid:

- deterministic T1–T6 field-bracket/candidate generation;
- explicit F3 vector-space structure on K4/K5/K6;
- source-level `-1 = invertKernel` seam;
- existing Heisenberg translations intertwined with F3 addition;
- selected finite-field multiplication, inverses, primitive elements, Frobenius profiles;
- selected `GF(3) < GF(9) < GF(81)` object maps;
- explicit runtime/source evidence that additive/negation structure does not select the chosen multiplication;
- real 1,330-state legacy transition graph and the 12-vector falsifier;
- canonical total program-counter machine for the full signed weave language.

Still open:

1. a richer independently existing DASHI action that canonically determines multiplication/Frobenius on K4/K5/K6, or an exact no-go for every candidate action family;
2. full action/orbit/stabilizer recognition once such an action is supplied;
3. the information-preserving `ProgramMachineState -> SignedSSPExecutionState` projection, or a proof that the summary type is intentionally too coarse for such a projection;
4. generation of the full rich fifteen-lane graph only after that bridge is paid;
5. exact-head Agda typechecking in an environment with Agda installed.

Agda is not installed in the current execution environment, so no local compiler-success claim is made for the new Agda owners.

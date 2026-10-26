# J369 finite-field and transition atlas — 2026-10-07

This tranche turns the PR #1053 finite-field ticket and graph request into deterministic numerical outputs plus exact source-side recognition boundaries. It does **not** use generated imagery and does not promote cardinality coincidences to semantic identity.

## Reproducible generators

```bash
python3 scripts/j369_field_transition_atlas.py --outdir /tmp/j369-field-atlas
python3 scripts/j369_kernel_field_recognition.py --output /tmp/kernelFieldRecognition.json
python3 scripts/j369_maxcut_runtime_receipt.py --output /tmp/OggSSPMaxCutRuntimeGenerated.agda
./scripts/check_j369_field_transition_atlas.sh
```

The checker runs both Python test suites, regenerates the committed CSV/JSON certificates and generated Agda receipts, and diffs them byte-for-byte.

## Finite-field atlas and selected models

All sixteen carrier rows are regenerated. Exact numerical hits include

```text
196817 < 196830 < 196831, 196831 prime,
196830 = |GF(196831)*|,
80 = |GF(81)*|,
810 = |GF(811)*|.
```

The Frobenius-orbit hypotheses for 3, 6, 10, 15 and 24 are checked numerically; the two distinct 24-orbit realizations remain an explicit counterexample to orbit-count uniqueness.

`OggSSPTriadicKernelF3LinearExact.agda` source-writes the F3 vector-space operations on the existing `TriadicPAdicCodec.Kernel d` carrier and proves `scale(-1) = invertKernel`. Selected coordinate presentations of `GF(3^4)`, `GF(3^5)` and `GF(3^6)` are exhaustively verified: every nonzero element has an inverse and primitive multiplicative orders are `80, 242, 728`.

For K4 the selected `GF(9)` subfield is exactly

```text
(a,b) |-> (a,b,-b,0),
```

which equals the `x^9=x` fixed set. The naive prefix plane is false.

## Existing Heisenberg action and the field no-go

The existing `X6 <-> Kernel6` chart and six finite-Heisenberg translations are exactly intertwined with F3 basis addition; the first four axes restrict to K4.

`OggSSPHeisenbergSymplecticFieldNoGoExact.agda` proves the stronger obstruction. Swapping coordinates 0 and 1 simultaneously in translation and modulation halves preserves:

- X6 addition and negation;
- the actual `dot6` pairing;
- the alternating symplectic form;
- the actual finite-Heisenberg central-extension composition.

The same symmetry changes the selected `GF(3^6)` multiplication. The numerical verifier independently checks `dot6` preservation on all `729^2 = 531441` ordered X6 pairs. Therefore the currently paid standard finite-Heisenberg/symplectic structure does **not** canonically select the chosen `GF(729)` product.

## Richer-action acquisition audit

`OggSSPKernelFieldActionAcquisitionFrontierExact.agda` now audits the plausible stronger lanes rather than leaving a generic field-action socket.

- **Rank-one Weil/elliptic lane:** the repo-native axis-0 Heisenberg embedding and Frobenius-type reflection exist, but the actual elliptic `E(F4)[3]` transport and Weil-pairing transport remain unpaid.
- **Monster/shortest-3B lane:** `ActualMonster3BActionRecognition` is not an independent leaf. `Trialectic369Shortest3BActionSourceBridgeExact` compiles it from `Shortest3BFrontierSource`. The genuine upstream source seam is `Shortest3BBase369CandidateSource`, which is currently uninhabited and requires the exact selected literal 3B kernel attachment plus a same-literal Base369 recognition candidate.
- **Selected-3B linear lane:** the canonical linear core is a large selected constituent/Hom-space route, not an `X6 -> X6` endomorphism. Its canonical core and action intertwiner remain uninhabited; the projected route separately lacks the actual constituent retraction and projected-action equation. No X6-typed operator is exported by this stack.
- **Exceptional F4/E6 lane:** the Albert/Freudenthal owners expose dimensions and same-action interfaces but do not identify the Monster residual/action with those exceptional carriers.

Thus no independently owned six-dimensional operator has been found which both breaks the proved coordinate-swap symmetry and can serve as a degree-six field generator. The field lane is now an **acquisition theorem**, not an arithmetic/representation-construction problem.

## Numerical transition graph

`FRACTRANSSPTransitionExact.firstEnabledStep` on the nonnegative four-coordinate mass-18 slice has exactly

```text
C(21,3) = 1330 nodes
1330 directed edges.
```

This matches the supplied browser screenshot's node/edge counts but not its displacement statistic. The deterministic 37-column embedding has 233 displacement vectors; scanning widths `2..200` finds no 12-vector realization and a minimum of 196 at widths 173 and 189. Same-graph recognition is rejected.

## Full signed weave: semantic core and lengths now reconstructed

The full fifteen-lane lane now has:

1. `SignedSSPWeaveProgramMachineExact.agda`: total program-counter machine over existing `WeaveInstruction/applyInstruction` semantics.
2. `SignedSSPWeaveInstructionTraceExact.agda`: executed trace retaining prime identity.
3. `SignedSSPWeaveSemanticCoreReplayExact.agda`: arbitrary-program replay of the full signed valuation and invariant-unit count.
4. `SignedSSPWeaveCanonicalProjectionExact.agda`: exact rich-state projections for both existing canonical 53 programs.
5. `SignedSSPWeaveRichMetadataCompilerExact.agda`: total rich-state compiler given metadata dynamics.
6. `SignedSSPWeaveDerivedLengthDynamicsExact.agda`: generic derivation of program, execution and normal-form lengths.

The derived execution cost is

```text
buildSixByNineFibre       -> 54
removeInvariantMode       -> 0
introducePrime            -> 1
introduceInversePrime     -> 1
introduceInvariantUnit    -> 1
refineAt369               -> 1
```

and reproduces the existing canonical length triples exactly:

```text
virtual 53 : program/execution/normal = 3/3/3
geometry 53: program/execution/normal = 2/54/2.
```

So the full arbitrary rich graph no longer depends on scheduler, prime identity, valuation semantics, invariant-unit semantics, program length, execution length or normal-form length.

## Residual graph-metadata acquisition frontier

Only three arbitrary-program metadata laws remain:

```text
address369
zeroApproachResidual
residualWitnessLength
```

`SignedSSPWeaveMetadataAcquisitionFrontierExact.agda` cross-pollinates the closest prior owners:

- legacy FRACTRAN prime transport preserves its 3/6/9 address;
- successful legacy transport records `fromPositive` residual direction;
- the hyperfabric owner provides the residual-witness complexity carrier.

But no general `WeaveInstruction -> FRACTRANRule` compiler exists; `refineAt369` has no source-owned address update beyond its aggregate counter; and no general per-instruction residual-witness-length law exists. `FibreMachineFoundation369Exact` additionally proves that the 369 address is an observer coordinate distinct from execution semantics, so deriving metadata from aggregate execution counters would be an invalid collapse.

## Current honest max-cut

Paid:

- deterministic T1–T6 field atlas and real numerical plots;
- F3 vector-space structure on K4/K5/K6;
- selected field models, inverses, primitive orders, Frobenius profiles and chosen K4 subfield map;
- exact Heisenberg/F3-addition weld;
- exact no-go for extracting the selected K6 multiplication from the full currently paid finite-Heisenberg/symplectic structure;
- audited rank-one Weil, shortest-3B/Monster, selected-3B linear and exceptional F4/E6 richer-action lanes;
- real 1330-state legacy graph and 12-vector falsifier;
- total fifteen-lane program machine, prime-preserving trace and arbitrary semantic-core replay;
- generic program/execution/normal-form length dynamics;
- exact rich projections for both canonical 53 programs;
- total arbitrary rich-state compiler conditional only on the three residual metadata laws above.

Remaining mathematical seams:

1. **Field recognition acquisition:** supply a source-owned `X6 -> X6` F3-linear operator that breaks the coordinate-swap no-go and has an independently checked degree-six field-generator/minimal-polynomial receipt. The current obvious richer action families do not supply such an operator. Once acquired, pay the action/orbit/stabilizer recognition contract against `GF(729)`.
2. **Arbitrary full signed graph acquisition:** supply source semantics for `address369`, `zeroApproachResidual`, and `residualWitnessLength` under general `WeaveInstruction`. Once supplied, the full rich fifteen-lane graph is compiler output.
3. **Compiler gate:** exact-head Agda typechecking of all new source owners in an environment with Agda installed.

Fresh finite verification for this cut includes exhaustive selected-field inverse/orbit checks, the `GF(9)` subfield, all 531441 X6 dot-pair preservation cases, canonical signed semantic-core replay, derived `3/3/3` and `2/54/2` length receipts, and the 1330-state displacement scan. Agda is not installed in the current execution environment, so no local Agda compiler-success claim is made.

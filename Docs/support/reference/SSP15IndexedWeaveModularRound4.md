# SSP15 Indexed Weave and Modular Fibration — Round 4

## Purpose

This tranche replaces the loose unindexed loom reading with a law-bearing indexed family and cross-pollinates it with the existing SSP15, `T^2 ⊔ {j}`, modular coarse/fine, Moonshine trace, Jacquard, helical, layered-binding and distributed-braid surfaces.

It continues `agent/ssp15-j-coarse-fine-round3` and preserves that branch's distinction between the existing frequency-scale model

```text
jCoarseFrequency = 3^2
jFineFrequency   = 3^9
jAbsolute        = 3^11
```

and the new address-depth model

```text
jCoarseAddressDepth = 1
jFineAddressDepth   = 10
jAbsoluteDepth      = 11.
```

These are different quantities and are not identified.

## Lawful indexed weave

`DASHI.Core.IndexedWeaveHyperfabricExact` defines a weave over an indexed family `State : Index -> Set`. Paths are typed by source and target, compose associatively, transport states, and retain a target-indexed residual. Identity and composition laws are fields of the structure rather than prose.

`DASHI.Biology.SSPIndexedWeaveHyperfabricExact` gives a complete finite instance over all fifteen `SSPPrime` lanes. Reverse parity flips the balanced lane state, two reversals preserve every state, and inverse transport retains an inverse residual.

## Modular address fibration

`DASHI.Biology.ModularCoarseFineAddressFibrationExact` uses the ten-state `DecimalCompletionState ~= T^2 ⊔ {j}` as the fine-sector index. A fine address is a ternary field over those ten sectors:

```text
FineAddress = FineSector -> BalancedTrit.
```

One coarse ternary coordinate and ten fine ternary coordinates yield:

```text
1 + 10 = 11
3^11 = 3^1 * 3^10.
```

The Fricke-style finite complement acts by precomposition with the proved ten-sector involution and is pointwise involutive. Every SSP lane indexes a fine fibre over the same coarse address type. The module does not claim to reconstruct `X_0(p)`, prove genus zero, or construct a Hauptmodul.

`DASHI.Biology.SSPIndexedWeaveModularIntegrationExact` forms the actual cross-product carrier. Its index is

```text
SSPPrime x CoarseAddress
```

and its state is

```text
FineAddress x laneState.
```

Typed paths can change the SSP lane only while preserving the coarse base. Fine data survive lane transport, while the lane state follows the proved parity action.

## Layered binding

`DASHI.Biology.LayeredBindingSystemExact` separates material presence, binding-medium presence and depth continuity. It proves that an intact state and a severed-but-bound state are distinct while producing the same coarse QC observation. An eight-superply finite model repeats the distinguished boundary defect independently of SSP lane.

This is neutral projection mathematics. It is not a materials or safety theorem.

## Jacquard semantics

`DASHI.Computation.JacquardOperationalSemanticsExact` implements:

```text
program -> lift schedule -> crossing rows -> crossing word.
```

The compiler-correctness theorem proves direct execution equals execution of the compiled lift schedule.

## Helical monodromy

`DASHI.Topology.HelicalWeaveMappingTorusExact` separates cylindrical fabric topology from helical production trajectory. The phase monodromy is nontrivial and has exact order three. Three production steps return to the same phase while advancing the production round by three.

Order-three closure is not promoted to a physical generation assignment.

## Distributed braid gluing

`DASHI.Reasoning.DistributedBraidGluingExact` uses the four even-parity sections of three Boolean local holders. For every holder there are two distinct coherent global sections with the same local observation, proving that no single owner determines the communal object. Cyclic role rotation is observation-equivariant and has order three.

## Klein-quartic factor symmetry

`DASHI.Physics.Closure.KleinQuarticGenerationSymmetryExact` constructs two transpositions of a three-factor carrier and proves there is no factor fixed by both. Three factors therefore do not canonically select a generation while full permutation symmetry remains unbroken. The existing Klein-quartic receipt's open symmetry-breaking status and blocked CKM promotion are preserved.

## Moonshine trace fibre

`DASHI.Physics.Moonshine.MoonshineTraceIndexedWeaveExact` is a bounded finite proxy with no postulates. Two distinct hidden states share one trace profile while carrying different hidden tags. Trace fibres form an indexed weave under equality transport. No actual Monster representation or McKay–Thompson equality is claimed.

## KAM boundary

`DASHI.Dynamics.KAMHypothesisCoreExact` proves that the finite order-three helical rotation has a resonance witness. It cannot itself serve as a nonreturning/quasiperiodic KAM frequency. Genuine KAM data are separated into near-integrability, twist nondegeneracy, Diophantine and invariant-torus witnesses.

Primary source:

- Jürgen Pöschel, *Integrability of Hamiltonian Systems on Cantor Sets*, Communications on Pure and Applied Mathematics 35 (1982), 653–696. DOI `10.1002/cpa.3160350504`.

## Substance audit

`scripts/classify_agda_substance.py` emits deterministic JSON metrics for each selected Agda source: postulates, holes, unsafe escapes, executable equations, theorem signatures, constructor/refl bodies, Boolean governance fields and strings. It classifies observable implementation shape without pretending to decide mathematical truth.

## Validation

```bash
bash scripts/check_ssp15_indexed_weave_modular_round4.sh
```

The checker:

1. runs the complete Round-3 chain;
2. rejects holes, postulates and trust escapes in every new Agda source;
3. verifies required theorem markers;
4. self-tests and runs the substance classifier with `--fail-on-external`;
5. checks both the cumulative validation root and the top-level aggregate with pinned Agda 2.9.

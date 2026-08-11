# SSP15 Indexed Weave and Modular Fibration — Round 4

## Purpose

This tranche replaces the loose unindexed loom reading with a law-bearing indexed family and then connects that kernel to the repository's existing SSP hyperfibre atlas, `T^2 ⊔ {j}` carrier, modular coarse/fine address model, Moonshine trace fibres, Jacquard execution, helical monodromy, layered binding and distributed braid surfaces.

It continues `agent/ssp15-j-coarse-fine-round3` and preserves a necessary distinction between the existing frequency-scale model

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

`DASHI.Core.IndexedWeaveHyperfabricExact` defines a weave over an indexed family

```text
State : Index -> Set.
```

Paths are indexed by source and target, compose associatively, transport states functorially, and return a residual in the target fibre. Identity transport preserves the residual already carried by a state; it does not force every hidden residual to collapse to zero.

The existing `DASHI.Biology.SSPHyperfibreSymmetryTowerExact` already supplied the important indexed content:

```text
Fibre    : SSPPrime -> Set
Path     : SSPPrime -> SSPPrime -> Set
Residual : SSPPrime -> Set.
```

What it lacked were category/action laws. `DASHI.Biology.SSPIndexedWeaveHyperfabricExact` supplies those laws without replacing the existing orientation vocabulary. Its path monoid uses the existing three values:

```text
mediatedOrientation
forwardOrientation
inverseOrientation.
```

`mediatedOrientation` is the global path identity. The nontrivial component obeys

```text
forward * forward = forward
forward * inverse = inverse
inverse * forward = inverse
inverse * inverse = forward.
```

All 27 associativity cases and the transport-action cases are proved by finite elimination. Two inverse paths preserve every lane state, compose to `forwardOrientation`, and retain their inverse residual.

`DASHI.Biology.SSPHyperfibreLawfulUpgradeExact` maps every legacy `LanePath` into this lawful weave and proves exact agreement of both transport and residual. The upgrade therefore extends the existing hyperfabric rather than creating a competing parallel carrier.

## Modular coarse/fine address fibration

`DASHI.Biology.ModularCoarseFineAddressFibrationExact` uses the ten-state `DecimalCompletionState ≃ T^2 ⊔ {j}` as the fine-sector index. A fine address is the indexed family

```text
FineAddress = FineSector -> BalancedTrit.
```

The module constructs an explicit ten-field representation `FineAddress10`, together with tabulation and lookup maps. Lookup after tabulation is proved pointwise, and tabulation after lookup is proved by record elimination. Thus “ten fine coordinates” is not merely a count: it has an exact finite representation.

One coarse ternary coordinate and ten fine ternary coordinates yield

```text
1 + 10 = 11
3^11 = 3^1 * 3^10.
```

The same module constructs a finite Fricke-quotient analogue from the already proved complement involution:

```text
10 fine sectors
  -> 5 complement modes
  x  2 phases.
```

The finite quotient coordinate is invariant under complement. Direct and counterphase lifts are both sections, and complement exchanges them. Pullback of a fine address along complement is pointwise involutive.

This is the exact finite compression theorem used internally. It does not reconstruct `X_0(p)`, prove that `X_0^+(p)` has genus zero, or construct an analytic Hauptmodul.

Primary references recorded in the Agda header:

- Nicholas M. Katz and Barry Mazur, *Arithmetic Moduli of Elliptic Curves*. DOI `10.1515/9781400881710`.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*. DOI `10.1016/j.jnt.2015.06.001`.

## SSP-indexed modular integration

`DASHI.Biology.SSPIndexedWeaveModularIntegrationExact` forms the cross-pollinated carrier

```text
Index = SSPPrime x CoarseAddress
State = FineAddress x laneState.
```

A typed path may change the SSP lane only while carrying a proof that the coarse base is unchanged. Fine addresses survive lane transport, the visible lane state follows the lawful three-orientation action, and inverse paths retain inverse residuals in the target index.

## Layered binding

`DASHI.Biology.LayeredBindingSystemExact` separates:

```text
material presence
binding-medium presence
depth continuity.
```

It proves that an intact state and a severed-but-bound state are distinct while producing the same coarse QC observation. An eight-superply finite model repeats the distinguished fifteenth-ply boundary defect independently of SSP lane. Interior and boundary states can therefore be observationally identical at the coarse projection while remaining unequal in the carrier.

This is neutral projection mathematics. It is not a materials or safety theorem.

## Jacquard operational semantics

`DASHI.Computation.JacquardOperationalSemanticsExact` implements

```text
pattern program
  -> lift-mask schedule
  -> crossing rows
  -> per-warp crossing word.
```

The compiler-correctness theorem proves that direct program execution and execution of the compiled lift schedule agree exactly.

`DASHI.Computation.JacquardHelicalWeaveBridgeExact` then compiles the helical three-phase orbit into a concrete three-warp, three-row Jacquard schedule. Each row lifts exactly one warp; the three exact crossing words are proved by reduction. Rotating the initial phase cyclically permutes the generated rows.

## Helical monodromy and shared C3 structure

`DASHI.Topology.HelicalWeaveMappingTorusExact` separates cylindrical fabric topology from helical production trajectory. The phase monodromy is nontrivial and has exact order three. Three production steps return to the same phase while advancing the production round by three.

`DASHI.Unified.ThreePhaseCrossPollinationExact` constructs mutually inverse, rotation-equivariant maps among:

```text
helical stitch phase
<-> distributed holder role
<-> three-factor slot.
```

Each carrier is a free cyclic order-three action. This proves a common `C3` torsor shape, not a physical identity among stitches, people and Klein-quartic factors.

## Distributed braid gluing

`DASHI.Reasoning.DistributedBraidGluingExact` uses the four even-parity sections of three Boolean local holders. For every holder there are two distinct coherent global sections with the same local observation. Hence no single holder determines the communal object. Cyclic role rotation is observation-equivariant and has order three.

## Klein-quartic factor symmetry

`DASHI.Physics.Closure.KleinQuarticGenerationSymmetryExact` constructs two transpositions of a three-factor carrier and proves that no factor is fixed by both. Three factors therefore do not canonically select a generation while full permutation symmetry remains unbroken. The existing Klein-quartic receipt's open symmetry-breaking status and blocked CKM promotion are preserved.

This theorem does not reconstruct the Klein quartic, its Jacobian, its endomorphism algebra or the physical CKM map. It isolates one exact obstruction already implicit in that programme.

## Moonshine trace fibre

`DASHI.Physics.Moonshine.MoonshineTraceIndexedWeaveExact` is a bounded finite proxy with no postulates. Two distinct hidden states share one trace profile while carrying different hidden tags. Trace fibres form an indexed weave under equality transport, and identity transport retains the hidden residual rather than erasing it.

`DASHI.Physics.Moonshine.SSPMoonshineTraceFibreIntegrationExact` then forms the actual bounded product index

```text
Index = SSPPrime x TraceProfile
State = laneState x TraceFibre.
```

Paths transport the SSP lane while preserving the trace profile by equality. Residuals retain both the lane orientation and hidden trace tag. The module proves that equal observed traces remain hidden-distinct in every SSP lane and that inverse lane transport preserves the hidden trace tag.

This is a finite cross-pollination theorem. It explicitly leaves false the stronger statement that Monster symmetry supplies a canonical compatibility or identification among the fifteen Ogg-prime lanes. No actual Monster representation or McKay–Thompson trace equality is claimed.

## KAM boundary

`DASHI.Dynamics.KAMHypothesisCoreExact` proves that the finite order-three helical rotation has a resonance witness. It therefore cannot itself serve as a nonreturning or quasiperiodic KAM frequency. Genuine KAM authority is typed separately by witnesses for:

- near-integrability;
- twist/nondegeneracy;
- a Diophantine frequency;
- an invariant torus carrying that frequency.

Primary source:

- Jürgen Pöschel, *Integrability of Hamiltonian Systems on Cantor Sets*, Communications on Pure and Applied Mathematics 35 (1982), 653–696. DOI `10.1002/cpa.3160350504`.

## Substance audit

`scripts/classify_agda_substance.py` emits deterministic JSON metrics for observable source shape:

- postulates, holes and trust escapes;
- imports, data and record declarations;
- theorem signatures and executable equations;
- constructor/`refl` bodies;
- Boolean governance fields and string literals.

The classifier does not decide mathematical truth. It supports two reports:

```text
artifacts/ssp15-indexed-weave-substance.json
artifacts/cross-pollination-substance.json.
```

The first is fail-closed for the new exact tranche. The second is informational over selected legacy loom, Moonshine, Klein, DHR, CKM/Yukawa and hyperfabric surfaces, so older postulated or governance-heavy implementation shapes are measured rather than concealed.

## Validation

```bash
bash scripts/check_ssp15_indexed_weave_modular_round4.sh
```

The checker:

1. runs the complete Round-3 chain;
2. rejects holes, postulates and trust escapes in every new Agda source;
3. verifies the exact theorem and bridge markers described above;
4. self-tests the substance classifier;
5. emits both new-tranche and legacy cross-pollination audit JSON;
6. checks the cumulative validation root and top-level aggregate with pinned Agda 2.9.

A successful kernel or GitHub Actions run must still be observed before claiming validation success.
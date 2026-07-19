# Nested modular tensor lift

This bridge formalises the narrow mathematical content behind the DASHI
3/6/9 nesting discussion without promoting the surrounding physical or
biological analogies to theorems.

## Exact claims

### 9-lifting preserves the coarse ternary state

A nonary value is represented as a ternary value plus one additional ternary
refinement digit.  The projection

```text
nonaryToTri : NonaryTruth -> TriTruth
```

forgets that higher digit.  The theorem

```text
nonaryLiftPreservesCoarsePolarity
```

proves that choosing any refinement digit leaves the already-fixed lower
ternary observation unchanged.

This is the finite first step of the Hensel-style intuition: refinement adds
precision inside a fibre rather than silently changing the coarse class.
The module does not claim a general polynomial Hensel lemma.

### 6 is a CRT boundary, not another 3-adic lift

The six-state carrier is exactly represented by:

```text
Bit x TriTruth
```

where `Bit` is the mod-2 parity observation and `TriTruth` is the mod-3
observation.  `hexObserveCRT` and `hexReconstructCRT` are inverse by exhaustive
proof.

This records the disjunct identified in the formalism:

- the 9 lane refines the 3-primary component;
- the 6 lane combines coprime 2- and 3-components.

### A 19,683-state sheet is local

`Sheet369` is one function from the nine lens/time slots to nonary values.
`TensorTree` permits such a sheet to be retained as one node of a recursively
nested state carrier.  Therefore the finite sheet vocabulary is not identified
with the total recursive state space.

No claim is made that the recursive carrier has cardinality `9 tetrated to 9`,
that it forms a particular Lie group, or that biological reproduction is
characterised by nonary closure.  Those require additional structures and
proof obligations.

### 10 over 9 and 11 over 10 are frame relations

Standard arithmetic modulo 1 sends every integer to the unique residue, so
phrases such as `10 = 9 mod 1` cannot distinguish stages.  The intended DASHI
content is encoded instead as:

```text
previousFrame stage-10 = stage-9
previousFrame stage-11 = stage-10
```

Stage 11 is represented by `TensorOrderJump`, which retains mod-3, mod-6, and
mod-9 observations together with nested child sheets and an explicit proof
that the mod-9 detail preserves the mod-3 shadow.

### Aperture

`ApertureState.resolvedDepth` records how many refinement constraints are
retained.  This is explicit metadata; it is not inferred from arbitrary
mixed-radix strings.  A future p-adic module may replace this natural-number
index with a certified finite prefix or inverse-limit carrier.

## Files

- `DASHI/Foundations/NestedModularTensorLift.agda`
- `DASHI/Foundations/NestedModularTensorLiftTests.agda`

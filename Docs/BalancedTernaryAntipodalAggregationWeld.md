# Balanced ternary, antipodal fibres, 369 comparison, and aggregate loss

This note records the additional cross-pollination on PR #587. It does **not** identify geometric `-1/0/+1`, epistemic `supported/unresolved/contradicted`, Boolean truth, or accept/reject decisions merely because those carriers have related cardinalities.

## Primitive geometric carrier

The canonical SSP carrier is already typed as `-1`, `0`, `+1` by `DASHI.Foundations.SSPTritCarrier`.

`BalancedTernaryAntipodalOrbitExact` adds the strict geometric action

```text
-1 <-> +1
 0 -> 0
```

and proves it involutive. Thus zero is the unique fixed centre of the local strict-antipode action; it is not the opposing pole.

For a ternary cube the finite orbit arithmetic is

```text
3  = 1 + 1 * 2
9  = 1 + 4 * 2
27 = 1 + 13 * 2.
```

The module constructs the `9 -> 5` quotient explicitly and constructs an exact 14-class canonicalization of a 27-state ternary cube by choosing the representative whose first nonzero coordinate is positive.

Representation-theoretic calibration follows Jean-Pierre Serre, *Linear Representations of Finite Groups* (Springer, 1977), DOI `10.1007/978-1-4684-9458-7`. The finite ternary quotient itself is a DASHI construction.

## Geometric antipode is not logical negation

`BalancedTernaryOppositionEvidenceBridgeExact` instantiates the strict antipode as an `orientationReversalRole` `OppositionDescriptor` in `ClaimIndexedEvidencePolarityExact`.

Therefore the evidence fibre may record support for a declared geometric antipode, but the existing theorem

```text
orientationReversalRole != logicalNegationRole
```

blocks construction of `LogicalNegationQualified` from carrier shape alone.

So all of the following remain distinct:

```text
not supported
support for logical not-P
support for strict geometric antipode
support for algebraic inverse
support for contextual counterposition
support for lens-transformed target.
```

## Epistemic trit is not balanced-ternary zero

`EpistemicTritBalancedTernarySeparationExact` is deliberately retained. It proves that only resolved positive/negative epistemic states have the canonical `+1/-1` polarity bridge. The unresolved state can be encoded as negative, zero, or positive under three explicit total policies.

Hence

```text
balanced zero = fixed geometric centre
```

never entails

```text
epistemic unresolved = zero
```

without a declared policy.

## 3/6/9/27 comparison geometry

`TernaryComparisonSynthesisExact` already owns the comparison decomposition

```text
9 = diagonal agreement 3 + directed disagreement 6
```

and the 27-state comparison-plus-synthesis carrier. Reversal of a directed disagreement is not automatically strict inversion or contextual counterposition.

`BinaryBalancedTernaryAggregateLossExact` adds the exact premature-collapse witness:

```text
balanced comparison 9
  -> declared binary decisions 4
  -> accept count 3.
```

The two directed binary states

```text
(1,0)
(0,1)
```

remain different after the first projection but both have accept count one. Thus count/mean-style aggregation quotients out disagreement direction.

No central-limit theorem is needed for this information loss. A future probabilistic concentration theorem would operate **after** this many-to-one aggregate has already been formed and cannot by concentration alone reopen the forgotten fibre.

## The 1/2 fixed point

`RepresentationChartInvariant` already proves that `1/2`, decimal `0.5`, `50%`, `3/6`, and the stored binary-radix presentation are charts of the same invariant rational point.

`BinaryBalancedTernaryAggregateLossExact` adds only the finite complement geometry on the three distinguished Bernoulli points:

```text
0 <-> 1
1/2 -> 1/2
```

which centres as

```text
-1 <-> +1
 0 -> 0.
```

This does not claim that the half point is definitionally indecision, that binary zero is world falsity, or that an analytic logistic theorem has been constructed in this module.

## Repo-native 27^3 = 3^9 interaction/appraisal carrier

The correct three-block object was already present in `Base369InteractionAppraisalCubeExact`:

```text
base interaction cube       = 27 states
participant-A appraisal     = 27 states
participant-B appraisal     = 27 states
---------------------------------------
one-round interaction state = 27^3 = 3^9 = 19683 states.
```

`Base369InteractionAntipodalFibreExact` reuses that carrier directly rather than introducing an `EgeCarrier` duplicate.

Forgetting the strict antipodal orientation independently in each 27-state block gives

```text
27^3 -> 14^3 = 2744.
```

The orientation-forgotten base stratifies as

```text
2744 = 1 + 39 + 507 + 2197,
```

according to whether zero, one, two, or three blocks are noncentral. The corresponding fine-state accounting is

```text
19683 = 1 + 78 + 2028 + 17576,
```

with orientation fibres of sizes

```text
1, 2, 4, 8
```

respectively. The all-three-noncentral case is represented concretely by eight fine states sharing one block-orientation quotient, with at least one pair proven distinct.

A separate global antipode on all nine ternary coordinates has the different arithmetic

```text
19683 = 1 + 9841 * 2,
```

so global orientation forgetting and blockwise orientation forgetting are not the same quotient.

## Nontrivial zero fibre

The same repo-native one-round carrier supplies a literal cancellation witness.

The all-zero state and a state with base interaction `( +1, -1, 0 )` and otherwise-zero appraisal coordinates satisfy

```text
aggregateSum structuralZero = 0
aggregateSum cancellation   = 0
```

while the fine states are provably distinct.

Thus the exact invariant is

```text
projection to zero != structural zero
net balance != empty fibre
cancellation != absence.
```

This is the finite deterministic substrate behind later averaging/concentration discussions.

## Five antipodal classes are not five D4 irrep species

`TernaryNineAntipodalD4SeparationExact` keeps two nearby occurrences of the number five separate.

The ternary `3 x 3` antipodal quotient has five orbit classes. Separately, the repository's `D4IrrepKind` has five species `A1,A2,B1,B2,E`.

But the raw nine-cell D4 permutation representation is

```text
3 A1 + B1 + B2 + 2 E
```

and has no `A2`, whereas `D4SO3NineIrrepRestrictionExact` proves

```text
V4 | D4 = 2 A1 + A2 + B1 + B2 + 2 E = 1 + Reg_D4.
```

So equal count, dimension, and group vocabulary do not manufacture an intertwiner or representation identification.

The representation references already used by the source module are:

- Jean-Pierre Serre, *Linear Representations of Finite Groups*, DOI `10.1007/978-1-4684-9458-7`.
- William Fulton and Joe Harris, *Representation Theory: A First Course*, DOI `10.1007/978-1-4612-0979-9`.

## Shared non-collapse law

The resulting cross-domain spine is:

```text
operator first, "opposite" second;
zero fixed centre != negative pole;
equal carrier cardinality != equal semantics;
epistemic unresolved != balanced zero without policy;
strict antipode != contextual counterposition != logical negation;
9-state directed comparison != its 4-state binary image;
binary pair != its count;
aggregate zero != trivial fine state;
blockwise orientation quotient != global antipodal quotient;
antipodal orbit class != representation irrep species;
concentration of a coarse statistic cannot by itself reopen its fibre.
```

## Validation boundary

The changes are source/API/proof-shape reviewed against the live repository and reuse existing constructors and theorem surfaces. The execution environment does not provide an Agda executable, so this tranche does not claim a fresh kernel typecheck. No GitHub Actions or CI runs are invoked here.

# Representation, frame, radix and lifted-hypervoxel spine

## Status

This document records the typed architecture implemented by the accompanying
Agda tranche. It does not claim that SU(2), SO(3), Base369, political stages,
psychological explanations or prime-specific p-adic spaces are definitionally
the same structure. The purpose is to make valid adapters explicit while
blocking invalid collapses.

## 1. Invariant value and presentation fibre

The elementary invariant is

```text
3/6 = 1/2 = 0.5 base 10 = 0.1 base 2 = 50%.
```

These are presentations of one rational point. The repository separates:

- the invariant ratio;
- its representation;
- the chart in which it is displayed;
- the evaluation proof connecting representation to invariant;
- chart transitions that preserve evaluation.

`DASHI.Foundations.RepresentationChartInvariant` contains exact
cross-multiplication proofs and a generic `FramedAtlas` contract. Every ratio
carries a proof that its denominator is strictly positive. Every refinement
factor is likewise required to be positive, so neither an invalid denominator
nor a vacuous `0/0` refinement can be constructed.

The metacognitive lift is not "ten per cent more facts". It is

```text
x -> (x, active-frame).
```

The experience or value is preserved while the frame becomes inspectable.

## 2. Harmonic and coarse/fine readings

The ratio `3:6` reduces to `1:2`. In an appropriate frequency context this is
an octave relation; in a partition context `3/6` is half occupancy. These are
typed roles of a ratio, not meanings inherently possessed by the glyphs 3 and
6.

Scaling numerator and denominator together refines the presentation:

```text
1/2 = 2/4 = 3/6 = 50/100.
```

The partition changes while the parent-level proportion is preserved. This is
the arithmetic analogue of replacing one cubie by finer subcubies while
preserving a coarse observable.

## 3. Rank, depth and the Rubik model

Let `A` be a three-element local axis carrier.

- rank says how many local coordinates define one site;
- depth says how many recursive refinements have been applied.

The base geometry at rank `r` and depth `d` has

```text
3^(r*d)
```

leaf addresses. A rank-three depth-one object has 27 cubies; a rank-three
depth-two object has 729 leaf cubies.

A cell is a cubie relative to its parent and a cube relative to its children.
Those are scale-relative roles, not absolute ontological classes.

The implementation distinguishes three joins:

1. address join: coarse prefix plus relative fine suffix;
2. sibling assembly: all children of one parent assembled into a refined local
   object, followed by a domain-specific aggregation law;
3. cross-object join: gluing two objects along a separately supplied common
   interface.

## 4. Spatial recursion versus tetration

Repeated spatial subdivision is exponential in depth, not tetrational:

```text
site-count(r,d) = 3^(r*d).
```

The configuration space of ternary fields over those sites has

```text
3^(3^(r*d))
```

members. Tetrational growth begins when an entire configuration space is used
as the index set of the next level:

```text
h(0) = 1
h(n+1) = 3^(h(n)).
```

The code therefore keeps `siteCount`, `configurationCount` and `tower3` as
different functions.

## 5. SU(2) -> SO(3) over the recursive geometry

The strongest legitimate finite adapter is:

```text
three Lie-axis roles x two central lifts = six axis/lift presentations.
```

The axis role is not a balanced-trit coefficient sign. The binary lift is a
fibre coordinate, not another ternary geometric dimension.

The typed hierarchy is:

```text
A               : 3
A x P           : 6
A^2             : 9
A^2 x P         : 18
A^3             : 27
A^3 x P         : 54
A^4             : 81
A^4 x P         : 162.
```

`DASHI.Physics.Closure.SU2SO3369HypervoxelBridge` provides:

- a separate three-axis type;
- an axis/lift-to-`HexTruth` round trip;
- an output-axis/input-axis-to-`NonaryTruth` round trip;
- a proof-carrying two-sheet interface;
- two canonical lifts over every finite base point;
- proofs that those lifts are distinct;
- completeness showing every cover point is one of those two lifts;
- a fixed-point-free central flip exchanging the sheets;
- centre-blind and centre-sensitive operator-sheet interfaces;
- the exact cardinal receipts above.

This is an indexing and fibre grammar. It does not identify `SU(2)` with
Base6, `SO(3)` with Base3, or the p7 `C6` witness with the double cover.

## 6. Fibre parity and fields

Lift polarities compose by the two-element group law. Projection forgets the
polarity, while a centre-sensitive consumer may retain it. The implementation
distinguishes:

```text
Address x Polarity
```

which selects one lifted site, from

```text
Address -> Polarity
```

which assigns lift data over the whole geometry.

A centre-blind field can no longer be declared by a label alone. It must carry
a proof that its value is invariant under `centralFlip`. A centre-sensitive
field remains unrestricted on the lifted carrier.

`DASHI.Foundations.LiftPolarityPathComposition` proves that lift transitions
accumulated along a path compose multiplicatively and that splitting a path
into a coarse prefix and relative fine suffix factors the total lift exactly.
A Rubik-style lifted move must commute with base projection.

## 7. Right-Jacobian and Haar convention lock

The convention receipt records the right-trivialised SO(3) Jacobian as

```text
J_r(theta)
  = I
  - (1 - cos r)/r^2 [theta]_x
  + (r - sin r)/r^3 [theta]_x^2,
    r = ||theta||.
```

The receipt fixes the minus sign and denominator powers 2 and 3 so they cannot
drift downstream. The SU(2) Haar-density receipt records

```text
(sin(r/2)/(r/2))^2.
```

Both remain radius-restricted chart statements. No global injectivity of the
exponential map is claimed, and no constant-Jacobian-to-global-polynomial-
inverse implication is used.

The plaquette route prefers exact quaternion multiplication before a generic
BCH fallback. The repository does not yet claim that the resulting cubic
constant is smaller; it records that comparison as the next analytic target.

## 8. Radix point, p-adic origin and prefix metric

The radix determines place weights. The radix point determines exponent zero
and therefore the scale origin. Radices used for positional rational
presentations carry positivity proofs. A numeral can be displayed in base 10
while being read with a p-adic valuation.

The relevant prefix is not universally the typographic left prefix. It is the
prefix beginning at the chosen valuation/radix origin and extending outward.
The existing `DASHI.Geometry.SSP369Ultrametric` proves that a longer shared
origin-prefix bounds the remaining distance. The new
`RepresentationPrefixUltrametricBridge` connects its digits to the 369
refinement forest and packages a depth-three example whose addresses share the
coarse `3/6` prefix and differ at the final fine digit.

## 9. Prime lanes, 369 diagnostics and the 0..11 atlas

Ternary/369 is the minimal exemplar, not the whole ontology. A prime lane has
its own branch structure. A selected 369 address is a finite diagnostic
projection of that larger lane, and stage interpretation is a further separate
map:

```text
prime lane
  -> prime-specific depth address
  -> selected 369 signature
  -> 0..11 stage point.
```

No stage label is identified with an arithmetic value and no finite receipt is
promoted into an analytic p-adic completion.

## 10. Stage 1, 10 and 11

The decimal display `9 -> 10 -> 11` instantiates a general carry grammar.
Within the stage atlas:

- Stage 1 is a local/current-place unit role;
- Stage 10 is the unit recurring after a carry to a new place;
- Stage 11 is the carried unit together with a new local unit.

Stage 1 and Stage 10 are proved distinct as stage coordinates. They are joined
only by a `SameUnitRoleAcrossScale` witness. Stage 10 and Stage 11 are also
proved distinct. Stage 11 is a typed coarse/fine join, not merely an
unqualified narrative label.

## 11. Situated frame and mental-health boundary

`DASHI.Cognition.SituatedFrameMetacognitionBoundary` separates experienced
state from explanatory frame. Biological, psychological, clinical, social,
economic, institutional, relational and self-authored frames may overlap.

The formal claims are deliberately weaker and safer than a totalising reading:

- distress does not by itself prove that a whole system is incoherent;
- distress is not forced into a biological-defect-only frame;
- frame awareness is not a view from nowhere;
- no diagnosis or treatment authority is promoted;
- political interventions do not carry guaranteed outcomes.

Standpoint theory, subjugated knowledges, pattern-mind and material-feedback
intervention are recorded as interpretive precedents and neighbours, not as
formal equivalences or universal empirical theorems.

## 12. Logistic and primorial role separation

The logistic-map receipt distinguishes:

- `x = 1/2`, the state-coordinate critical point of the parabola;
- `r = 3`, the first period-doubling parameter;
- the period-doubling accumulation parameter near `3.5699456`;
- period-three chaos results;
- optional metaphorical stage readings.

These are not one universal `0.5` threshold.

The primorial receipt imports the existing finite implementation, records
A276086 as the primorial-base exp-function role, and proves definitionally that
A276087 is its second iterate. Claims about systemic rebirth, logistic branches
or manifolds require an additional typed interpretation map and separate
evidence.

## 13. Integration and validation

The aggregate theorem surface is:

```text
DASHI.Foundations.RepresentationHypervoxelRegression
```

It is imported by both:

- `DASHI.Foundations.SSPPrimeLane369BridgeRegression`, already on the
  `DASHI.Everything` authoritative route;
- `DASHI.Foundations.SSPPrimeLane369ConsumerRegression`, covering downstream
  consumers.

Run:

```bash
python3 scripts/check_representation_hypervoxel_spine.py
nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/RepresentationHypervoxelRegression.agda
nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/SSPPrimeLane369ConsumerRegression.agda
nix develop .# --command bash scripts/run_agda29_parallel_check.sh \
  DASHI/Everything.agda
```

The focused workflow uses the repository-approved flake-pinned checker wrapper,
disables persisted checkout credentials, and pins the wrapper's repository,
Agda and log paths for the GitHub runner.

The Python audit checks exact ratio identities, denominator/refinement
positivity surfaces, hierarchy/cardinality values, rank/depth counts, fibre
completeness, centre-blind proof carrying, path parity, carry grammar, required
theorem names and a no-hole/no-postulate surface. Only Agda kernel checking can
certify the full formal tranche.

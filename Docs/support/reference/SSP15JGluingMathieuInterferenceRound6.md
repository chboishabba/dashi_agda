# SSP15 indexed-j gluing, Eisenstein interference, and Mathieu towers — Round 6

## Purpose

This round converts the supplied `0 ~ 1 ~ 10 ~ 11`, nine-ring, Eisenstein-phase, `196884`, Mathieu-order, and divisor-lattice discussion into executable finite mathematics. It continues Round 5 and reuses its ten-sector projection, D4 nine-cell codec, C3 character evaluation, modular/Fricke interface, and pointed-phase arithmetic.

The central correction is typed rather than numerical:

```text
0_F ~ 1_J
1_J -> 10_{J/F}
11 = (1_F, 10_{J/F}).
```

`0_F` is the intrinsic zero-indexed seam. `1_J` is the external pointed object in its own one-indexed chart. `10_{J/F}` is the same external point after transport through a host chart of width nine. `11` retains an intrinsic fibre coordinate together with that transported external coordinate.

The label `J` in the finite gluing modules is a generic external pointed object. It is not silently identified with the classical modular `j`-invariant. The literal modular interface remains separately typed in `ModularCurveJFrickeInterfaceExact`.

## Exact indexed attachment

`DASHI.Biology.IndexedJExternalGluingExact` constructs:

- a zero-indexed nine-ring `r0,...,r8`;
- a one-indexed linear lift `l1,...,l10`;
- closure maps with both `l1` and `l10` projecting to `r0`;
- a generic `PointedAttachment` interface;
- a concrete finite attachment identifying the intrinsic base `r0` with the external base `jOne`;
- two representations `localOne` and `transportedTen` of the same external point;
- the exact index law `10 = 1 + 9`;
- a joined coordinate retaining `r1` and `transportedTen`;
- the exact joined-address law `11 = 1 + 10`.

The concrete attachment is pushout-shaped but does not claim a categorical universal property. Mac Lane is cited for the categorical vocabulary:

- Saunders Mac Lane, *Categories for the Working Mathematician*, second edition. DOI `10.1007/978-1-4757-4721-8`.

## The five-by-two quotient

`DASHI.Biology.HalfChartNineRingQuotientExact` constructs two oriented five-point half charts. Before gluing there are ten points. The two distinguished endpoints map to one quotient point, while the eight nonbase points remain distinct:

```text
5 * 2 = 10
10 - 1 = 9
5 + 5 - 1 = 9.
```

The module supplies a lossless quotient encoding for the nine surviving points.

It also separates two unrelated five-element carriers:

```text
pointed half-chart positions
D4 irreducible-representation kinds.
```

Equal cardinality does not identify these types or explain one from the other.

## Exact Eisenstein phases and interference

`DASHI.Biology.EisensteinNineRingInterferenceExact` uses rational coordinates for

```text
a + b omega,
```

with multiplication reduced by

```text
omega^2 + omega + 1 = 0.
```

All scalar constants are explicitly typed as rational `/1` values before they enter the Eisenstein carrier or an equality target. It defines

```text
N(a + b omega) = a^2 - ab + b^2
```

and the exact polarization cross term

```text
B((a,b),(c,d)) = 2ac - ad - bc + 2bd.
```

The kernel proves

```text
N(x+y) = N(x) + N(y) + B(x,y).
```

For `1`, `omega`, and `omega^2` it proves:

- each phase has unit norm;
- each distinct pair has cross term `-1`;
- diagonal mass is `3`;
- pair mass is `-3`;
- total mass cancels exactly;
- the coordinate sum `1 + omega + omega^2` is exactly zero.

A typed `HostGuestWave` then proves the exact joined-intensity identity

```text
joined intensity
  = host intensity
  + guest intensity
  + host/guest cross term.
```

This is exact quadratic algebra. It is not promoted to literal quantum physics.

The same module constructs the pointed-square quotient:

```text
(vacant,+)  ~ (vacant,-)
(occupied,+) -> zeta
(occupied,-) -> zeta^2.
```

Thus orientation is conditional on occupancy rather than an independent bit at the zero state.

It also keeps the cardinality layers separate:

```text
3 * 2 = 6       local phase/orientation symmetry count
3^6   = 729     six-coordinate ternary field count
3^9   = 19683   nine-address ternary field count.
```

No six-coordinate reduction is claimed without an explicit three-constraint producer.

Primary source:

- Serge Lang, *Algebraic Number Theory*, second edition. DOI `10.1007/978-1-4612-0853-2`.

## The exact 196884 arithmetic split

`DASHI.Moonshine.Monster196884FibreInterferenceExact` proves

```text
fine chart count          = 5 * 2 = 10
fine phase-field count    = 3^9 = 19683
fine sector dimension     = 10 * 19683 = 196830
coarse phase symmetry     = 3 * 2 = 6
coarse address count      = 3^2 = 9
coarse sector dimension   = 6 * 9 = 54
fine + coarse             = 196830 + 54 = 196884.
```

Equivalently:

```text
196884 = (5 * 2) * 3^9 + (3 * 2) * 3^2.
```

The total is proved equal to the already formalized `moonshineV2Dimension`; the coarse term is proved numerically equal to the already formalized 3B trace `54` on `V^natural_2`.

This does **not** construct Monster submodules, a Monster action, or an isomorphism from equality of dimensions. It also does not derive the coefficient ten.

Primary source:

- John H. Conway and Simon P. Norton, *Monstrous Moonshine*. DOI `10.1112/blms/11.3.308`.

## Mathieu stabilizer order spine

`DASHI.Moonshine.MathieuStabilizerTowerExact` proves the exact order/index arithmetic

```text
8 --x9--> 72 --x10--> 720 --x11--> 7920 --x12--> 95040.
```

In particular:

```text
7920  = 8 * 9 * 10 * 11
95040 = 8 * 9 * 10 * 11 * 12.
```

Each transition is stored as a `StabilizerStep` containing the lower level, upper level, orbit size, and exact order law. `OrbitStabilizerArithmeticWitness` and `MathieuStepArithmeticWitness` package only the three orders and their multiplication law. They deliberately contain no arbitrary carriers, action, chosen point, stabilizer inclusion, or cardinality equivalences. Consequently they cannot masquerade as an actual group action; constructing the Mathieu permutation action remains a separate producer obligation.

The source boundary is important. The Atlas reports the order-eight four-point stabilizer in the Mathieu chain as quaternion `Q8`. It must not be replaced by square-grid `D4` merely because both groups have order eight. The module therefore gives these different `OrderEightShape` constructors and proves the selected source tag is not `D4`.

Primary sources:

- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker, and Robert A. Wilson, *Atlas of Finite Groups*. No DOI assigned.
- John D. Dixon and Brian Mortimer, *Permutation Groups*. DOI `10.1007/978-1-4612-0731-3`.

## Divisor lattices and path confluence

`DASHI.Moonshine.MathieuDivisorLatticeExact` constructs the exponent boxes

```text
95040 = 2^6 * 3^3 * 5 * 11
D(95040) = [0,6] x [0,3] x [0,1] x [0,1]
node count = 7 * 4 * 2 * 2 = 112,
```

and

```text
7920 = 2^4 * 3^2 * 5 * 11
D(7920) = [0,4] x [0,2] x [0,1] x [0,1]
node count = 5 * 3 * 2 * 2 = 60.
```

It also proves the valuation split

```text
(6,3,1,1) = (6,1,0,0) + (0,2,1,1)
```

corresponding arithmetically to

```text
192 * 495 = 95040
192 = 2^6 * 3
495 = 3^2 * 5 * 11.
```

The `M11 -> M12` increment is similarly

```text
(6,3,1,1) = (4,2,1,1) + (2,1,0,0),
```

with orbit factor `12 = 2^2 * 3`.

A terminating Pascal recurrence computes

```text
choose(12,4) = 495.
```

The module does not infer a cycle shape from that binomial equality alone.

Prime-coloured histories are represented explicitly. Different orderings such as `x2` then `x3`, and `x3` then `x2`, have the same endpoint. This proves the arithmetic confluence skeleton behind the interference analogy.

`DASHI.Moonshine.MathieuDivisorPathInterferenceExact` adds the missing amplitude data explicitly. For two histories ending at the same divisor it assigns independent Eisenstein amplitudes and proves

```text
node intensity
  = left diagonal intensity
  + right diagonal intensity
  + path cross term.
```

For amplitudes `1` and `omega`, it proves diagonal intensity `2`, cross term `-1`, and resulting node intensity `1`. The amplitudes are additional structure and are not inferred from divisor incidence. This is an exact finite coherent-amplitude model, not a claim of physical quantum dynamics.

Primary source for the lattice vocabulary:

- Garrett Birkhoff, *Lattice Theory*, third edition. DOI `10.1090/coll/025`.

## Typed integration of gluing and Mathieu indices

`DASHI.Moonshine.MathieuJTransportIntegrationExact` keeps two operations separate:

```text
pointed-set extension: 10 = 9 + 1, 11 = 10 + 1
order extension:       720 = 10 * 72, 7920 = 11 * 720.
```

The shared orbit number links the layers but does not equate addition of points with multiplication of group orders.

The canonical nine-to-ten analogy records:

```text
host point count      = 9
adjoined point count  = 1
completed point count = 10
internal order        = 72
completed order       = 720
orbit size            = 10.
```

The ten-to-eleven analogue is stored separately. Actual Mathieu actions, classical modular `j`, and Moonshine promotion remain outside this finite analogy.

## Lifted spiral of attachments

`DASHI.Biology.IteratedPointedAttachmentSpiralExact` formalizes the geometric content of a spiral that appears closed after projection but grows in a lifted direction.

Several seam states project to the same ring point while retaining distinct depth constructors. The addresses satisfy:

```text
0 and 1 project to the seam
1 and 10 project to the seam
1 and 10 have the same current lift depth
11 advances the depth by one
10 = 1 + 9
11 = 10 + 1.
```

Repeated attachment accumulates imported bundle depth. The module deliberately does not attribute categorical pushouts or this exact formalism to Marx or any philosophical author. Historical/dialectical comparison remains interpretive context rather than theorem provenance.

## Validation

Run:

```bash
bash scripts/check_ssp15_j_gluing_mathieu_interference_round6.sh
```

The checker:

- chains the Round-5 checker;
- rejects holes, postulates, unsafe pragmas, trust primitives, and termination escapes;
- checks source and theorem markers, explicit rational constants, arithmetic-only Mathieu witnesses, and amplitude-decorated path proofs;
- emits `artifacts/ssp15-j-gluing-mathieu-interference-round6.json`;
- invokes pinned Agda 2.9 on the Round-6 validation and aggregate roots.

The workflow pins all third-party actions to immutable commit SHAs and watches every direct checker dependency. No successful Agda-kernel result is claimed until a local or GitHub Actions run is observed.

## Exact boundary

This round proves finite arithmetic, finite quotient, rational Eisenstein, and typed-interface theorems. It does not prove:

- that the finite external `J` is the modular `j`-invariant;
- a universal pushout theorem for the concrete attachment;
- actual Mathieu permutation actions or subgroup embeddings;
- `Q8 ~= D4`;
- a Monster-module decomposition from `196884 = 196830 + 54`;
- that the divisor lattice determines amplitudes or is a physical quantum experiment;
- that `3^6` is the quotient of `3^9` without three explicit independent constraints;
- a historical claim that Marx formulated this categorical construction.

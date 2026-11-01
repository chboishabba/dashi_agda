# SSP15 indexed-j stratified quotient and multiresolution — Round 7

## Scope

This round is stacked on the indexed-j / Mathieu Round-6 branch.  It does not replace the existing pointed attachment interpretation of `0_F ~ 1_J ~ 10_{J/F} ~ 11`; it adds a second, explicitly typed multiresolution interpretation and states exactly where the two coincide only numerically.

The central separation is:

1. a **resolution quotient tower** `... -> X_2 -> X_1 -> X_0`;
2. a **filtered count profile** whose new grade can have size `b^r` while the retained prefix has size `1 + b + ... + b^r`;
3. an **inverse-limit point** as a compatible state at every finite resolution;
4. a second **3/6/9 relational-depth axis** that commutes with, but is not identified with, resolution.

## 1. Bare quotient tower versus split multiscale carrier

`DASHI.Foundations.StratifiedResolutionTowerExact` introduces the deliberately weak record

```text
ResolutionTower
  Carrier : Nat -> Set
  project : Carrier (suc r) -> Carrier r
```

No global section is assumed.  This matters because a coarse quotient can forget information without having a canonical fine representative.

The pre-existing `DASHI.Core.MultiscaleMDL.MultiscaleCarrier` is shown to be a stronger split structure: it has `lift` and proves `project (lift x) = x`.  The new bridge `multiscaleCarriesChosenSplit` records that relationship rather than silently making every quotient a product.

`CoarseFineCut` and `MiddleLevelRole` make the relative nature of the labels exact: a state at one level may be fine relative to its predecessor and coarse relative to its successor.

## 2. Stratified fibres are executable, not decorative terminology

The same module packages a `StratifiedProjection` with

```text
Stratum
stratumOf
FibreModel
fibreEquivalenceAt
```

so fibre type is permitted to vary by coarse stratum.

A concrete finite witness has:

```text
regular coarse stratum : two fine realisations
fixed coarse stratum   : one fine realisation
```

and proves explicit two-sided equivalences between each dependent projection fibre and its stratum fibre model.  Therefore the round does not rely on a globally homogeneous `X_fine = X_coarse x F` assumption.

## 3. Decimal homogeneous model and exact coarse/residual factorisation

`DASHI.Biology.IndexedJStratifiedMultiresolutionExact` instantiates a ten-way address tower

```text
DecimalAddress 0
DecimalAddress 1
DecimalAddress 2
...
```

where one refinement appends one `DecimalDigit` and `prefix` is the quotient map.

This model is deliberately homogeneous, so it also instantiates the existing `MultiscaleMDL` interface.  Its residual is exactly the last digit and reconstruction appends that digit.

The generic MDL codec already proves

```text
join (split fine) = fine.
```

Round 7 proves the converse for this homogeneous model:

```text
split (join (coarse , digit)) = (coarse , digit).
```

Thus a fine decimal address is exactly factored into its coarse prefix and one refinement digit.  This is stronger than merely observing a geometric-series count.

## 4. `1,10,100,1000,...` versus `1,11,111,1111,...`

The grade count is defined recursively by

```text
grade_b(0)     = 1
grade_b(r + 1) = b * grade_b(r).
```

The cumulative retained count is

```text
retained_b(0)     = 1
retained_b(r + 1) = retained_b(r) + grade_b(r + 1).
```

For radix ten the formal kernel reduces these definitions exactly to

```text
grade    : 1, 10, 100, 1000
retained : 1, 11, 111, 1111.
```

The distinction is explicit: `100` is the level-two homogeneous fine count; `111` is the cumulative count through levels zero, one and two.  Round 7 therefore does **not** assert that the finest level-two quotient itself has 111 states.

The existing Round-6 indexed-j construction also produces natural number `11`, from one intrinsic coordinate plus transported external index ten.  Round 7 proves

```text
retainedResolutionCount 10 1 = joinedAddressIndex
```

only as an equality in `Nat`.  A boundary blocks promotion of that numeric equality to an identification of the two typed constructions.

## 5. Infinite refinement is a compatible history

The generic type

```text
InverseLimitPoint tower
```

contains

```text
atResolution : (r : Nat) -> Carrier r
coherent : project (atResolution (suc r)) = atResolution r.
```

The decimal model constructs an actual infinite compatible point: the all-zero address at every finite depth.

This is intentionally weaker than a p-adic claim.  A boundary explicitly records that an inverse limit of the bare decimal-address tree is not automatically a `10`-adic ring.  Modular arithmetic, ring operations, topology/completeness and the canonical `mod 10^r` transition maps would need to be supplied before such a promotion.

Likewise, finite grade counts do not by themselves construct the completed Hilbert direct sum used in analytic multiresolution/wavelet theory.

## 6. Coarse observable stretched over the fine fibre

For an observable

```text
f : Carrier r -> Value
```

Round 7 defines the pullback

```text
pullbackObservable f fine = f (project fine).
```

and proves it is constant on a projection fibre:

```text
project left = project right
  -> pullback f left = pullback f right.
```

This is the exact finite interpretation of “stretch/superimpose the coarse sheet over the fine sheet”.

Fine-to-coarse averaging is not invented automatically: `FibreAggregator` is separate additional structure.  Once supplied, `coarseThenStretch` is available as a fine-observable endomorphism.

## 7. Independent 3/6/9 depth and resolution axes

`DASHI.Biology.SSP369JResolutionBifiltrationExact` makes the two-index proposal concrete.

At each decimal resolution `r`:

```text
H3 r = one three-coordinate block
H6 r = H3 r + a second three-coordinate block
H9 r = H6 r + a third three-coordinate block.
```

Every coordinate is itself a `DecimalAddress r`.

Depth projections forget the newest block:

```text
H9 r -> H6 r -> H3 r.
```

Resolution projections apply decimal `prefix` coordinatewise:

```text
H3 (r+1) -> H3 r
H6 (r+1) -> H6 r
H9 (r+1) -> H9 r.
```

The two depth/resolution squares are proved definitionally:

```text
project6to3 (coarsen6 x) = coarsen3 (project6to3 x)
project9to6 (coarsen9 x) = coarsen6 (project9to6 x).
```

Chosen all-zero blocks give split inclusions `H3 -> H6 -> H9`, and two additional theorems prove those inclusions commute with resolution coarsening.

`J369Bifiltration` packages the complete finite commuting structure.

The all-zero inclusion is only a mathematical section, not a claim that zero-padding is the physically canonical way to extend relational depth.

## 8. Honest infinite boundary

The finite commuting squares are enough to establish a coherent bifiltration.  They do **not** prove

```text
colim_d lim_r X(d,r) = lim_r colim_d X(d,r).
```

Interchange of limits needs additional categorical/topological hypotheses.  The Round-7 boundary keeps this claim false rather than turning finite commutativity into an unjustified infinite theorem.

## Sources carried in Agda headers

- Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer (1998), DOI `10.1007/978-1-4757-4721-8`.
- Mark Goresky and Robert MacPherson, *Stratified Morse Theory*, Springer (1988), DOI `10.1007/978-3-642-71714-7`.
- Stephane G. Mallat, “A Theory for Multiresolution Signal Decomposition: The Wavelet Representation”, *IEEE Transactions on Pattern Analysis and Machine Intelligence* 11(7) (1989), DOI `10.1109/34.192463`.
- Ingrid Daubechies, “Orthonormal Bases of Compactly Supported Wavelets”, *Communications on Pure and Applied Mathematics* 41(7) (1988), DOI `10.1002/cpa.3160410705`.

The sources motivate the standard mathematical vocabulary.  The concrete indexed-j decimal tower, typed bridge to Round 6, 3/6/9 product bifiltration, and DASHI claim boundaries are repository constructions, not attributions to those sources.

## Validation

The cumulative validation module exercises:

- the regular and fixed singular-fibre equivalences;
- both decimal split/join directions;
- `10`, `100`, `1000` and `11`, `111`, `1111`;
- the numeric-but-not-typed bridge to Round-6 `joinedAddressIndex`;
- inverse-limit coherence;
- the `6 -> 3` and `9 -> 6` depth/resolution commuting squares;
- both inclusion/resolution commuting squares;
- the no-automatic-`10`-adic and no-automatic-limit-interchange boundaries.

The Round-7 checker cascades through the complete Round-6 checker, rejects holes/postulates/unsafe trust escapes, runs the substance classifier, and invokes the repository's pinned Agda 2.9 parallel checker on the new validation and aggregate roots.

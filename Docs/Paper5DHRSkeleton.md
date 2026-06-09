# Paper 5 Draft: Finite Prime-Lane DHR Reconstruction

## Abstract

This paper records the finite prime-lane part of the DASHI DHR/DR
reconstruction story.  The verified object is not the full category of
localized transportable DHR endomorphisms.  It is the finite carrier-level
sector surface over the three selected prime lanes `p2`, `p3`, and `p5`,
together with typed witnesses for the five internal Doplicher-Roberts
axiom slots consumed by the QFT receipt layer.

The positive result is finite and receipt-shaped:

- the selected finite sector rows are present;
- the selected carrier-level localized endomorphisms are present;
- the selected tensor, braiding, hexagon, statistics, star, and dual receipts
  are present;
- the finite fibre functor sends the three prime lanes to Hilbert dimensions
  `1`, `2`, and `3`;
- the reconstruction status may be recorded as `conditionalOnDRAuthority`
  when the external DHR/DR and Tannaka-Krein authority receipts are consumed.

The negative result is equally important.  The repository does not promote an
unconditional theorem `G_DHR ~= G_SM`.  It does not internally construct the
compact gauge group, does not prove a full arbitrary-sector DHR category
theorem, and does not discharge the exact Standard Model identification.  The
formal receipts keep those promotion flags false.

## 1. Formal Sources

The paper is a prose companion to the following Agda receipt surfaces:

- `DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger`
- `DASHI.Physics.QFT.DHRGaugeReceiptSurface`
- `DASHI.Physics.QFT.DHROriginalPaperAuthorityReceipt`
- `DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt`
- `DASHI.Physics.QFT.ConditionalGDHRSMPromotionReceipt`
- `DASHI.Physics.QFT.DHRTensorDualGroupReconstruction`

The key typed status constructor is:

```text
conditionalOnDRAuthority
```

from `GDHRSMPromotionStatus`.  The corresponding non-promotion flags are:

```text
unconditionalGDHREqualsGSMPromoted = false
fullTheoremInRepoClaimed = false
drTheoremAppliedHere = false
compactGaugeGroupConstructedHere = false
categoryEquivalenceToRepGPromoted = false
standardModelMatchingPromoted = false
tannakaDualGroupConstructed = false
```

Those booleans are part of the mathematical claim.  They are not caveats to be
removed in prose.

## 2. Finite Prime-Lane Sector Surface

The finite sector universe is the three-row prime-lane surface recorded by
`FinitePrimeLaneDHRSMCompatibilityLedger`.

```text
p2 -> U1Y  -> dimension 1 -> DHR.U1Sector
p3 -> SU2L -> dimension 2 -> DHR.SU2Sector
p5 -> SU3c -> dimension 3 -> DHR.SU3Frontier
```

The rows are represented by:

- `p2U1YFinitePrimeLaneSMRow`
- `p3SU2LFinitePrimeLaneSMRow`
- `p5SU3cFinitePrimeLaneSMRow`
- `canonicalFinitePrimeLaneSMRows`

This is a finite chosen carrier surface.  It is not the full DHR universe of
all localized transportable endomorphisms over an AQFT net.  In paper
notation, write the selected objects as:

```text
rho_p2, rho_p3, rho_p5
```

and write the selected finite sector category as:

```text
C_fp = <rho_p2, rho_p3, rho_p5>_finite
```

The subscript is essential: `C_fp` is the category actually witnessed by the
finite receipts, not an arbitrary-sector closure.

## 3. Carrier-Level Localized Endomorphisms

The carrier-level endomorphism receipt is:

```text
FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt
```

It records the three selected localized endomorphism kinds:

```text
p2CarrierLocalisedEndomorphism
p3CarrierLocalisedEndomorphism
p5CarrierLocalisedEndomorphism
```

The finite end-sector matrix targets are:

```text
p2 -> C / M1
p3 -> M2
p5 -> M3
```

with matrix-size agreement closed by the finite row data.  This is enough for
the finite carrier-level statements used in the ledger.  It is not a proof
that every localized transportable endomorphism of a Haag-Kastler net has
been constructed inside the repository.

## 4. The Five Internal DR Axiom Slots

The five internal axiom slots are collected by:

```text
DHRDRInternalAxiomReceiptPack
canonicalDHRDRInternalAxiomReceiptPack
canonicalDHRDRInternalAxiomKindOrder
allFiveInternalAxiomReceiptsTyped
```

The receipts typecheck the finite prime-lane witnesses for the following five
DR/DHR internal axiom slots.

### 4.1 Symmetric Tensor Structure

The finite tensor surface is supplied by the prime-lane tensor carrier and
swap receipts:

```text
FinitePrimeLaneTensorCarrier
finitePrimeLaneTensorSwap
FinitePrimeLaneBraidingSwapReceipt
FinitePrimeLanePairSwapBraidingNaturalityReceipt
```

The naturality square is consumed at the finite wire level.  Its scope is the
selected carrier action and selected finite wire, where the canonical laws
close over the finite prime-lane cases.  This supports the finite symmetric
tensor slot in the receipt pack.  It does not assert a full symmetric tensor
category of arbitrary DHR sectors.

### 4.2 Star Structure

The finite star surface is part of the carrier localized endomorphism receipt
and associated star-algebra pack:

```text
FinitePrimeLaneLocalisedEndomorphismStarAlgebraPack
```

At paper level this is the finite `C*`-style involutive structure available
on the selected carrier rows.  The receipt is intentionally narrower than an
internal construction of a full DHR `C*`-category.

### 4.3 Conjugates And Duals

The finite conjugate-dual laws are represented by:

```text
FinitePrimeLaneConjugateDualReceipt
```

The receipt supplies the finite duality/zigzag witness needed by the internal
axiom pack for the selected `p2/p3/p5` sector.  It does not claim a universal
dual object construction for every sector outside `C_fp`.

### 4.4 Direct Sums And Subobjects

The direct-sum/subobject slot is typed as an internal DR axiom receipt.  In
this draft the statement is deliberately receipt-level: the finite pack
contains the required typed witness for the finite prime-lane surface, and
the paper consumes that witness.  It is not expanded into a theorem that all
subobjects in a completed DHR category exist internally.

### 4.5 `End(1) ~= C`

The scalar-unit slot is also recorded in the internal receipt pack.  For the
finite carrier surface, it is tied to the selected scalar end-sector target
and the finite fibre target.  The paper may state that the typed finite unit
endomorphism condition is present; it may not state that the repository has
proved the full AQFT categorical scalar law beyond the finite receipt surface.

## 5. Braiding, Hexagon, And Statistics Receipts

The finite pair-swap braiding naturality and coherence receipts are:

```text
FinitePrimeLaneDHRSMNaturalityReceipt
FinitePrimeLanePairSwapBraidingNaturalityReceipt
DHRFinitePrimeLaneLeftRightHexagonCoherenceReceipt
FinitePrimeLaneStatisticsAsBraidingTargetReceipt
```

These receipts are the finite coherence layer used by the paper.  They say
that the selected prime-lane swaps and coherence diagrams have canonical
witnesses in the repository.  The phrase "finite" should remain visible
whenever these results are cited, because the receipt boundary is not the
same as a general DHR coherence theorem for every localized sector.

## 6. Fibre Functor And Tannaka-Krein Boundary

The finite prime-lane fibre functor receipt is:

```text
TannakaKreinFibreFunctorReceipt
```

It maps the selected prime-lane endomorphisms to finite Hilbert dimensions:

```text
F(rho_p2) = C^1
F(rho_p3) = C^2
F(rho_p5) = C^3
```

The canonical rows are:

```text
p2FinitePrimeLaneFibreFunctorRow
p3FinitePrimeLaneFibreFunctorRow
p5FinitePrimeLaneFibreFunctorRow
```

The finite monoidal structure is recorded by:

```text
FinitePrimeLaneFibreFunctorMonoidalStructure
```

The external authority names are:

```text
tannakaKreinCompactGroupDuality
deligneTannakianCategories
doplicherRobertsDHRReconstruction
```

This section is an authority boundary.  It permits a conditional prose bridge
from the finite typed witnesses to the usual Tannaka-Krein/DHR reconstruction
story, but the receipt keeps:

```text
tannakaDualGroupConstructed = false
```

unless an actual internal construction of `Aut^tensor(F)` is added later.

## 7. Theorem 5.1

### Statement

Let `C_fp` be the finite prime-lane sector surface generated by the selected
objects `rho_p2`, `rho_p3`, and `rho_p5`, with carrier-level endomorphism,
tensor, braiding, star, conjugate-dual, direct-sum/subobject, and scalar-unit
witnesses consumed from the QFT receipt layer.

Then `C_fp` satisfies the five DR internal axiom slots as typed finite
witnesses in:

```text
DHRDRInternalAxiomReceiptPack
```

More precisely, the finite witness pack records:

1. finite symmetric tensor structure;
2. finite star structure;
3. finite conjugates/duals;
4. finite direct sums/subobjects at the typed receipt surface;
5. finite `End(1) ~= C` scalar-unit target.

Conditional on the external DHR/DR and Tannaka-Krein authority receipts, the
paper may record the conditional reconstruction status:

```text
conditionalOnDRAuthority
```

with target statement:

```text
G_DHR conditionally targets U(1) x SU(2) x SU(3)
through consumed DHR/DR authority applied to the finite prime-lane witnesses.
```

The theorem does not prove:

```text
G_DHR ~= G_SM
```

as an unconditional in-repository result.

Equivalently, Theorem 5.1 has the following exact boundary:

```text
finite DHR axiom receipts + consumed DHR/DR authority
  => conditionalOnDRAuthority
```

and not:

```text
finite DHR axiom receipts
  => G_DHR ~= G_SM
```

The distinction is part of the theorem.  `conditionalOnDRAuthority` is a
status value recording that the finite prime-lane witnesses have been placed
at the authority boundary.  It is not an inhabitant of a compact-group
reconstruction theorem, and it is not an inhabitant of an exact Standard Model
group-identification theorem.

In manuscript notation, the result should be written as:

```text
Theorem 5.1.  C_fp realizes the finite DHR/DR receipt skeleton and supports a
conditional authority target for G_DHR.
```

It should not be written as:

```text
Theorem 5.1.  C_fp reconstructs G_SM.
```

### Proof Sketch

The finite sector rows are supplied by
`FinitePrimeLaneDHRSMCompatibilityLedger`, which fixes the three selected
prime lanes, their gauge-factor labels, their dimensions, and their DHR sector
atoms.  The finite localized endomorphism layer is supplied by
`FinitePrimeLaneCarrierLevelLocalisedEndomorphismReceipt`; the finite
naturality, pair-swap, hexagon, statistics, star, and conjugate-dual layers
are supplied by the corresponding QFT receipts.

The record `FinitePrimeLaneDHRInternalCondition` consumes these receipts
together with `DHRDRInternalAxiomReceiptPack`.  Its field
`allFinitePrimeLaneAxiomsInhabited` is identified with
`allFiveInternalAxiomReceiptsTyped` from the canonical internal axiom receipt
pack.  Its field `arbitrarySectorAxiomsInhabited` remains false.  Thus the
in-repository theorem is exactly finite-prime-lane inhabitation of the five
typed axiom slots.

The record `DHRDRAuthorityExternalCondition` then records that DHR/DR
authority is consumed while also recording:

```text
drTheoremAppliedHere = false
compactGaugeGroupConstructedHere = false
```

Finally, `ConditionalGDHRSMPromotionReceipt` sets the status to
`conditionalOnDRAuthority` while keeping the unconditional and full-theorem
promotion flags false.  Therefore the result is a conditional authority
receipt over finite witnesses, not a full reconstruction theorem.

### Boundary Corollary

Theorem 5.1 immediately implies a negative corollary:

```text
unconditionalGDHREqualsGSMPromoted = false
fullTheoremInRepoClaimed = false
```

This corollary should be stated close to the theorem in the final paper.  The
point is not merely that the proof is unfinished.  The formal object records
the non-promotion as data.  Any future paper that wants to replace this
boundary must add one of the following:

- an internal arbitrary-sector DHR category construction with the corresponding
  tensor, braiding, statistics, star, dual, direct-sum/subobject, and scalar
  laws;
- an internal construction of the compact reconstructed group `G_DHR`;
- a concrete equivalence or homomorphism comparison between `G_DHR` and
  `U(1) x SU(2) x SU(3)` with the required kernel/image/faithfulness or
  quotient data;
- an explicit authority receipt whose scope is strong enough to close the
  reconstruction and Standard Model identification boundary.

Until one of these is present, the only admissible theorem-level phrase is
"conditional authority target", not "reconstruction of the Standard Model
gauge group".

## 7.1 Exact Role of `conditionalOnDRAuthority`

The status `conditionalOnDRAuthority` should be treated as a typed midpoint
between a finite receipt and a promoted theorem.  It records that three inputs
are simultaneously available:

1. the finite prime-lane internal condition is inhabited;
2. original DHR/DR and Tannaka-Krein authority receipts are consumed;
3. residual blockers are retained rather than erased.

The status does not assert that the external theorem has been applied inside
the repository.  It also does not assert that an internally constructed
`Aut^tensor(F)` has been computed.  The corresponding fields remain:

```text
drTheoremAppliedHere = false
compactGaugeGroupConstructedHere = false
tannakaDualGroupConstructed = false
autTensorFComputedLocally = false
gDHREqualsSMGaugePromoted = false
```

This is the cleanest way to describe Paper 5's advance: the finite
prime-lane data have reached a precise authority boundary, and the boundary
is recorded without being crossed.

## 8. Exact Non-Promotion Boundary

The following blockers are canonical and should be cited when explaining why
the result remains conditional:

```text
blockedByArbitrarySectorGeneralisation
blockedByInternalCompactGaugeGroupConstruction
blockedByConcreteGDHRToSMHomomorphism
blockedByExactSMCarrierFunctorMatch
```

They correspond to four missing promotions.

First, the finite prime-lane witnesses do not cover all localized
transportable DHR endomorphisms.  The repository has finite receipts for
`p2/p3/p5`; it does not have arbitrary-sector closure.

Second, the compact gauge group is not constructed internally.  The DHR/DR
and Tannaka-Krein results are cited as external authority, not reproved inside
the repository.

Third, no concrete in-repository homomorphism from an internally constructed
`G_DHR` to `U(1) x SU(2) x SU(3)` is available with laws, kernel, image,
faithfulness, and quotient decisions.

Fourth, the exact Standard Model carrier-functor match remains unpromoted.
The three finite dimensions match the selected prime-lane targets, but that
is not the same as proving a full equivalence between the reconstructed DHR
group and the physical Standard Model gauge group.

## 9. Recommended Paper Wording

Use:

```text
The finite prime-lane sector satisfies the five DR internal axiom slots as
typed witnesses in the DASHI receipt layer.
```

Use:

```text
Conditional on the external DHR/DR and Tannaka-Krein authority receipts, this
supports the conditional reconstruction target
G_DHR -> U(1) x SU(2) x SU(3).
```

Do not use:

```text
DASHI proves G_DHR ~= G_SM.
```

Do not use:

```text
The full DHR category has been constructed internally.
```

Do not use:

```text
Aut^tensor(F) is constructed in Agda.
```

The strongest honest summary is:

```text
finite typed DHR/DR axiom receipt + external reconstruction authority
+ conditional Standard Model gauge target, with full identification still
blocked.
```

## 10. Acceptance Checklist

Before this draft is promoted into the paper body, every sentence that mentions
reconstruction should pass the following checks:

- if it says "DHR category", it specifies finite prime-lane scope unless a
  later arbitrary-sector proof is cited;
- if it says "gauge group", it says conditional authority target unless a
  later internal compact-group construction is cited;
- if it says `U(1) x SU(2) x SU(3)`, it distinguishes selected finite target
  matching from full `G_DHR ~= G_SM` identification;
- if it cites Tannaka-Krein or DHR/DR, it marks the result as an external
  authority boundary;
- if it states Theorem 5.1, it includes the false full-promotion flags or an
  equivalent non-promotion paragraph nearby.

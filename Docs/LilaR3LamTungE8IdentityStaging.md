# LILA-R3 Lam-Tung/E8 Identity Staging

Date: `2026-05-13`
Status: `staged behind LILA-R2 proof closure; skeleton-only; non-promoting`
Owner: `Lie-class worker / DASHI Lane 4 LILA-R3 staging`

This document stages LILA-R3 as a future proof obligation, not as a theorem.
LILA-R3 must remain blocked until Lane 1/LILA-R2 supplies a completed E8 root
enumeration/cardinality receipt. In the typed staging surface this gate is named
`E8RootEnumerationReceipt` and is deliberately just the local alias:

```text
DASHI.Physics.Closure.LamTungAsE8EvenSumIdentity.E8RootEnumerationReceipt
  = DASHI.Algebra.Trit.E8RootEnumeration.E8RootEnumerationComplete
```

`E8RootEnumerationComplete` is constructorless today, so the R3 surface can name
the dependency and proof obligations but cannot inhabit the Lam-Tung/E8
identity. The current E8 module now exposes concrete generator surfaces, but
those generators are not a completion receipt.

## Current Local Surfaces

- `DASHI.Algebra.Trit.E8RootEnumeration`
  - prepares the doubled-coordinate E8 split:
    - integer class: `112`
    - half class: `128`
    - total expected class: `240`
  - now exposes concrete generator surfaces:
    - `integerIndexedRoots` / integer family length `112`;
    - `halfIndexedRoots` / half family length `128`;
    - `combinedIndexedRoots` / combined family length `240`.
  - keeps `E8RootEnumerationComplete` constructorless.
- `DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2`
  - records count support only via `LilaE8RootEnumerationReceiptR2`.
  - `theoremCompletedHere = false`.
  - does not construct root carrier, decidable enumeration, duplicate freedom,
    completeness, norm/inner-product laws, Weyl closure, or projection
    compatibility.
- `DASHI.Physics.Closure.LamTungE8AdapterSurface`
  - names A0..A7, E8 coordinate slots, coefficient definition requirements,
    E8 prior requirements, phi-star projection targets, blockers, and
    non-promotion boundaries.
  - keeps `LamTungRelationAsE8EvenSumObligation` and
    `LamTungE8PromotionReceipt` uninhabited locally.
- `DASHI.Physics.Closure.LamTungAsE8EvenSumIdentity`
  - currently exists locally as a skeleton/diagnostic surface.
  - imports the R2 count receipt, R3 adapter surface, Clifford even-lift
    bridge, and `DASHI.Algebra.Trit.E8RootEnumeration` only to gate on the
    uninhabited complete receipt.
  - binds only an even-subalgebra handle; it does not prove Lam-Tung as an E8
    even-sum identity.
- `DASHI.Physics.Closure.LilaE8ThetaJBridgeSurface`
  - is R4-facing and remains blocked on modular-form/theta/J receipts. It is
    not a substitute for R2 or R3.

## Exact Gate Dependency

The current exact gate is:

```text
DASHI.Algebra.Trit.E8RootEnumeration.E8RootEnumerationComplete
```

The LILA-R3 module exposes this as `E8RootEnumerationReceipt` for staging
language only. The gate is blocked by:

```text
DASHI.Algebra.Trit.E8RootEnumeration.e8RootEnumerationCompleteImpossibleHere
```

This is a no-promotion dependency: it records that R3 cannot proceed until the
root enumeration receipt exists. Concrete lists with the right lengths are
available, but R3 treats them as pre-receipt evidence until the proof-closure
obligations below are discharged.

## Native Lift And Sub-Root Gate

R3 now imports the exact R2 propositional-lift ledger
`canonicalE8NativePropositionalLiftTargets`. The ledger names the required
lift from executable membership/no-duplicate/disjointness/parity checks to
native root membership, `Unique`/no-duplicate structure, native disjointness,
native even parity, and integer/half/combined completeness. It is a dependency
ledger only; it does not inhabit `E8RootEnumerationComplete`.

R3 also records a separate electroweak sub-root restriction gate:

- the electroweak sub-root carrier must be shown inside the completed R2 E8
  root set;
- membership in that restricted carrier must be decidable;
- the restricted roots must be unique inside the combined root list;
- the restricted roots must be disjoint from the excluded roots;
- the restricted carrier must be complete for the Lam-Tung electroweak sector;
- the A0..A7 coordinate assignment must target that restricted carrier;
- the restricted even-sum law must be proved equivalent to the Lam-Tung
  relation.

The local placeholder `ElectroweakSubRootRestrictionReceipt` is constructorless,
with an impossibility eliminator, so no electroweak sub-root restriction is
claimed here.

## Current Lane 1 Boundary

The R3 diagnostic now records both sides of the Lane 1 state:

- available generator surface:
  - concrete integer-root generator/list with length `112`;
  - concrete half-root generator/list with length `128`;
  - concrete combined generator/list with length `240`;
- missing proof closure:
  - integer-family no-duplicates and completeness;
  - half-family parity soundness, no-duplicates, and completeness;
  - integer/half disjointness;
  - combined no-duplicates;
  - combined E8-shape completeness.

This distinction is important. LILA-R3 may start planning the exhaustive
Lam-Tung/E8 check against the expected list shapes, but it may not execute or
promote the identity from generator length alone.

## Required Lane 1 Fields

LILA-R3 may not promote until Lane 1 lands a receipt with fields equivalent to
all of the following:

- concrete eight-coordinate E8 root carrier;
- indexed eight-coordinate E8 root carrier, if the proof route keeps the
  `HalfTritIndexed` machinery;
- integer-root enumerator with `112` roots;
- half-root enumerator with `128` roots;
- combined root enumerator with `240` roots;
- total root enumeration with `240` roots;
- root equality decision;
- root membership decision;
- duplicate-freedom proof;
- completeness proof;
- squared-norm and inner-product laws;
- even-sum/parity law in the same coordinate convention;
- coordinate chart for exactly eight slots;
- coordinate-assignment compatibility for A0..A7;
- Weyl or symmetry closure, if consumed by the identity;
- DASHI/LILA projection compatibility if the result feeds R5.

The expected future import should be an `E8RootEnumerationReceipt`-like surface,
or a renamed local equivalent, whose fields explicitly certify the above. The
current exact blocked carrier is still `E8RootEnumerationComplete`.

## Exhaustive 240-Root Check Plan

After the gate lands, exhaustive checking should be mechanical over the
receipt's enumerators:

1. Check the integer family enumerates exactly `112` doubled-coordinate roots.
2. Check the half family enumerates exactly `128` doubled-coordinate roots.
3. Append the two families and prove the combined list has length `240`.
4. Run the root equality decision over every pair to prove duplicate freedom
   within and across families.
5. Run membership decisions for candidate roots against the integer, half, and
   combined enumerators.
6. Verify the squared-norm law for all `240` roots.
7. Verify the inner-product law in the same E8 lattice convention.
8. Verify the even-sum/parity law for all `240` roots.
9. Verify the A0..A7 coordinate assignment against the eight-coordinate chart.
10. Only then transport the Lam-Tung relation into the E8/Clifford even-sum
    identity statement.

## LILA-R3 Proof Obligations

Once R2 lands, LILA-R3 must still supply:

- Lam-Tung coefficient definitions for A0..A7;
- angular-frame convention;
- coefficient normalization law;
- coefficient extraction observable;
- covariance and uncertainty semantics;
- dataset/bin binding if tied to phi-star;
- semantics for assigning A0..A7 into the E8 coordinate frame;
- statement of the Lam-Tung relation in the selected coefficient convention;
- E8 even-sum identity statement in the exact R2 coordinate convention;
- proof that the Lam-Tung relation is equivalent to that E8 even-sum identity;
- optional Clifford/even-subspace compatibility if the current Clifford bridge
  remains part of the route;
- non-promotion boundary preserving separation from W3/W4/W5/W8 and R5.

## Expected E8 Field Names

The future R2/R3 bridge should expect names equivalent to:

```text
E8RootCarrier
E8IndexedRootCarrier
integerRoots
integerRootsLength112
halfRoots
halfRootsLength128
allRoots
allRootsLength240
rootEqualityDecision
rootMembershipDecision
noDuplicateRoots
enumerationComplete
squaredNormLaw
innerProductLaw
evenSumLaw
coordinateChart8
coordinateAssignmentCompatible
```

These names are staging expectations, not current imports. If the eventual R2
module uses different names, R3 should adapt through a small compatibility
record rather than rewriting the identity proof.

## Current Skeleton Status

The current skeleton surface is safe only as `skeletonOnly/noPromotion`.
It may import:

```text
DASHI.Algebra.Trit.E8RootEnumeration
DASHI.Physics.Closure.LamTungE8AdapterSurface
DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2
DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem
```

It must not import these as proof of LILA-R3. The Clifford/even binding is only
a handle for later interpretation; it does not supply E8 cardinality,
coordinate enumeration, Lam-Tung coefficient semantics, or an identity proof.

## Cannot Be Inhabited Yet

The current repo cannot inhabit:

- `E8RootEnumerationReceipt`;
- `LamTungRelationAsE8EvenSumObligation`;
- `LamTungAsE8EvenSumIdentity`;
- exhaustive 240-root Lam-Tung/E8 identity check;
- A0..A7 coefficient-definition receipt;
- A0..A7-to-E8 coordinate-assignment proof;
- phi-star projection receipt;
- LILA-R3 promotion receipt.

## No-Promotion Boundary

LILA-R3 must not claim:

- Lam-Tung proof;
- E8 physical theorem;
- E8 cardinality/enumeration completion;
- phi-star projection receipt;
- comparison-law receipt;
- W3/G5 promotion;
- W4/W5/W8 promotion;
- LILA-R5 readiness.

Promotion is allowed only after R2 lands a real E8 enumeration/cardinality
receipt and R3 proves the Lam-Tung/E8 identity against that exact carrier.

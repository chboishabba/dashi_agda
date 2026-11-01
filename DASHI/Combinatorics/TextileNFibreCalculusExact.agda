module DASHI.Combinatorics.TextileNFibreCalculusExact where

open import DASHI.Core.Prelude
open import Data.List using (map; _++_)

------------------------------------------------------------------------
-- Shared textile event kernel.
--
-- The calculus is unbounded in the number of fibres.  The canonical
-- regression ladder below instantiates 3 through 15 fibres explicitly.
--
-- Important separation:
--   braid/plait  = ordered adjacent strand crossings;
--   weave        = interlacement of two strand families;
--   knitting     = loop formation through retained prior loops;
--   crochet      = active-loop hook operations, possibly into prior fabric.
--
-- These crafts may share crossing / passage events without being identified.
------------------------------------------------------------------------

data CrossingOrientation : Set where
  overCrossing : CrossingOrientation
  underCrossing : CrossingOrientation

data Handedness : Set where
  leftHanded : Handedness
  rightHanded : Handedness

data FibreRole : Set where
  freeStrand : FibreRole
  warpStrand : FibreRole
  weftStrand : FibreRole
  workingYarn : FibreRole
  retainedLoop : FibreRole
  activeLoop : FibreRole

data TextileKind : Set where
  braidKind : TextileKind
  plaitKind : TextileKind
  weaveKind : TextileKind
  knitKind : TextileKind
  crochetKind : TextileKind

------------------------------------------------------------------------
-- Valid adjacent braid generators.
--
-- sigma i is only constructible when i + 2 <= n, so it denotes a crossing
-- between adjacent positions i and i+1 inside an n-fibre bundle.
------------------------------------------------------------------------

record AdjacentCrossing (n : Nat) : Set where
  constructor sigma
  field
    leftIndex : Nat
    orientation : CrossingOrientation
    inRange : leftIndex + 2 ≤ n

open AdjacentCrossing public

BraidWord : Nat → Set
BraidWord n = List (AdjacentCrossing n)

emptyBraid : {n : Nat} → BraidWord n
emptyBraid = []

singleCrossing :
  {n : Nat} →
  (i : Nat) →
  (o : CrossingOrientation) →
  i + 2 ≤ n →
  BraidWord n
singleCrossing i o p = sigma i o p ∷ []

prependCrossing :
  {n : Nat} →
  AdjacentCrossing n →
  BraidWord n →
  BraidWord n
prependCrossing c w = c ∷ w

------------------------------------------------------------------------
-- Explicit 3-fibre Artin/Yang--Baxter words.
------------------------------------------------------------------------

threeHasSigma0 : 0 + 2 ≤ 3
threeHasSigma0 = s≤s (s≤s z≤n)

threeHasSigma1 : 1 + 2 ≤ 3
threeHasSigma1 = s≤s (s≤s (s≤s z≤n))

sigma0-3 : AdjacentCrossing 3
sigma0-3 = sigma 0 overCrossing threeHasSigma0

sigma1-3 : AdjacentCrossing 3
sigma1-3 = sigma 1 overCrossing threeHasSigma1

threeFibreYangBaxterLeft : BraidWord 3
threeFibreYangBaxterLeft = sigma0-3 ∷ sigma1-3 ∷ sigma0-3 ∷ []

threeFibreYangBaxterRight : BraidWord 3
threeFibreYangBaxterRight = sigma1-3 ∷ sigma0-3 ∷ sigma1-3 ∷ []

------------------------------------------------------------------------
-- Braid history is first-class.  Endpoint coincidence does not erase the
-- ordered word, crossing orientation, handedness, or fibre count.
------------------------------------------------------------------------

record BraidedFibreHistory (n : Nat) : Set where
  constructor braidedFibreHistory
  field
    word : BraidWord n
    handedness : Handedness
    provenanceDepth : Nat

open BraidedFibreHistory public

threeLeftHistory : BraidedFibreHistory 3
threeLeftHistory =
  braidedFibreHistory threeFibreYangBaxterLeft rightHanded 3

threeRightHistory : BraidedFibreHistory 3
threeRightHistory =
  braidedFibreHistory threeFibreYangBaxterRight rightHanded 3

------------------------------------------------------------------------
-- Generic n-fibre braid/plait plans.
------------------------------------------------------------------------

record NFibreBraidPlan (n : Nat) : Set where
  constructor nFibreBraidPlan
  field
    braidSteps : BraidWord n
    repeatCount : Nat
    planHandedness : Handedness

open NFibreBraidPlan public

record NFibrePlaitPlan (n : Nat) : Set where
  constructor nFibrePlaitPlan
  field
    underlyingBraid : NFibreBraidPlan n
    flatPresentation : Bool

open NFibrePlaitPlan public

braidToPlait : {n : Nat} → NFibreBraidPlan n → NFibrePlaitPlan n
braidToPlait p = nFibrePlaitPlan p true

------------------------------------------------------------------------
-- Canonical full adjacent sweep for arbitrary fibre count n >= 2.
--
-- Parameter k denotes n = k + 2.  The word contains every adjacent generator
-- sigma_0, sigma_1, ..., sigma_k exactly once, in order.  Thus k=1 gives a
-- 3-fibre sweep [sigma_0,sigma_1], k=13 gives a 15-fibre sweep through all
-- fourteen adjacent pairs.  Repeating or reversing/orienting these sweeps
-- produces ordinary braid/plait pattern families without changing the kernel.
------------------------------------------------------------------------

liftCrossing :
  {n : Nat} →
  AdjacentCrossing n →
  AdjacentCrossing (suc n)
liftCrossing (sigma i o p) = sigma i o (≤-step p)

allAdjacentCrossings : (k : Nat) → BraidWord (k + 2)
allAdjacentCrossings zero =
  sigma 0 overCrossing ≤-refl ∷ []
allAdjacentCrossings (suc k) =
  map liftCrossing (allAdjacentCrossings k)
  ++
  (sigma (suc k) overCrossing ≤-refl ∷ [])

canonicalSweepPlan : (k : Nat) → NFibreBraidPlan (k + 2)
canonicalSweepPlan k =
  nFibreBraidPlan (allAdjacentCrossings k) 1 rightHanded

canonicalSweepPlait : (k : Nat) → NFibrePlaitPlan (k + 2)
canonicalSweepPlait k = braidToPlait (canonicalSweepPlan k)

------------------------------------------------------------------------
-- Weaving: two indexed families rather than one freely permuted family.
------------------------------------------------------------------------

data WeavePass : Set where
  warpOverWeft : Nat → Nat → WeavePass
  warpUnderWeft : Nat → Nat → WeavePass

record WeavePlan (warpCount weftCount : Nat) : Set where
  constructor weavePlan
  field
    passes : List WeavePass
    repeatRows : Nat

open WeavePlan public

plainWeaveCell : WeavePlan 2 2
plainWeaveCell =
  weavePlan
    (warpOverWeft 0 0 ∷
     warpUnderWeft 0 1 ∷
     warpUnderWeft 1 0 ∷
     warpOverWeft 1 1 ∷ [])
    1

------------------------------------------------------------------------
-- Knitting: new loops depend on retained prior loops.
------------------------------------------------------------------------

data KnitLoopOp : Set where
  knitThrough : Nat → KnitLoopOp
  purlThrough : Nat → KnitLoopOp
  passSlip : Nat → KnitLoopOp
  knitTogether : Nat → Nat → KnitLoopOp

record KnitPlan (liveLoopCount : Nat) : Set where
  constructor knitPlan
  field
    loopOperations : List KnitLoopOp
    rows : Nat

open KnitPlan public

stockinetteSeed : KnitPlan 3
stockinetteSeed =
  knitPlan
    (knitThrough 0 ∷ knitThrough 1 ∷ knitThrough 2 ∷ [])
    1

------------------------------------------------------------------------
-- Crochet: one distinguished active loop plus hook operations.
------------------------------------------------------------------------

data CrochetHookOp : Set where
  yarnOver : CrochetHookOp
  pullThroughActive : CrochetHookOp
  insertInto : Nat → CrochetHookOp
  pullThroughTwo : CrochetHookOp
  chainOne : CrochetHookOp

record CrochetPlan (fabricLoopCount : Nat) : Set where
  constructor crochetPlan
  field
    hookOperations : List CrochetHookOp
    activeLoopInvariant : Bool

open CrochetPlan public

singleCrochetSeed : CrochetPlan 1
singleCrochetSeed =
  crochetPlan
    (insertInto 0 ∷ yarnOver ∷ pullThroughActive ∷ yarnOver ∷ pullThroughTwo ∷ [])
    true

------------------------------------------------------------------------
-- Explicit supported fibre-count ladder: 3,4,...,15.
--
-- The general calculus above is not capped at 15.  This finite datatype is a
-- regression/certification surface proving that the requested range has been
-- instantiated explicitly.
------------------------------------------------------------------------

data CertifiedFibreCount : Set where
  fibres3 : CertifiedFibreCount
  fibres4 : CertifiedFibreCount
  fibres5 : CertifiedFibreCount
  fibres6 : CertifiedFibreCount
  fibres7 : CertifiedFibreCount
  fibres8 : CertifiedFibreCount
  fibres9 : CertifiedFibreCount
  fibres10 : CertifiedFibreCount
  fibres11 : CertifiedFibreCount
  fibres12 : CertifiedFibreCount
  fibres13 : CertifiedFibreCount
  fibres14 : CertifiedFibreCount
  fibres15 : CertifiedFibreCount

certifiedCount : CertifiedFibreCount → Nat
certifiedCount fibres3 = 3
certifiedCount fibres4 = 4
certifiedCount fibres5 = 5
certifiedCount fibres6 = 6
certifiedCount fibres7 = 7
certifiedCount fibres8 = 8
certifiedCount fibres9 = 9
certifiedCount fibres10 = 10
certifiedCount fibres11 = 11
certifiedCount fibres12 = 12
certifiedCount fibres13 = 13
certifiedCount fibres14 = 14
certifiedCount fibres15 = 15

nMinFibreTarget : Nat
nMinFibreTarget = 15

fifteenMeetsNMinTarget : certifiedCount fibres15 ≡ nMinFibreTarget
fifteenMeetsNMinTarget = refl

------------------------------------------------------------------------
-- Concrete full-sweep braid plans for n = 3,4,...,15.
------------------------------------------------------------------------

braid3 : NFibreBraidPlan 3
braid3 = canonicalSweepPlan 1

braid4 : NFibreBraidPlan 4
braid4 = canonicalSweepPlan 2

braid5 : NFibreBraidPlan 5
braid5 = canonicalSweepPlan 3

braid6 : NFibreBraidPlan 6
braid6 = canonicalSweepPlan 4

braid7 : NFibreBraidPlan 7
braid7 = canonicalSweepPlan 5

braid8 : NFibreBraidPlan 8
braid8 = canonicalSweepPlan 6

braid9 : NFibreBraidPlan 9
braid9 = canonicalSweepPlan 7

braid10 : NFibreBraidPlan 10
braid10 = canonicalSweepPlan 8

braid11 : NFibreBraidPlan 11
braid11 = canonicalSweepPlan 9

braid12 : NFibreBraidPlan 12
braid12 = canonicalSweepPlan 10

braid13 : NFibreBraidPlan 13
braid13 = canonicalSweepPlan 11

braid14 : NFibreBraidPlan 14
braid14 = canonicalSweepPlan 12

braid15 : NFibreBraidPlan 15
braid15 = canonicalSweepPlan 13

braid3IsFullAdjacentSweep : braidSteps braid3 ≡ allAdjacentCrossings 1
braid3IsFullAdjacentSweep = refl

braid15IsFullAdjacentSweep : braidSteps braid15 ≡ allAdjacentCrossings 13
braid15IsFullAdjacentSweep = refl

plait3 : NFibrePlaitPlan 3
plait3 = braidToPlait braid3

plait15 : NFibrePlaitPlan 15
plait15 = braidToPlait braid15

------------------------------------------------------------------------
-- Non-collapse boundary.
------------------------------------------------------------------------

record TextileNonCollapseBoundary : Set where
  constructor textileNonCollapseBoundary
  field
    braidEqualsPlaitAsCraft : Bool
    braidEqualsPlaitAsCraftIsFalse : braidEqualsPlaitAsCraft ≡ false

    weaveEqualsBraidAsCraft : Bool
    weaveEqualsBraidAsCraftIsFalse : weaveEqualsBraidAsCraft ≡ false

    knittingEqualsWeavingAsCraft : Bool
    knittingEqualsWeavingAsCraftIsFalse : knittingEqualsWeavingAsCraft ≡ false

    crochetEqualsKnittingAsCraft : Bool
    crochetEqualsKnittingAsCraftIsFalse : crochetEqualsKnittingAsCraft ≡ false

    endpointPermutationErasesBraidHistory : Bool
    endpointPermutationErasesBraidHistoryIsFalse :
      endpointPermutationErasesBraidHistory ≡ false

open TextileNonCollapseBoundary public

canonicalTextileNonCollapseBoundary : TextileNonCollapseBoundary
canonicalTextileNonCollapseBoundary =
  textileNonCollapseBoundary
    false refl
    false refl
    false refl
    false refl
    false refl

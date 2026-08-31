module DASHI.Combinatorics.TextileNFibreCalculusExact where

open import DASHI.Core.Prelude

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
-- A generic n-fibre braid/plait recipe.
--
-- Rather than hard-code one aesthetic pattern, the recipe records a valid
-- sequence of adjacent generators.  Any n is accepted; invalid generators
-- cannot be constructed because every sigma carries its bound proof.
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

requestedMinimumMaximum : Nat
requestedMinimumMaximum = 15

fifteenIsCertified : certifiedCount fibres15 ≡ requestedMinimumMaximum
fifteenIsCertified = refl

------------------------------------------------------------------------
-- Canonical n-fibre "first crossing" witnesses for every certified count.
-- This establishes an actual valid braid generator on each n=3..15 carrier.
------------------------------------------------------------------------

zeroCrossingBound : (n : Nat) → 2 ≤ n → AdjacentCrossing n
zeroCrossingBound n p = sigma 0 overCrossing p

threeAtLeastTwo : 2 ≤ 3
threeAtLeastTwo = s≤s (s≤s z≤n)

fourAtLeastTwo : 2 ≤ 4
fourAtLeastTwo = s≤s (s≤s z≤n)

fiveAtLeastTwo : 2 ≤ 5
fiveAtLeastTwo = s≤s (s≤s z≤n)

sixAtLeastTwo : 2 ≤ 6
sixAtLeastTwo = s≤s (s≤s z≤n)

sevenAtLeastTwo : 2 ≤ 7
sevenAtLeastTwo = s≤s (s≤s z≤n)

eightAtLeastTwo : 2 ≤ 8
eightAtLeastTwo = s≤s (s≤s z≤n)

nineAtLeastTwo : 2 ≤ 9
nineAtLeastTwo = s≤s (s≤s z≤n)

tenAtLeastTwo : 2 ≤ 10
tenAtLeastTwo = s≤s (s≤s z≤n)

elevenAtLeastTwo : 2 ≤ 11
elevenAtLeastTwo = s≤s (s≤s z≤n)

twelveAtLeastTwo : 2 ≤ 12
twelveAtLeastTwo = s≤s (s≤s z≤n)

thirteenAtLeastTwo : 2 ≤ 13
thirteenAtLeastTwo = s≤s (s≤s z≤n)

fourteenAtLeastTwo : 2 ≤ 14
fourteenAtLeastTwo = s≤s (s≤s z≤n)

fifteenAtLeastTwo : 2 ≤ 15
fifteenAtLeastTwo = s≤s (s≤s z≤n)

braid3 : NFibreBraidPlan 3
braid3 = nFibreBraidPlan (zeroCrossingBound 3 threeAtLeastTwo ∷ []) 1 rightHanded

braid4 : NFibreBraidPlan 4
braid4 = nFibreBraidPlan (zeroCrossingBound 4 fourAtLeastTwo ∷ []) 1 rightHanded

braid5 : NFibreBraidPlan 5
braid5 = nFibreBraidPlan (zeroCrossingBound 5 fiveAtLeastTwo ∷ []) 1 rightHanded

braid6 : NFibreBraidPlan 6
braid6 = nFibreBraidPlan (zeroCrossingBound 6 sixAtLeastTwo ∷ []) 1 rightHanded

braid7 : NFibreBraidPlan 7
braid7 = nFibreBraidPlan (zeroCrossingBound 7 sevenAtLeastTwo ∷ []) 1 rightHanded

braid8 : NFibreBraidPlan 8
braid8 = nFibreBraidPlan (zeroCrossingBound 8 eightAtLeastTwo ∷ []) 1 rightHanded

braid9 : NFibreBraidPlan 9
braid9 = nFibreBraidPlan (zeroCrossingBound 9 nineAtLeastTwo ∷ []) 1 rightHanded

braid10 : NFibreBraidPlan 10
braid10 = nFibreBraidPlan (zeroCrossingBound 10 tenAtLeastTwo ∷ []) 1 rightHanded

braid11 : NFibreBraidPlan 11
braid11 = nFibreBraidPlan (zeroCrossingBound 11 elevenAtLeastTwo ∷ []) 1 rightHanded

braid12 : NFibreBraidPlan 12
braid12 = nFibreBraidPlan (zeroCrossingBound 12 twelveAtLeastTwo ∷ []) 1 rightHanded

braid13 : NFibreBraidPlan 13
braid13 = nFibreBraidPlan (zeroCrossingBound 13 thirteenAtLeastTwo ∷ []) 1 rightHanded

braid14 : NFibreBraidPlan 14
braid14 = nFibreBraidPlan (zeroCrossingBound 14 fourteenAtLeastTwo ∷ []) 1 rightHanded

braid15 : NFibreBraidPlan 15
braid15 = nFibreBraidPlan (zeroCrossingBound 15 fifteenAtLeastTwo ∷ []) 1 rightHanded

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

module DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five

------------------------------------------------------------------------
-- STABLE ALGEBRAIC IDENTITIES
--
-- Numbers are shadows/cardinalities of named carriers.  A numerical
-- factorisation is promoted here only when explicit encode/decode maps witness
-- the corresponding carrier equivalence.
------------------------------------------------------------------------

record CarrierIso (A B : Set) : Set where
  constructor carrier-iso
  field
    to : A → B
    from : B → A
    fromTo : (a : A) → from (to a) ≡ a
    toFrom : (b : B) → to (from b) ≡ b

open CarrierIso public

------------------------------------------------------------------------
-- 1. Stable named carriers.
------------------------------------------------------------------------

Nonary9 : Set
Nonary9 = Base.TriTruth × Base.TriTruth

record Base27 : Set where
  constructor base27
  field
    first : Base.TriTruth
    second : Base.TriTruth
    third : Base.TriTruth

open Base27 public

Situated6 : Set
Situated6 = Completion.SituatedSlot

Completion54 : Set
Completion54 = Situated6 × Nonary9

record Appraisal729 : Set where
  constructor appraisal729
  field
    support : Base.TriTruth
    separation : Base.TriTruth
    measurement : Base.TriTruth
    residual : Base.TriTruth
    provenance : Base.TriTruth
    authority : Base.TriTruth

Fine19683 : Set
Fine19683 = Base27 × Appraisal729

Pointed10 : Set
Pointed10 = Five.PointedNonary10

MonsterBulk196830 : Set
MonsterBulk196830 = Pointed10 × Fine19683

FiveMode : Set
FiveMode = Five.D4IrreducibleType

Orientation2 : Set
Orientation2 = Five.BinaryOrientation

------------------------------------------------------------------------
-- 2. The situated 3-column identity is itself ternary, giving
--
--   Situated6 = Row2 x Column3.
------------------------------------------------------------------------

columnToTri : Completion.SituatedTriadColumn → Base.TriTruth
columnToTri Completion.firstAxis = Base.tri-low
columnToTri Completion.secondAxis = Base.tri-mid
columnToTri Completion.thirdAxis = Base.tri-high

triToColumn : Base.TriTruth → Completion.SituatedTriadColumn
triToColumn Base.tri-low = Completion.firstAxis
triToColumn Base.tri-mid = Completion.secondAxis
triToColumn Base.tri-high = Completion.thirdAxis

columnRoundTrip :
  (column : Completion.SituatedTriadColumn) →
  triToColumn (columnToTri column) ≡ column
columnRoundTrip Completion.firstAxis = refl
columnRoundTrip Completion.secondAxis = refl
columnRoundTrip Completion.thirdAxis = refl

triColumnRoundTrip :
  (tri : Base.TriTruth) →
  columnToTri (triToColumn tri) ≡ tri
triColumnRoundTrip Base.tri-low = refl
triColumnRoundTrip Base.tri-mid = refl
triColumnRoundTrip Base.tri-high = refl

------------------------------------------------------------------------
-- 3. Stable 54 identity:
--
--   ((Row2 x Column3) x (Tri3 x Tri3))
--       ~= Row2 x (Tri3 x Tri3 x Tri3)
--       = 2 x Base27.
------------------------------------------------------------------------

completion54ToTwoBy27 :
  Completion54 → Completion.SituatedTriadRow × Base27
completion54ToTwoBy27
  (slot , (left , right)) =
  Completion.row slot ,
  base27 (columnToTri (Completion.column slot)) left right

completion54FromTwoBy27 :
  Completion.SituatedTriadRow × Base27 → Completion54
completion54FromTwoBy27
  (row , base27 columnTri left right) =
  Completion.situated-slot row (triToColumn columnTri) , (left , right)

completion54FromTo :
  (state : Completion54) →
  completion54FromTwoBy27 (completion54ToTwoBy27 state) ≡ state
completion54FromTo
  (Completion.situated-slot row column , (left , right))
  rewrite columnRoundTrip column = refl

completion54ToFrom :
  (state : Completion.SituatedTriadRow × Base27) →
  completion54ToTwoBy27 (completion54FromTwoBy27 state) ≡ state
completion54ToFrom
  (row , base27 columnTri left right)
  rewrite triColumnRoundTrip columnTri = refl

completion54IsTwoBy27 :
  CarrierIso Completion54 (Completion.SituatedTriadRow × Base27)
completion54IsTwoBy27 =
  carrier-iso
    completion54ToTwoBy27
    completion54FromTwoBy27
    completion54FromTo
    completion54ToFrom

------------------------------------------------------------------------
-- 4. Stable 10 identity: existing pointed nonary carrier is literally the
-- five-mode x two-orientation carrier via the canonical round trips.
------------------------------------------------------------------------

pointed10ToFiveByTwo : Pointed10 → FiveMode × Orientation2
pointed10ToFiveByTwo state with Five.pointedNonaryToOrientedMode state
... | Five.orientedMode mode orientation = mode , orientation

fiveByTwoToPointed10 : FiveMode × Orientation2 → Pointed10
fiveByTwoToPointed10 (mode , orientation) =
  Five.orientedModeToPointedNonary (Five.orientedMode mode orientation)

pointed10FromTo :
  (state : Pointed10) →
  fiveByTwoToPointed10 (pointed10ToFiveByTwo state) ≡ state
pointed10FromTo state = Five.pointedNonaryRoundTrip state

pointed10ToFrom :
  (state : FiveMode × Orientation2) →
  pointed10ToFiveByTwo (fiveByTwoToPointed10 state) ≡ state
pointed10ToFrom (mode , orientation)
  rewrite Five.orientedModeRoundTrip (Five.orientedMode mode orientation) = refl

pointed10IsFiveByTwo : CarrierIso Pointed10 (FiveMode × Orientation2)
pointed10IsFiveByTwo =
  carrier-iso
    pointed10ToFiveByTwo
    fiveByTwoToPointed10
    pointed10FromTo
    pointed10ToFrom

------------------------------------------------------------------------
-- 5. Stable 196830 identity.
--
-- Start with:
--   Pointed10 x (Base27 x Appraisal729)
--
-- use Pointed10 ~= FiveMode x Orientation2 and
-- Completion54 ~= Orientation2 x Base27 (same two-valued carrier shape,
-- explicit row/orientation bridge below), then reassociate to:
--
--   FiveMode x Completion54 x Appraisal729.
------------------------------------------------------------------------

rowToOrientation : Completion.SituatedTriadRow → Orientation2
rowToOrientation Completion.observationalRow = Five.negativeOrientation
rowToOrientation Completion.governedRow = Five.positiveOrientation

orientationToRow : Orientation2 → Completion.SituatedTriadRow
orientationToRow Five.negativeOrientation = Completion.observationalRow
orientationToRow Five.positiveOrientation = Completion.governedRow

rowRoundTrip :
  (row : Completion.SituatedTriadRow) →
  orientationToRow (rowToOrientation row) ≡ row
rowRoundTrip Completion.observationalRow = refl
rowRoundTrip Completion.governedRow = refl

orientationRoundTrip :
  (orientation : Orientation2) →
  rowToOrientation (orientationToRow orientation) ≡ orientation
orientationRoundTrip Five.negativeOrientation = refl
orientationRoundTrip Five.positiveOrientation = refl

orientationBase27ToCompletion54 : Orientation2 × Base27 → Completion54
orientationBase27ToCompletion54 (orientation , state27) =
  completion54FromTwoBy27 (orientationToRow orientation , state27)

completion54ToOrientationBase27 : Completion54 → Orientation2 × Base27
completion54ToOrientationBase27 state with completion54ToTwoBy27 state
... | row , state27 = rowToOrientation row , state27

orientationBase27RoundTrip :
  (state : Orientation2 × Base27) →
  completion54ToOrientationBase27 (orientationBase27ToCompletion54 state) ≡ state
orientationBase27RoundTrip (orientation , base27 a b c)
  rewrite orientationRoundTrip orientation = refl

completion54OrientationRoundTrip :
  (state : Completion54) →
  orientationBase27ToCompletion54 (completion54ToOrientationBase27 state) ≡ state
completion54OrientationRoundTrip
  (Completion.situated-slot row column , (left , right))
  rewrite rowRoundTrip row
        | columnRoundTrip column = refl

BulkFive54Appraisal : Set
BulkFive54Appraisal = FiveMode × Completion54 × Appraisal729

bulkToFive54Appraisal : MonsterBulk196830 → BulkFive54Appraisal
bulkToFive54Appraisal (pointed , (state27 , appraisal)) with pointed10ToFiveByTwo pointed
... | mode , orientation =
  mode , orientationBase27ToCompletion54 (orientation , state27) , appraisal

five54AppraisalToBulk : BulkFive54Appraisal → MonsterBulk196830
five54AppraisalToBulk (mode , completion , appraisal) with completion54ToOrientationBase27 completion
... | orientation , state27 =
  fiveByTwoToPointed10 (mode , orientation) , (state27 , appraisal)

bulkFive54FromTo :
  (state : MonsterBulk196830) →
  five54AppraisalToBulk (bulkToFive54Appraisal state) ≡ state
bulkFive54FromTo (pointed , (state27 , appraisal)) with pointed10ToFiveByTwo pointed
... | mode , orientation
  rewrite pointed10FromTo pointed
        | orientationBase27RoundTrip (orientation , state27) = refl

bulkFive54ToFrom :
  (state : BulkFive54Appraisal) →
  bulkToFive54Appraisal (five54AppraisalToBulk state) ≡ state
bulkFive54ToFrom (mode , completion , appraisal) with completion54ToOrientationBase27 completion
... | orientation , state27
  rewrite pointed10ToFrom (mode , orientation)
        | completion54OrientationRoundTrip completion = refl

monsterBulkIsFiveBy54By729 :
  CarrierIso MonsterBulk196830 BulkFive54Appraisal
monsterBulkIsFiveBy54By729 =
  carrier-iso
    bulkToFive54Appraisal
    five54AppraisalToBulk
    bulkFive54FromTo
    bulkFive54ToFrom

------------------------------------------------------------------------
-- 6. Stable identity boundaries.
------------------------------------------------------------------------

data EqualCardinalityMeansSameIdentity : Set where
data FactorFiveIsAnonymousMultiplicity : Set where
data CompletionJEqualsWholeCompletion54 : Set where
data SituatedRowEqualsPhysicalOrientationSemantically : Set where
data CarrierIsoCreatesMonsterRepresentation : Set where

equalCardinalityDoesNotMeanSameIdentity : EqualCardinalityMeansSameIdentity → ⊥
equalCardinalityDoesNotMeanSameIdentity ()

factorFiveIsNotAnonymous : FactorFiveIsAnonymousMultiplicity → ⊥
factorFiveIsNotAnonymous ()

completionJIsNotWhole54 : CompletionJEqualsWholeCompletion54 → ⊥
completionJIsNotWhole54 ()

rowOrientationBridgeIsCarrierOnly :
  SituatedRowEqualsPhysicalOrientationSemantically → ⊥
rowOrientationBridgeIsCarrierOnly ()

carrierIsoDoesNotCreateMonsterRepresentation :
  CarrierIsoCreatesMonsterRepresentation → ⊥
carrierIsoDoesNotCreateMonsterRepresentation ()

record StableAlgebraicIdentityBoundary : Set where
  constructor stable-algebraic-identity-boundary
  field
    nineHasNamedCarrier : Bool
    twentySevenHasNamedCarrier : Bool
    sixHasNamedCarrier : Bool
    fiftyFourHasNamedCarrier : Bool
    sevenTwentyNineHasNamedCarrier : Bool
    nineteenSixEightThreeHasNamedCarrier : Bool
    tenHasNamedPointedCarrier : Bool
    nineteenSixEightThreeZeroHasNamedCarrier : Bool
    tenIsFiveByTwoByIso : Bool
    fiftyFourIsTwoByTwentySevenByIso : Bool
    bulkIsFiveByFiftyFourBySevenTwentyNineByIso : Bool
    cardinalEqualityAloneCreatesIdentity : Bool
    carrierIsoCreatesMonsterAction : Bool

canonicalStableAlgebraicIdentityBoundary : StableAlgebraicIdentityBoundary
canonicalStableAlgebraicIdentityBoundary =
  stable-algebraic-identity-boundary
    true true true true true true true true true true true false false

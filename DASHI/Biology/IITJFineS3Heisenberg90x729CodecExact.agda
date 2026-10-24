module DASHI.Biology.IITJFineS3Heisenberg90x729CodecExact where

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact as Gauge
import DASHI.Biology.IITJFineS3RegularMonsterCharacterExact as C3Regular
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Heisenberg
import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as Monster

------------------------------------------------------------------------
-- A *concrete source-typed 90 x 729 chart*, NOT a Weyl representation.
-- In the previous module the actual original pointed 10*3^9 harmonic
-- carrier is recoded as:
--   ((ten-marker, relative edges4, relative corners4), centre C3).
-- Here split the 8 relative trits into 2 distinguished relative edge
-- values, plus the remaining 6. That gives:
--   [coarse10 x phase-pair9] x [six-trit729] x [centre3]
--             90           x      729     x      3
--        = 65610 regular C3 orbit labels x 3
--        = 196830 pointed states.
--
-- Earlier Monster3BHeisenbergMultiplicityExact source owns the
-- independent 65610 = 90 * 3^6 factor and the exceptional multiplicity
-- decomposition 90 = 12 + 78. We DO NOT identify the six-trit chart
-- with a genuine 3^6 Heisenberg/Suzuki representation by dimension alone.
------------------------------------------------------------------------

record TwoTrit : Set where
  constructor twoTrit
  field
    first second : Base.TriTruth
open TwoTrit public

record SixTrit : Set where
  constructor sixTrit
  field
    one two three four five six : Base.TriTruth
open SixTrit public

NinetyLabel : Set
NinetyLabel = Harmonic.CoarseChannel × TwoTrit

NinetyBy729 : Set
NinetyBy729 = NinetyLabel × SixTrit

toNinetyBy729 : C3Regular.OrbitLabel → NinetyBy729
toNinetyBy729
  (coarse , (Gauge.fourTrit a b c d , Gauge.fourTrit e f g h)) =
  (coarse , twoTrit a b) , sixTrit c d e f g h

fromNinetyBy729 : NinetyBy729 → C3Regular.OrbitLabel
fromNinetyBy729
  ((coarse , twoTrit a b) , sixTrit c d e f g h) =
  coarse , (Gauge.fourTrit a b c d , Gauge.fourTrit e f g h)

toAfterFrom :
  (w : NinetyBy729) → toNinetyBy729 (fromNinetyBy729 w) ≡ w
toAfterFrom ((coarse , twoTrit a b) , sixTrit c d e f g h) = refl

fromAfterTo :
  (o : C3Regular.OrbitLabel) → fromNinetyBy729 (toNinetyBy729 o) ≡ o
fromAfterTo
  (coarse , (Gauge.fourTrit a b c d , Gauge.fourTrit e f g h)) = refl

NinetyBy729WithCentre : Set
NinetyBy729WithCentre = NinetyBy729 × Base.TriTruth

sourceToHeisenbergShape :
  Harmonic.ElementaryHarmonicChannel → NinetyBy729WithCentre
sourceToHeisenbergShape source with C3Regular.toRegularC3 source
... | label , centre = toNinetyBy729 label , centre

heisenbergShapeToSource :
  NinetyBy729WithCentre → Harmonic.ElementaryHarmonicChannel
heisenbergShapeToSource (shape , centre) =
  C3Regular.fromRegularC3 (fromNinetyBy729 shape , centre)

sourceShapeAfterSource :
  (source : Harmonic.ElementaryHarmonicChannel) →
  heisenbergShapeToSource (sourceToHeisenbergShape source) ≡ source
sourceShapeAfterSource source
  with C3Regular.toRegularC3 source
... | label , centre
  rewrite fromAfterTo label = C3Regular.regularAfterSource source

shapeSourceAfterShape :
  (shape : NinetyBy729WithCentre) →
  sourceToHeisenbergShape (heisenbergShapeToSource shape) ≡ shape
shapeSourceAfterShape (shape , centre)
  rewrite
    C3Regular.sourceAfterRegular
      (fromNinetyBy729 shape , centre)
  | toAfterFrom shape = refl

heisenbergBlockIs729 : 3 * 3 * 3 * 3 * 3 * 3 ≡ Heisenberg.threePowerSix
heisenbergBlockIs729 = refl

ninetyTimes729MatchesMonsterC3BulkPhase :
  90 * Heisenberg.threePowerSix ≡ Monster.regularC3Multiplicity
ninetyTimes729MatchesMonsterC3BulkPhase = Heisenberg.ninetyTimesThreePowerSixIs65610

pointedSourceMatchesThreeRegularPhases :
  3 * (90 * Heisenberg.threePowerSix) ≡ 196830
pointedSourceMatchesThreeRegularPhases = refl

record NinetyBy729ActualActionBoundary : Set where
  constructor ninety-by729-actual-action-boundary
  field
    actualPointedSourceCodecSourceWritten : Bool
    priorHeisenbergMultiplicityArithmeticReused : Bool
    literalMonsterHeisenbergWeylActionIdentified : Bool
    actualSuzukiNinetyMultiplicityActionIdentified : Bool
    sourceTenMarkerTimesNineMatchesNinety : Bool
    AgdaExactHeadKernelReceipt : Bool

canonicalBoundary : NinetyBy729ActualActionBoundary
canonicalBoundary =
  ninety-by729-actual-action-boundary
    true true false false true false

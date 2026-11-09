module DASHI.Foundations.TernaryThirteenTwoChartOverlapGluingExact where

------------------------------------------------------------------------
-- H2.02: a nontrivial TWO-CHART OVERLAP covering the original 12
-- StageAtlas axes. This is not the singleton/discrete-stage
-- maximal-only cover: chart L={0..6}, R={6..11}, with actual
-- intersection at stage 6. Matching needs two independent facts:
-- both chart valuations agree at stage 6; both central trits agree.
--
-- The explicit gluing constructs the SAME original source valuation
-- plus central TriTruth and re-restricts to both charts. It is a
-- finite set-cover / matching-family theorem, not an assertion
-- that the original discrete Grothendieck topology was changed
-- or that all covers of an unselected site already descend.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

data LeftChartAxis : Set where
  left0 left1 left2 left3 left4 left5 left6 : LeftChartAxis

data RightChartAxis : Set where
  right6 right7 right8 right9 right10 right11 : RightChartAxis

leftAxis : LeftChartAxis → Atlas.StageAtlasZeroToEleven
leftAxis left0 = Atlas.atlas-0
leftAxis left1 = Atlas.atlas-1
leftAxis left2 = Atlas.atlas-2
leftAxis left3 = Atlas.atlas-3
leftAxis left4 = Atlas.atlas-4
leftAxis left5 = Atlas.atlas-5
leftAxis left6 = Atlas.atlas-6

rightAxis : RightChartAxis → Atlas.StageAtlasZeroToEleven
rightAxis right6 = Atlas.atlas-6
rightAxis right7 = Atlas.atlas-7
rightAxis right8 = Atlas.atlas-8
rightAxis right9 = Atlas.atlas-9
rightAxis right10 = Atlas.atlas-10
rightAxis right11 = Atlas.atlas-11

-- Both actual charts refer to the *same* atlas-6 address.
chartIntersectionIsSameAxis :
  leftAxis left6 ≡ rightAxis right6
chartIntersectionIsSameAxis = refl

record TwoChartCentralFamily : Set where
  constructor two-chart-central-family
  field
    leftValue : LeftChartAxis → Base.TriTruth
    rightValue : RightChartAxis → Base.TriTruth
    leftCentre : Base.TriTruth
    rightCentre : Base.TriTruth
open TwoChartCentralFamily public

record TwoChartMatches (charts : TwoChartCentralFamily) : Set where
  constructor two-chart-matches
  field
    overlapMatches :
      leftValue charts left6 ≡ rightValue charts right6
    centreMatches :
      leftCentre charts ≡ rightCentre charts
open TwoChartMatches public

gluedValuation :
  TwoChartCentralFamily → Rel.SourceTwelveAxisValuation
gluedValuation charts Atlas.atlas-0 = leftValue charts left0
gluedValuation charts Atlas.atlas-1 = leftValue charts left1
gluedValuation charts Atlas.atlas-2 = leftValue charts left2
gluedValuation charts Atlas.atlas-3 = leftValue charts left3
gluedValuation charts Atlas.atlas-4 = leftValue charts left4
gluedValuation charts Atlas.atlas-5 = leftValue charts left5
gluedValuation charts Atlas.atlas-6 = leftValue charts left6
gluedValuation charts Atlas.atlas-7 = rightValue charts right7
gluedValuation charts Atlas.atlas-8 = rightValue charts right8
gluedValuation charts Atlas.atlas-9 = rightValue charts right9
gluedValuation charts Atlas.atlas-10 = rightValue charts right10
gluedValuation charts Atlas.atlas-11 = rightValue charts right11

glueTwoChartCentral :
  (charts : TwoChartCentralFamily) →
  TwoChartMatches charts →
  Rel.SourceCentralCompletionCarrier
glueTwoChartCentral charts matching =
  gluedValuation charts , leftCentre charts

-- Chart A is chosen on overlap; right restriction on atlas-6
-- needs exactly the nontrivial overlap matching hypothesis.
twoChartLeftRestricts :
  (charts : TwoChartCentralFamily)
  (matching : TwoChartMatches charts)
  (axis : LeftChartAxis) →
  proj₁ (glueTwoChartCentral charts matching) (leftAxis axis)
  ≡ leftValue charts axis
twoChartLeftRestricts charts matching left0 = refl
twoChartLeftRestricts charts matching left1 = refl
twoChartLeftRestricts charts matching left2 = refl
twoChartLeftRestricts charts matching left3 = refl
twoChartLeftRestricts charts matching left4 = refl
twoChartLeftRestricts charts matching left5 = refl
twoChartLeftRestricts charts matching left6 = refl

twoChartRightRestricts :
  (charts : TwoChartCentralFamily)
  (matching : TwoChartMatches charts)
  (axis : RightChartAxis) →
  proj₁ (glueTwoChartCentral charts matching) (rightAxis axis)
  ≡ rightValue charts axis
twoChartRightRestricts charts matching right6 = overlapMatches matching
twoChartRightRestricts charts matching right7 = refl
twoChartRightRestricts charts matching right8 = refl
twoChartRightRestricts charts matching right9 = refl
twoChartRightRestricts charts matching right10 = refl
twoChartRightRestricts charts matching right11 = refl

twoChartLeftCentreRestricts :
  (charts : TwoChartCentralFamily)
  (matching : TwoChartMatches charts) →
  proj₂ (glueTwoChartCentral charts matching)
  ≡ leftCentre charts
twoChartLeftCentreRestricts charts matching = refl

twoChartRightCentreRestricts :
  (charts : TwoChartCentralFamily)
  (matching : TwoChartMatches charts) →
  proj₂ (glueTwoChartCentral charts matching)
  ≡ rightCentre charts
twoChartRightCentreRestricts charts matching =
  centreMatches matching

restrictToTwoCharts :
  Rel.SourceCentralCompletionCarrier → TwoChartCentralFamily
restrictToTwoCharts (valuation , centre) =
  two-chart-central-family
    (λ a → valuation (leftAxis a))
    (λ a → valuation (rightAxis a))
    centre centre

restrictedTwoChartsMatch :
  (state : Rel.SourceCentralCompletionCarrier) →
  TwoChartMatches (restrictToTwoCharts state)
restrictedTwoChartsMatch (valuation , centre) =
  two-chart-matches refl refl

-- This proof is stronger than comparing counts: it reconstructs the
-- original selected state pointwise at each stage from TWO genuinely
-- overlapping proper subcharts.
sourceTwoChartGluingRoundTripPointwise :
  (state : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (glueTwoChartCentral
    (restrictToTwoCharts state)
    (restrictedTwoChartsMatch state)) axis
  ≡ proj₁ state axis
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-0 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-1 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-2 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-3 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-4 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-5 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-6 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-7 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-8 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-9 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-10 = refl
sourceTwoChartGluingRoundTripPointwise state Atlas.atlas-11 = refl

sourceTwoChartGluingCentreRoundTrip :
  (state : Rel.SourceCentralCompletionCarrier) →
  proj₂ (glueTwoChartCentral
    (restrictToTwoCharts state)
    (restrictedTwoChartsMatch state))
  ≡ proj₂ state
sourceTwoChartGluingCentreRoundTrip state = refl

-- An incompatible family is an actual obstruction.
badOverlapChartFamily : TwoChartCentralFamily
badOverlapChartFamily =
  two-chart-central-family
    (λ _ → Base.tri-mid)
    (λ _ → Base.tri-high)
    Base.tri-mid Base.tri-mid

badOverlapCannotGlue :
  TwoChartMatches badOverlapChartFamily → ⊥
badOverlapCannotGlue matching with overlapMatches matching
... | ()

-- Even if valuations agree on their intersection, a split centre
-- prevents the two charts from gluing to a single 13th coordinate.
badCentreChartFamily : TwoChartCentralFamily
badCentreChartFamily =
  two-chart-central-family
    (λ _ → Base.tri-mid)
    (λ _ → Base.tri-mid)
    Base.tri-mid Base.tri-high

badCentreCannotGlue :
  TwoChartMatches badCentreChartFamily → ⊥
badCentreCannotGlue matching with centreMatches matching
... | ()

-- Puncturing is compatible with gluing when the COMMON centre
-- is nonneutral; this does not remove neutral full sections.
twoChartPunctureGluing :
  (charts : TwoChartCentralFamily)
  (matching : TwoChartMatches charts) →
  ¬ (leftCentre charts ≡ Base.tri-mid) →
  ¬ (proj₂ (glueTwoChartCentral charts matching) ≡ Base.tri-mid)
twoChartPunctureGluing charts matching punctured = punctured

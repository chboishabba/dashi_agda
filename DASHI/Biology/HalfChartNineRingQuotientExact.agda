module DASHI.Biology.HalfChartNineRingQuotientExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Construct the finite gluing behind
--
--   5 x 2 = 10  and  5 + 5 - 1 = 9.
--
-- Two oriented five-point half charts are unfolded to ten points.  Their
-- distinguished endpoints are identified, giving a nine-point quotient.
-- This pointed half-chart five is not the five-element set of D4 irreducible
-- representation kinds, even though both carriers have cardinality five.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.D4NineCellOrbitCompressionExact as D4

data Half5 : Set where
  h0 h1 h2 h3 h4 : Half5

data Orientation2 : Set where
  direct reflected : Orientation2

data Unfolded10 : Set where
  d0 d1 d2 d3 d4 : Unfolded10
  r0 r1 r2 r3 r4 : Unfolded10

data Quotient9 : Set where
  glued0 : Quotient9
  direct1 direct2 direct3 direct4 : Quotient9
  reflected1 reflected2 reflected3 reflected4 : Quotient9

unfold : Half5 → Orientation2 → Unfolded10
unfold h0 direct = d0
unfold h1 direct = d1
unfold h2 direct = d2
unfold h3 direct = d3
unfold h4 direct = d4
unfold h0 reflected = r0
unfold h1 reflected = r1
unfold h2 reflected = r2
unfold h3 reflected = r3
unfold h4 reflected = r4

quotient : Unfolded10 → Quotient9
quotient d0 = glued0
quotient r0 = glued0
quotient d1 = direct1
quotient d2 = direct2
quotient d3 = direct3
quotient d4 = direct4
quotient r1 = reflected1
quotient r2 = reflected2
quotient r3 = reflected3
quotient r4 = reflected4

baseEndpointsGlue : quotient d0 ≡ quotient r0
baseEndpointsGlue = refl

directNonbaseSurvives :
  quotient d1 ≡ direct1
  × quotient d2 ≡ direct2
  × quotient d3 ≡ direct3
  × quotient d4 ≡ direct4
directNonbaseSurvives = refl , refl , refl , refl

reflectedNonbaseSurvives :
  quotient r1 ≡ reflected1
  × quotient r2 ≡ reflected2
  × quotient r3 ≡ reflected3
  × quotient r4 ≡ reflected4
reflectedNonbaseSurvives = refl , refl , refl , refl

halfChartCount : Nat
halfChartCount = 5

orientationCount : Nat
orientationCount = 2

unfoldedCount : Nat
unfoldedCount = halfChartCount * orientationCount

identifiedEndpointCount : Nat
identifiedEndpointCount = 1

quotientCount : Nat
quotientCount = unfoldedCount ∸ identifiedEndpointCount

unfoldedCountIsTen : unfoldedCount ≡ 10
unfoldedCountIsTen = refl

quotientCountIsNine : quotientCount ≡ 9
quotientCountIsNine = refl

halfUnionCountIsNine : 5 + 5 ∸ 1 ≡ 9
halfUnionCountIsNine = refl

data HalfChartRole : Half5 → Set where
  seamRole : HalfChartRole h0
  firstRole : HalfChartRole h1
  secondRole : HalfChartRole h2
  thirdRole : HalfChartRole h3
  fourthRole : HalfChartRole h4

encodeQuotient : Quotient9 → Σ Half5 (λ half → Orientation2 × HalfChartRole half)
encodeQuotient glued0 = h0 , direct , seamRole
encodeQuotient direct1 = h1 , direct , firstRole
encodeQuotient direct2 = h2 , direct , secondRole
encodeQuotient direct3 = h3 , direct , thirdRole
encodeQuotient direct4 = h4 , direct , fourthRole
encodeQuotient reflected1 = h1 , reflected , firstRole
encodeQuotient reflected2 = h2 , reflected , secondRole
encodeQuotient reflected3 = h3 , reflected , thirdRole
encodeQuotient reflected4 = h4 , reflected , fourthRole

decodeQuotient :
  Σ Half5 (λ half → Orientation2 × HalfChartRole half) →
  Quotient9
decodeQuotient (h0 , direct , seamRole) = glued0
decodeQuotient (h0 , reflected , seamRole) = glued0
decodeQuotient (h1 , direct , firstRole) = direct1
decodeQuotient (h1 , reflected , firstRole) = reflected1
decodeQuotient (h2 , direct , secondRole) = direct2
decodeQuotient (h2 , reflected , secondRole) = reflected2
decodeQuotient (h3 , direct , thirdRole) = direct3
decodeQuotient (h3 , reflected , thirdRole) = reflected3
decodeQuotient (h4 , direct , fourthRole) = direct4
decodeQuotient (h4 , reflected , fourthRole) = reflected4

decodeAfterEncode :
  (point : Quotient9) →
  decodeQuotient (encodeQuotient point) ≡ point
decodeAfterEncode glued0 = refl
decodeAfterEncode direct1 = refl
decodeAfterEncode direct2 = refl
decodeAfterEncode direct3 = refl
decodeAfterEncode direct4 = refl
decodeAfterEncode reflected1 = refl
decodeAfterEncode reflected2 = refl
decodeAfterEncode reflected3 = refl
decodeAfterEncode reflected4 = refl

------------------------------------------------------------------------
-- Keep the two meanings of five typed apart.
------------------------------------------------------------------------

data FiveMeaning : Set where
  pointedHalfChart : FiveMeaning
  d4RepresentationKinds : FiveMeaning

halfChartFiveMeaning : FiveMeaning
halfChartFiveMeaning = pointedHalfChart

d4FiveMeaning : FiveMeaning
d4FiveMeaning = d4RepresentationKinds

fiveMeaningsAreDistinct : halfChartFiveMeaning ≡ d4FiveMeaning → ⊥
fiveMeaningsAreDistinct ()

d4IrrepCountStillFive : D4.listCount D4.canonicalD4IrrepKinds ≡ 5
d4IrrepCountStillFive = D4.d4IrrepKindCountIsFive

record HalfChartBoundary : Set where
  constructor halfChartBoundary
  field
    quotientHasNinePoints : Bool
    quotientHasNinePointsIsTrue : quotientHasNinePoints ≡ true
    fiveMeansD4IrrepKindsHere : Bool
    fiveMeansD4IrrepKindsHereIsFalse : fiveMeansD4IrrepKindsHere ≡ false
    cardinalityCoincidenceIdentifiesCarriers : Bool
    cardinalityCoincidenceIdentifiesCarriersIsFalse :
      cardinalityCoincidenceIdentifiesCarriers ≡ false

canonicalHalfChartBoundary : HalfChartBoundary
canonicalHalfChartBoundary = halfChartBoundary true refl false refl false refl

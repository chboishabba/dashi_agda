{-# OPTIONS --safe #-}

module DASHI.Education.DigitalESDGoldenIntersectionalKernelExact where

-- GOLDEN, SELF-CONTAINED FINITE/KERNEL MATHEMATICS.
-- No postulates, no rewrite pragmas, no asserted external theorem receipts.
-- Original conceptual motivations: Kimberle Crenshaw (1991) on situated
-- intersectionality; Blackwell (1953) on information and observation.
-- These finite propositions are DASHI's independent mathematics. They do
-- not assert findings about any Digital-ESD participants or papers.

open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record Lossless {Situated Summary : Set}
  (project : Situated → Summary) : Set where
  constructor lossless
  field
    recover : Summary → Situated
    leftInverse : (s : Situated) → recover (project s) ≡ s

open Lossless public

record FactorsThrough {Situated Summary Answer : Set}
  (project : Situated → Summary)
  (answer : Situated → Answer) : Set where
  constructor factors-through
  field
    interpret : Summary → Answer
    factors : (s : Situated) → answer s ≡ interpret (project s)

open FactorsThrough public

record Collision {Situated Summary Answer : Set}
  (project : Situated → Summary)
  (answer : Situated → Answer) : Set where
  constructor collision
  field
    first second : Situated
    sameProjection : project first ≡ project second
    answersDistinct : answer first ≡ answer second → Empty

open Collision public

-- G00: lossless projections preserve every exact consumer question.
losslessConsumerFactorisation :
  {Situated Summary Answer : Set}
  (project : Situated → Summary)
  (answer : Situated → Answer) →
  Lossless project → FactorsThrough project answer
losslessConsumerFactorisation project answer cert =
  factors-through
    (λ summary → answer (recover cert summary))
    (λ s → sym (cong answer (leftInverse cert s)))

-- G01: an exact projection collision with distinct answers rules out
-- any purported global recovery map.
collisionRulesOutLossless :
  {Situated Summary Answer : Set}
  (project : Situated → Summary)
  (answer : Situated → Answer) →
  Collision project answer → Lossless project → Empty
collisionRulesOutLossless project answer witness cert =
  answersDistinct witness
    (trans (sym (factors factor (first witness)))
      (trans (cong (interpret factor) (sameProjection witness))
        (factors factor (second witness))))
  where
    factor : FactorsThrough project answer
    factor = losslessConsumerFactorisation project answer cert

-- G02: arbitrary source-part and axis carriers, not fixed 3/9/27.
-- The certificate must reconstruct *every* declared axis observation.
record AllAxisRoundTrip
    {Part Axis : Set}
    (Observation : Part → Axis → Set)
    (Stalk : Part → Set) : Set₁ where
  constructor all-axis-round-trip
  field
    encode :
      (part : Part) →
      ((axis : Axis) → Observation part axis) → Stalk part
    decode :
      (part : Part) →
      Stalk part → ((axis : Axis) → Observation part axis)
    eachAxisRecovered :
      (part : Part) →
      (original : (axis : Axis) → Observation part axis) →
      (axis : Axis) →
      decode part (encode part original) axis ≡ original axis

open AllAxisRoundTrip public

-- G03: the pointwise round-trip is the exact consumer read-back, not
-- an equality of summaries, names, paper DOIs or source-count receipts.
roundTripReadback :
  {Part Axis : Set}
  {Observation : Part → Axis → Set}
  {Stalk : Part → Set} →
  (cert : AllAxisRoundTrip Observation Stalk) →
  (part : Part) →
  (original : (axis : Axis) → Observation part axis) →
  (axis : Axis) →
  decode cert part (encode cert part original) axis ≡ original axis
roundTripReadback cert part original axis =
  eachAxisRecovered cert part original axis

-- G04: a completely worked finite positive witness. The three named
-- axes here are TEST FIXTURE values; there is no upper bound in G02/G03.
data FixturePart : Set where
  questionPart methodPart inferencePart : FixturePart

data FixtureAxis : Set where
  accessAxis agencyAxis ecologyAxis : FixtureAxis

data FixtureValue : Set where
  unresolved reported : FixtureValue

fixtureObservation : FixturePart → FixtureAxis → Set
fixtureObservation part axis = FixtureValue

fixtureStalk : FixturePart → Set
fixtureStalk part = (axis : FixtureAxis) → FixtureValue

fixtureRoundTrip :
  AllAxisRoundTrip fixtureObservation fixtureStalk
fixtureRoundTrip =
  all-axis-round-trip
    (λ part original → original)
    (λ part values → values)
    (λ part original axis → refl)

fixtureEveryAxisSurvives :
  (part : FixturePart) →
  (value : (axis : FixtureAxis) → FixtureValue) →
  (axis : FixtureAxis) →
  decode fixtureRoundTrip part
    (encode fixtureRoundTrip part value) axis ≡ value axis
fixtureEveryAxisSurvives =
  roundTripReadback fixtureRoundTrip

-- G05: negative control: dropping an axis is not lossless merely because
-- the other axis and both study parts remain available.
data TwoStates : Set where
  noCommunityAuthority independentCommunityAuthority : TwoStates

data OneCoarseValue : Set where
  sameObservedEngagement : OneCoarseValue

data DistinctAnswer : Set where
  authorityAbsent authorityPresent : DistinctAnswer

coarseStudyView : TwoStates → OneCoarseValue
coarseStudyView noCommunityAuthority = sameObservedEngagement
coarseStudyView independentCommunityAuthority = sameObservedEngagement

authorityQuestion : TwoStates → DistinctAnswer
authorityQuestion noCommunityAuthority = authorityAbsent
authorityQuestion independentCommunityAuthority = authorityPresent

authorityAnswersDiffer :
  authorityQuestion noCommunityAuthority ≡
  authorityQuestion independentCommunityAuthority → Empty
authorityAnswersDiffer ()

authorityCollision : Collision coarseStudyView authorityQuestion
authorityCollision =
  collision noCommunityAuthority independentCommunityAuthority
    refl authorityAnswersDiffer

coarseStudyViewCannotBeLossless :
  Lossless coarseStudyView → Empty
coarseStudyViewCannotBeLossless =
  collisionRulesOutLossless
    coarseStudyView authorityQuestion authorityCollision

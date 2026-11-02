module DASHI.Education.DigitalESDOpenAxisWorldRegression where

------------------------------------------------------------------------
-- Small executable normalisation witness over the real Taimur/Onuki source
-- identifier. This is a SYNTHETIC missingness/arity test, not source
-- empirical analysis or reviewed full-text admission.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)

import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as W
import DASHI.Education.DigitalESDOpenAxisGapTransportExact as Gap
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS
import DASHI.Algebra.BalancedTernary as Ternary

data TestStudy : Set where
  taimurTestStudy : TestStudy

data TestPart : TestStudy → Set where
  studyQuestion : TestPart taimurTestStudy
  studyMethod : TestPart taimurTestStudy
  studyInference : TestPart taimurTestStudy

data TestAxis : Set where
  participantAuthority : TestAxis
  ecologicalEffect : TestAxis
  historicalDurability : TestAxis

testParts : List (TestPart taimurTestStudy)
testParts = studyQuestion ∷ studyMethod ∷ studyInference ∷ []

testPartsFor : (s : TestStudy) → List (TestPart s)
testPartsFor taimurTestStudy = testParts

testAxes : List TestAxis
testAxes =
  participantAuthority ∷ ecologicalEffect ∷ historicalDurability ∷ []

studyPartName : (s : TestStudy) → TestPart s → String
studyPartName taimurTestStudy studyQuestion = "question"
studyPartName taimurTestStudy studyMethod = "method"
studyPartName taimurTestStudy studyInference = "inference"

testAxisName : TestAxis → String
testAxisName participantAuthority = "participant-authority"
testAxisName ecologicalEffect = "ecological-effect"
testAxisName historicalDurability = "historical-durability"

everyTestPartListed :
  (s : TestStudy) (p : TestPart s) →
  p ∈ testPartsFor s
everyTestPartListed taimurTestStudy studyQuestion = here refl
everyTestPartListed taimurTestStudy studyMethod = there (here refl)
everyTestPartListed taimurTestStudy studyInference = there (there (here refl))

everyTestAxisListed :
  (a : TestAxis) → a ∈ testAxes
everyTestAxisListed participantAuthority = here refl
everyTestAxisListed ecologicalEffect = there (here refl)
everyTestAxisListed historicalDurability = there (there (here refl))

testScope : W.StudyWorldScope
testScope = W.study-world-scope
  TestStudy
  TestPart
  TestAxis
  (λ _ → EfS.taimurOnukiSource)
  (λ _ → "synthetic-study-decomposition-fixture")
  studyPartName
  testAxisName
  (taimurTestStudy ∷ [])
  (λ { taimurTestStudy → here refl })
  testPartsFor
  everyTestPartListed
  testAxes
  everyTestAxisListed
  (λ _ _ _ _ → ⊤)

testWorld : W.AccountedStudyWorld testScope
testWorld = W.accounted-study-world
  (λ s p axis →
    W.unmeasuredForQuestion
      (studyPartName s p)
      (testAxisName axis))

allThreeAxesAccountedAtMethod :
  W.accounting testWorld taimurTestStudy studyMethod historicalDurability
  ≡ W.unmeasuredForQuestion "method" "historical-durability"
allThreeAxesAccountedAtMethod = refl

threePartHigherRelation : W.HigherOrderStudyRelation testScope Nat
threePartHigherRelation = W.higher-order-study-relation
  (W.study-part taimurTestStudy studyQuestion ∷
   W.study-part taimurTestStudy studyMethod ∷
   W.study-part taimurTestStudy studyInference ∷ [])
  (participantAuthority ∷ ecologicalEffect ∷ historicalDurability ∷ [])
  (W.signedTernaryView Ternary.zero)
  "Which higher-order joint dependencies must future EfS research observe?"
  ("DASHI synthetic test; no empirical source observations" ∷ [])
  "ternary is only a relational view"
  "all three part/axis accounts are explicitly unmeasured"

threePartRelationRetainsWorld : W.SituatedWorldRelation testScope Nat
threePartRelationRetainsWorld =
  W.situated-world-relation testWorld threePartHigherRelation

-- One-step extension: the first three axes are recovered exactly and a
-- fourth axis can be addressed without changing a fixed 3/9/27 carrier.
data ExtendedAxis : Set where
  inheritedAxis : TestAxis → ExtendedAxis
  prospectiveCommunityPower : ExtendedAxis

axisExtension : Gap.OpenAxisExtension TestAxis ExtendedAxis
axisExtension = Gap.open-axis-extension
  inheritedAxis
  (λ { (inheritedAxis a) → a ;
       prospectiveCommunityPower → participantAuthority })
  (λ _ → refl)
  "synthetic finite witness of an open axis family"

oldAxesRetained :
  (a : TestAxis) →
  Gap.leftInverse axisExtension (Gap.embed axisExtension a) ≡ a
oldAxesRetained = Gap.originalAxisIsRecovered axisExtension

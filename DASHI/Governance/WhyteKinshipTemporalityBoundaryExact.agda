module DASHI.Governance.WhyteKinshipTemporalityBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousAuthoritySourceRegistryExact as Sources

------------------------------------------------------------------------
-- KYLE POWYS WHYTE: KINSHIP / TEMPORAL OBSERVER BOUNDARY
--
-- Source: Kyle Powys Whyte, "Time as Kinship", The Cambridge Companion to
-- Environmental Humanities (2021), pp. 39-55,
-- DOI 10.1017/9781009039369.005.
--
-- The source motivates a distinction between linear climate-time narration
-- and kinship/justice relations.  DASHI's finite witness does NOT claim that
-- mathematical linear time is invalid or that every Indigenous temporality is
-- represented by this carrier.
------------------------------------------------------------------------

data RelationalHistory : Set where
  disruptedKinRelations sustainedKinRelations : RelationalHistory

data PresentBurdenCode : Set where
  samePresentBurden : PresentBurdenCode

data RelationalJusticeCode : Set where
  disruptedHistory sustainedHistory : RelationalJusticeCode

presentBurdenObserver : RelationalHistory → PresentBurdenCode
presentBurdenObserver disruptedKinRelations = samePresentBurden
presentBurdenObserver sustainedKinRelations = samePresentBurden

relationalHistoryObserver : RelationalHistory → RelationalJusticeCode
relationalHistoryObserver disruptedKinRelations = disruptedHistory
relationalHistoryObserver sustainedKinRelations = sustainedHistory

samePresentBurden :
  presentBurdenObserver disruptedKinRelations ≡
  presentBurdenObserver sustainedKinRelations
samePresentBurden = refl

differentRelationalHistory :
  relationalHistoryObserver disruptedKinRelations ≡
  relationalHistoryObserver sustainedKinRelations → ⊥
differentRelationalHistory ()

presentBurdenDoesNotRecoverRelationalHistory :
  (recover : PresentBurdenCode → RelationalJusticeCode) →
  ((x : RelationalHistory) →
    recover (presentBurdenObserver x) ≡ relationalHistoryObserver x) → ⊥
presentBurdenDoesNotRecoverRelationalHistory recover factors =
  differentRelationalHistory
    (trans (sym (factors disruptedKinRelations)) (factors sustainedKinRelations))

whyteSource : Sources.SourceReference
whyteSource = Sources.whyte2021

record WhyteKinshipTemporalityBoundary : Set where
  constructor whyteKinshipTemporalityBoundary
  field
    samePresentBurdenMeansSameRelationalHistory : Bool
    samePresentBurdenMeansSameRelationalHistoryIsFalse :
      samePresentBurdenMeansSameRelationalHistory ≡ false
    responsibilityStateEqualsResponsibilityTrajectory : Bool
    responsibilityStateEqualsResponsibilityTrajectoryIsFalse :
      responsibilityStateEqualsResponsibilityTrajectory ≡ false
    linearTimeIsMathematicallyInvalid : Bool
    linearTimeIsMathematicallyInvalidIsFalse : linearTimeIsMathematicallyInvalid ≡ false
    finiteWitnessUniversalizesIndigenousTemporality : Bool
    finiteWitnessUniversalizesIndigenousTemporalityIsFalse :
      finiteWitnessUniversalizesIndigenousTemporality ≡ false

canonicalWhyteKinshipTemporalityBoundary : WhyteKinshipTemporalityBoundary
canonicalWhyteKinshipTemporalityBoundary =
  whyteKinshipTemporalityBoundary false refl false refl false refl false refl

module DASHI.Governance.BlackGirlsMatterCRDCAggregationBoundaryExact where

-- A conditional arithmetic/identification theorem for CRDC 2011-12.
-- The 2011-12 survey distinguishes exactly one vs multiple out-of-school
-- suspensions. Other discipline measures may overlap the same students.
-- DASHI-original proof; neither original OCR rows nor a person-level
-- disjointness certificate has been obtained in this module.

open import DASHI.Core.Prelude
import DASHI.Governance.BlackGirlsMatterCRDCOriginalRowAdmissionExact as OCR

-- A generic observed count is a number; a COUNT OF UNIQUE STUDENTS is
-- a source-dependent interpretation, not a property of Nat by itself.
record TwoIndicatorAggregation : Set where
  constructor two-indicator-aggregation
  field
    firstIndicatorCount : Nat
    secondIndicatorCount : Nat
    sameStudentOverlap : Nat
    uniqueStudentsAcrossIndicators : Nat
    countConservation :
      firstIndicatorCount + secondIndicatorCount ≡
      uniqueStudentsAcrossIndicators + sameStudentOverlap

open TwoIndicatorAggregation public

-- A zero-overlap receipt is indispensable to identify an aggregate
-- sum with the unique-student count. If overlap is not separately known,
-- raw totals do not determine the number of people exposed.
disjointCountsRecoverUniqueStudents :
  (a : TwoIndicatorAggregation) →
  sameStudentOverlap a ≡ 0 →
  firstIndicatorCount a + secondIndicatorCount a
    ≡ uniqueStudentsAcrossIndicators a
disjointCountsRecoverUniqueStudents a zeroOverlap
  rewrite zeroOverlap =
  countConservation a

-- Two datasets with EXACTLY the same two category totals can have
-- distinct unique-person counts because overlap differs.
data OverlapScenario : Set where
  separateParticipants sameParticipant : OverlapScenario

categoryOne : OverlapScenario → Nat
categoryOne _ = 1

categoryTwo : OverlapScenario → Nat
categoryTwo _ = 1

uniquePeople : OverlapScenario → Nat
uniquePeople separateParticipants = 2
uniquePeople sameParticipant = 1

sameTwoCategoryCountsCannotRecoverUniquePeople :
  (categoryOne separateParticipants ≡ categoryOne sameParticipant)
  × (categoryTwo separateParticipants ≡ categoryTwo sameParticipant)
  × (uniquePeople separateParticipants ≡ uniquePeople sameParticipant → ⊥)
sameTwoCategoryCountsCannotRecoverUniquePeople =
  refl , (refl , (λ ()))

-- Do not fill an explicit one-suspension/multiple-suspension witness
-- with an inference about the cross-category overlap of EXPULSIONS,
-- ARRESTS and REFERRALS; they are independently measured indicators.
differentCRDCMeasuresAreNotDefinitionalEqual :
  OCR.schoolRelatedArrest ≡ OCR.referralToLawEnforcement → ⊥
differentCRDCMeasuresAreNotDefinitionalEqual ()

differentUnitsAreNotDefinitionalEqual :
  OCR.disciplinaryEvents ≡ OCR.uniqueStudents → ⊥
differentUnitsAreNotDefinitionalEqual ()

record OriginalAggregationReceipt
  (src : OCR.VerifiedCRDCSource)
  (d : OCR.District)
  (g : OCR.Population) : Set where
  constructor original-aggregation-receipt
  field
    oneSuspension :
      OCR.MatchedOriginalCell src OCR.y2011to2012 d g
        OCR.oneOutOfSchoolSuspension
    repeatedSuspension :
      OCR.MatchedOriginalCell src OCR.y2011to2012 d g
        OCR.multipleOutOfSchoolSuspensions
    bothCountingUnitMatches :
      OCR.sourceCountingUnit src
        (OCR.MatchedOriginalCell.selectedRow oneSuspension)
      ≡ OCR.uniqueStudents
    repeatedCountingUnitMatches :
      OCR.sourceCountingUnit src
        (OCR.MatchedOriginalCell.selectedRow repeatedSuspension)
      ≡ OCR.uniqueStudents
    oneCount : Nat
    repeatedCount : Nat
    oneObserved :
      OCR.sourceCell src
        (OCR.MatchedOriginalCell.selectedRow oneSuspension)
      ≡ OCR.observed oneCount
    repeatedObserved :
      OCR.sourceCell src
        (OCR.MatchedOriginalCell.selectedRow repeatedSuspension)
      ≡ OCR.observed repeatedCount
    originalDisjointnessAudited : Set
    exactOneAndMultipleDisjoint : originalDisjointnessAudited

-- originalDisjointnessAudited is an externally owned audited evidence type;
-- setting it arbitrarily to unit would not constitute original-source proof.

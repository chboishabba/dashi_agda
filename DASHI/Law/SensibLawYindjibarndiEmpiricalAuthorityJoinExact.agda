module DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawSharedWorldConsumerJoinExact as Join

------------------------------------------------------------------------
-- S21.A YINDJIBARNDI EMPIRICAL AUTHORITY-TREATMENT JOIN
--
-- Source-grounded distinction:
--
-- * dedicated WAD37/2022 submissions expressly treat Commonwealth v
--   Yunupingu [2025] HCA 6;
-- * the applicant's closing reply records an FMG reliance on Brennan J in
--   Mabo (No 2) and answers it by distinguishing voluntary assignment from
--   compulsory Crown acquisition;
-- * therefore specific Yunupingu and specific Mabo treatment coordinates may
--   enter the Yindjibarndi dependency slice after review;
-- * no generic "native title => Mabo" dependency is admitted.
------------------------------------------------------------------------

yunupinguAcquisitionCoordinate : Join.SharedCoordinate
yunupinguAcquisitionCoordinate =
  Join.sharedCoordinate
    "coordinate:authority:yunupingu-2025-hca6:s51xxxi-native-title-acquisition"
    "semantic:yunupingu:s51xxxi-native-title-acquisition"
    true refl false refl false refl

maboAcquisitionDistinctionCoordinate : Join.SharedCoordinate
maboAcquisitionDistinctionCoordinate =
  Join.sharedCoordinate
    "coordinate:authority:mabo-no2:brennan-60-acquisition-distinction"
    "semantic:mabo-no2:acquisition-distinction"
    true refl false refl false refl

genericMaboNativeTitleCoordinate : Join.SharedCoordinate
genericMaboNativeTitleCoordinate =
  Join.sharedCoordinate
    "coordinate:authority:mabo-no2:generic-native-title"
    "semantic:mabo-no2:generic-native-title"
    true refl false refl false refl

data YindjibarndiEmpiricalNeed : String → Set where
  needsYunupinguAcquisition :
    YindjibarndiEmpiricalNeed
      "coordinate:authority:yunupingu-2025-hca6:s51xxxi-native-title-acquisition"
  needsMaboAcquisitionDistinction :
    YindjibarndiEmpiricalNeed
      "coordinate:authority:mabo-no2:brennan-60-acquisition-distinction"

yindjibarndiEmpiricalSlice : Join.ConsumerDependencySlice
yindjibarndiEmpiricalSlice =
  Join.consumerDependencySlice
    "consumer:yindjibarndi-compensation"
    YindjibarndiEmpiricalNeed
    "slice:yindjibarndi:empirical-authority-treatment"
    true refl false refl

yunupinguReviewedJoin :
  Join.ReviewedJoinWitness
    yunupinguAcquisitionCoordinate
    yindjibarndiEmpiricalSlice
yunupinguReviewedJoin =
  Join.reviewedJoinWitness
    needsYunupinguAcquisition
    "review:yindjibarndi:yunupingu-treatment"
    true refl false refl false refl

maboSpecificTreatmentReviewedJoin :
  Join.ReviewedJoinWitness
    maboAcquisitionDistinctionCoordinate
    yindjibarndiEmpiricalSlice
maboSpecificTreatmentReviewedJoin =
  Join.reviewedJoinWitness
    needsMaboAcquisitionDistinction
    "review:yindjibarndi:mabo-specific-treatment"
    true refl false refl false refl

------------------------------------------------------------------------
-- The source relation is adversarial rather than a single merged proposition.
------------------------------------------------------------------------

data ArgumentRole : Set where
  support : ArgumentRole
  defeater : ArgumentRole
  counterDefeater : ArgumentRole
  authorityScope : ArgumentRole

record SourceGroundedTreatment : Set where
  constructor sourceGroundedTreatment
  field
    sourceRef : String
    authorityRef : String
    propositionRef : String
    role : ArgumentRole
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open SourceGroundedTreatment public

applicantYunupinguSupport : SourceGroundedTreatment
applicantYunupinguSupport =
  sourceGroundedTreatment
    "fedcourt:WAD37/2022:applicant-yunupingu-reply:2025-06-25"
    "case:au:hca:2025:6"
    "proposition:yindjibarndi:yunupingu-supports-acquisition-through-diminution-or-impairment"
    support
    true refl false refl

stateYunupinguScope : SourceGroundedTreatment
stateYunupinguScope =
  sourceGroundedTreatment
    "fedcourt:WAD37/2022:state-yunupingu-reply:2025-05-23"
    "case:au:hca:2025:6"
    "proposition:yindjibarndi:yunupingu-did-not-decide-nonextinguishment-act-acquisition"
    authorityScope
    true refl false refl

fmgYunupinguDefeater : SourceGroundedTreatment
fmgYunupinguDefeater =
  sourceGroundedTreatment
    "fedcourt:WAD37/2022:fmg-yunupingu-submissions:2025-05-16"
    "case:au:hca:2025:6"
    "proposition:yindjibarndi:yunupingu-does-not-establish-every-mining-lease-acquisition"
    defeater
    true refl false refl

fmgMaboDefeater : SourceGroundedTreatment
fmgMaboDefeater =
  sourceGroundedTreatment
    "fedcourt:WAD37/2022:applicant-closing-reply:2025-02-03"
    "case:au:hca:1992:23"
    "proposition:yindjibarndi:fmg-invokes-mabo-brennan-60-against-acquisition"
    defeater
    true refl false refl

applicantMaboDistinction : SourceGroundedTreatment
applicantMaboDistinction =
  sourceGroundedTreatment
    "fedcourt:WAD37/2022:applicant-closing-reply:2025-02-03"
    "case:au:hca:1992:23"
    "proposition:yindjibarndi:applicant-distinguishes-voluntary-assignment-from-crown-compulsory-acquisition"
    counterDefeater
    true refl false refl

------------------------------------------------------------------------
-- Anti-collapse theorem: the specific reviewed treatment does not create a
-- generic Mabo/native-title dependency.
------------------------------------------------------------------------

data GenericMaboDependencyPaid : Set where

genericMaboAdjacencyDoesNotPayYindjibarndi :
  GenericMaboDependencyPaid → ⊥
genericMaboAdjacencyDoesNotPayYindjibarndi ()

record YindjibarndiEmpiricalJoinBoundary : Set where
  constructor yindjibarndiEmpiricalJoinBoundary
  field
    yunupinguTreatmentIsRequired : Bool
    yunupinguTreatmentIsRequiredIsTrue :
      yunupinguTreatmentIsRequired ≡ true

    specificMaboTreatmentIsRequired : Bool
    specificMaboTreatmentIsRequiredIsTrue :
      specificMaboTreatmentIsRequired ≡ true

    genericMaboAdjacencyIsRequired : Bool
    genericMaboAdjacencyIsRequiredIsFalse :
      genericMaboAdjacencyIsRequired ≡ false

    opposingAuthorityTreatmentsCoexist : Bool
    opposingAuthorityTreatmentsCoexistIsTrue :
      opposingAuthorityTreatmentsCoexist ≡ true

    reviewedTreatmentCreatesClaimTruth : Bool
    reviewedTreatmentCreatesClaimTruthIsFalse :
      reviewedTreatmentCreatesClaimTruth ≡ false

open YindjibarndiEmpiricalJoinBoundary public

canonicalYindjibarndiEmpiricalJoinBoundary :
  YindjibarndiEmpiricalJoinBoundary
canonicalYindjibarndiEmpiricalJoinBoundary =
  yindjibarndiEmpiricalJoinBoundary
    true refl
    true refl
    false refl
    true refl
    false refl

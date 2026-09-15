module DASHI.Culture.MissingDeceasedTwentyScientistRound46ExternalCohortCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as R44
import DASHI.Culture.MissingDeceasedTwentyScientistRound45ChineseReportedCohortExact as R45

------------------------------------------------------------------------
-- ROUND 46: EXTERNAL COHORT COVERAGE OF THE RETAINED TWENTY
------------------------------------------------------------------------

record ExternalCohortCoverage : Set where
  constructor external-cohort-coverage
  field
    person : String
    inUSOfficialReportingCohort : Bool
    inChineseReportedCohort : Bool

open ExternalCohortCoverage public

hicks = external-cohort-coverage "Michael David Hicks" true false
reza = external-cohort-coverage "Monica Jacinto / Monica Reza" true false
mccasland = external-cohort-coverage "William Neil McCasland" true false
maiwald = external-cohort-coverage "Frank W. Maiwald" true false
grillmair = external-cohort-coverage "Carl J. Grillmair" true false
nuno = external-cohort-coverage "Nuno F. G. Loureiro" true false
chavez = external-cohort-coverage "Anthony Chavez" true false
thomas = external-cohort-coverage "Jason R. Thomas" true false
chen = external-cohort-coverage "Chen Shuming" false true
feng = external-cohort-coverage "Feng Yanghe" false true
zhou = external-cohort-coverage "Zhou Guangyuan" false true
liu = external-cohort-coverage "Liu Donghao" false true
zhangXiaoxin = external-cohort-coverage "Zhang Xiaoxin" false true
zhangDaibing = external-cohort-coverage "Zhang Daibing" false true
liMinyong = external-cohort-coverage "Li Minyong" false true
fang = external-cohort-coverage "Fang Daining" false true
yan = external-cohort-coverage "Yan Hong" false true
amy = external-cohort-coverage "Amy Eskridge" false false
ning = external-cohort-coverage "Ning Li" false false
leblanc = external-cohort-coverage "Joshua Kyle LeBlanc" false false

round46RetainedCount : Nat
round46RetainedCount = 20

round46USOfficialReportingOverlap : Nat
round46USOfficialReportingOverlap = 8

round46ChineseReportedOverlap : Nat
round46ChineseReportedOverlap = 9

round46ExternalComparisonCoverage : Nat
round46ExternalComparisonCoverage = 17

round46OutsideBothComparisonSets : Nat
round46OutsideBothComparisonSets = 3

amyOutsideBoth : Bool
amyOutsideBoth = true

ningOutsideBoth : Bool
ningOutsideBoth = true

leblancOutsideBoth : Bool
leblancOutsideBoth = true

externalCoverageIsSelectionContextNotCausation : Bool
externalCoverageIsSelectionContextNotCausation = true

seventeenOfTwentyDoesNotPayCommonProgramme : Bool
seventeenOfTwentyDoesNotPayCommonProgramme = true

seventeenOfTwentyDoesNotPayTargeting : Bool
seventeenOfTwentyDoesNotPayTargeting = true

usOfficialAndChineseMediaCohortsMustRemainSourceDistinct : Bool
usOfficialAndChineseMediaCohortsMustRemainSourceDistinct = true

round46H2PaidCount : Nat
round46H2PaidCount = 0

round46H3PaidCount : Nat
round46H3PaidCount = 0

round46NarrativeBoundary : String
round46NarrativeBoundary = "Seventeen of the retained twenty are already members of one of two externally reported comparison sets: eight overlap the U.S. House/public-reporting ten and all nine members of the April 2026 Chinese reported cluster are retained. Amy Eskridge, Ning Li and Joshua Kyle LeBlanc are outside both comparison sets. This is strong evidence that the retained cohort substantially overlaps independently assembled public-reporting sets, but it is a selection/context fact only. The U.S. official-inquiry cohort and Chinese media-comparison cohort have different source status and cannot be merged into a single official, causal or operational object."

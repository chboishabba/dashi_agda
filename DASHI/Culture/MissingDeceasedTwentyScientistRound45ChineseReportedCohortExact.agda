module DASHI.Culture.MissingDeceasedTwentyScientistRound45ChineseReportedCohortExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as R44

------------------------------------------------------------------------
-- ROUND 45: CHINESE REPORTED COHORT / CONGRESSIONAL CHINA-SECURITY SEPARATION
--
-- April 2026 reporting compared a nine-person Chinese scientist cluster with
-- the U.S. missing/deceased-scientist inquiry.  All nine are already present
-- in the retained analytical twenty.  Separately, House Oversight opened and
-- expanded a China science-and-technology-agreement security inquiry.  These
-- are adjacent public contexts, not one evidentiary object.
------------------------------------------------------------------------

record ChineseReportedPerson : Set where
  constructor chinese-reported-person
  field
    person : String
    representedInRetainedTwenty : Bool
    reportedInApril2026ChineseCluster : Bool
    exactTechnicalObjectAlreadyTracked : Bool

open ChineseReportedPerson public

chen = chinese-reported-person "Chen Shuming" true true true
feng = chinese-reported-person "Feng Yanghe" true true true
zhou = chinese-reported-person "Zhou Guangyuan" true true true
liu = chinese-reported-person "Liu Donghao" true true true
zhangXiaoxin = chinese-reported-person "Zhang Xiaoxin" true true true
zhangDaibing = chinese-reported-person "Zhang Daibing" true true true
liMinyong = chinese-reported-person "Li Minyong" true true true
fang = chinese-reported-person "Fang Daining" true true true
yan = chinese-reported-person "Yan Hong" true true true

chineseReportedNine : List ChineseReportedPerson
chineseReportedNine = chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

chineseReportedCohortCount : Nat
chineseReportedCohortCount = 9

chineseReportedRetainedOverlapCount : Nat
chineseReportedRetainedOverlapCount = 9

allChineseReportedRowsAlreadyInRetainedTwenty : Bool
allChineseReportedRowsAlreadyInRetainedTwenty = true

mediaComparisonToUSInquiryPaid : Bool
mediaComparisonToUSInquiryPaid = true

formalCongressionalChineseDeathInquiryLocated : Bool
formalCongressionalChineseDeathInquiryLocated = false

houseChinaSTASecurityInquiryPaid : Bool
houseChinaSTASecurityInquiryPaid = true

houseChinaSTAInquiryIsDistinctFromChineseDeathCluster : Bool
houseChinaSTAInquiryIsDistinctFromChineseDeathCluster = true

burlisonPublicForeignAdversaryChinaConcernPaid : Bool
burlisonPublicForeignAdversaryChinaConcernPaid = true

burlisonConcernDoesNotPayChineseDeathInquiry : Bool
burlisonConcernDoesNotPayChineseDeathInquiry = true

mediaClusterDoesNotPayCommonCause : Bool
mediaClusterDoesNotPayCommonCause = true

mediaClusterDoesNotPayTargeting : Bool
mediaClusterDoesNotPayTargeting = true

chinaSTASecurityConcernDoesNotTransferToIndividualDeaths : Bool
chinaSTASecurityConcernDoesNotTransferToIndividualDeaths = true

sharedSensitiveTechnologyThemeDoesNotPayCrossNationalMechanism : Bool
sharedSensitiveTechnologyThemeDoesNotPayCrossNationalMechanism = true

round45H2PaidCount : Nat
round45H2PaidCount = 0

round45H3PaidCount : Nat
round45H3PaidCount = 0

round45NarrativeBoundary : String
round45NarrativeBoundary = "April 2026 reporting identified a nine-person Chinese scientist cluster and explicitly compared it with the contemporaneous U.S. missing/deceased-scientist inquiry. All nine reported Chinese cases are already represented in the retained analytical twenty. House Oversight also opened a separate April 24 China science-and-technology-agreement security inquiry and expanded it on June 17. No primary House record has been located that formally incorporates the nine Chinese deaths into the April 20 missing-scientists inquiry. Media comparison, congressional China research-security concern and Representative Burlison's public foreign-adversary concern must therefore remain separate source roles and cannot pay a common programme, targeting or cross-national causal mechanism."

round45Pareto : String
round45Pareto = "Use the exact object surfaces already acquired for the nine Chinese rows to search for literal pairwise crossings inside the Chinese cluster, while separately monitoring the House missing-scientists inquiry and the House China STA inquiry for any future official linkage. Do not infer such linkage from temporal adjacency or shared national-security framing."

module DASHI.Culture.MissingDeceasedCommonProgrammePromotionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common
import DASHI.Culture.MissingDeceasedCommonProgrammePromotionStateExact as Promotion

------------------------------------------------------------------------
-- PROMOTION-DEBT PARETO
--
-- A candidate pair is ranked by the shortest literal documentary path to H2,
-- not by how evocative its scientific or geographic similarity appears.
-- H3 is a separate downstream gate requiring operational evidence.
------------------------------------------------------------------------

data PromotionSearchClass : Set where
  explicitHistoricalReference
  programmeIdentifierSecondPersonSearch
  institutionalWorkPackageSearch
  intermediaryChainSearch
  preEventOperationalSearch : PromotionSearchClass

record PromotionSearchCandidate : Set where
  constructor promotion-search-candidate
  field
    participantA : String
    participantB : String
    searchClass : PromotionSearchClass
    strongestPaidEdge : String
    targetObjectOrIdentifier : String
    missingH2Receipt : String
    missingH3Receipt : String
    inventedInterfaceDebt : Nat
    documentaryDistanceToH2 : Nat
    h2Paid : Bool
    h3Paid : Bool

open PromotionSearchCandidate public

amyNingCandidate : PromotionSearchCandidate
amyNingCandidate = promotion-search-candidate
  "Amy Eskridge"
  "Ning Li"
  explicitHistoricalReference
  "Amy's 2018 HAL5 deck explicitly names Ning Li/Torr AC Gravity as historical research"
  "AC Gravity / DAAH01-01-9-R001 / Amy Institute-NASA reviewed release object"
  "one pre-event source naming Amy or her Institute on Ning/AC Gravity/Army apparatus, contract, work package, handoff or successor object"
  "cross-case operational/security/action evidence tied to that paid common object"
  1 1 false false

rezaMcCaslandCandidate : PromotionSearchCandidate
rezaMcCaslandCandidate = promotion-search-candidate
  "Monica Jacinto / Monica Reza"
  "William Neil McCasland"
  intermediaryChainSearch
  "Reza-Hardwick Mondaloy lineage plus Hardwick AFRL role plus McCasland AFRL command chronology"
  "pre-2013 Mondaloy AFRL contract / work package / programme review"
  "one pre-event document naming McCasland and the same Mondaloy/Reza programme object or placing him in its tasking/review chain"
  "operational action against both people tied to the same paid programme object"
  1 1 false false

hicksMaiwaldCandidate : PromotionSearchCandidate
hicksMaiwaldCandidate = promotion-search-candidate
  "Michael David Hicks"
  "Frank W. Maiwald"
  institutionalWorkPackageSearch
  "both are source-backed JPL researchers with distinct small-body and spectroscopy objects"
  "JPL instrument / SURP / mission / procurement / work-package identifier"
  "one JPL source naming both on the same project, instrument, facility, procurement or work package"
  "pre-event cross-case operational/security/action receipt on that same JPL object"
  2 2 false false

nudtChenFengCandidate : PromotionSearchCandidate
nudtChenFengCandidate = promotion-search-candidate
  "Chen Shuming"
  "Feng Yanghe"
  institutionalWorkPackageSearch
  "both are source-backed NUDT scientists in strategic computing/decision research"
  "NUDT military task / project / programme / laboratory identifier"
  "one primary NUDT/PLA source naming both on the same task, programme, codebase, facility or work package"
  "pre-event operational/security/action receipt tied to that same task"
  2 2 false false

nudtFengZhangCandidate : PromotionSearchCandidate
nudtFengZhangCandidate = promotion-search-candidate
  "Feng Yanghe"
  "Zhang Daibing"
  institutionalWorkPackageSearch
  "both are source-backed NUDT scientists with AI/decision and unmanned-systems carriers"
  "NUDT autonomous-system / decision-support military task identifier"
  "one primary source naming both on a shared task, codebase, vehicle programme, laboratory or work package"
  "pre-event operational/security/action receipt tied to that same task"
  2 2 false false

ningSecondPersonIdentifierSearch : PromotionSearchCandidate
ningSecondPersonIdentifierSearch = promotion-search-candidate
  "Ning Li"
  "second retained scientist unresolved"
  programmeIdentifierSecondPersonSearch
  "DAAH01-01-9-R001 is a strong single-person programme identifier"
  "DAAH01-01-9-R001 SOW / closeout / personnel / subcontract / facility list"
  "a second retained scientist named on the same Army/AC Gravity programme object"
  "pre-event action/security receipt spanning both participants on that object"
  0 1 false false

currentPromotionSearchFront : List PromotionSearchCandidate
currentPromotionSearchFront =
  amyNingCandidate ∷
  rezaMcCaslandCandidate ∷
  ningSecondPersonIdentifierSearch ∷
  hicksMaiwaldCandidate ∷
  nudtChenFengCandidate ∷
  nudtFengZhangCandidate ∷ []

literalReferenceWithoutSameProgrammeDoesNotPayH2 : Bool
literalReferenceWithoutSameProgrammeDoesNotPayH2 = false

institutionWithoutWorkPackageDoesNotPayH2 : Bool
institutionWithoutWorkPackageDoesNotPayH2 = false

sameProgrammeWithoutOperationalActionDoesNotPayH3 : Bool
sameProgrammeWithoutOperationalActionDoesNotPayH3 = false

singlePersonProgrammeIdDoesNotPayCrossPersonH2 : Bool
singlePersonProgrammeIdDoesNotPayCrossPersonH2 = false

currentH2PromotionCount : Nat
currentH2PromotionCount = 0

currentH3PromotionCount : Nat
currentH3PromotionCount = 0

h2CurrentDeficit : Nat
h2CurrentDeficit = Promotion.currentH2CrossPersonDeficit

h3CurrentDeficit : Nat
h3CurrentDeficit = Promotion.currentH3OperationalDeficit

nextParetoAcquisition : String
nextParetoAcquisition =
  "1 DAAH01-01-9-R001 SOW/closeout personnel-facility-subcontract table; 2 Amy Institute/NASA release object for AC Gravity/Army identifier reuse; 3 pre-2013 Mondaloy AFRL work-package/review records; 4 exact JPL shared work package; 5 exact NUDT shared military task"

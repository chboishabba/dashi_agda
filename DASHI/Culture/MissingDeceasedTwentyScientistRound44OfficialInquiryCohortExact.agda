module DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound43NarrativeEvidenceStrataExact as R43

------------------------------------------------------------------------
-- ROUND 44: OFFICIAL-INQUIRY COHORT AS AN ORTHOGONAL CONTEXT SURFACE
--
-- Congressional attention is institutionally important, but is not a payment
-- for shared programme identity or targeting.  We therefore add a context
-- coordinate G and keep the official/public-reporting cohort distinct from
-- the original retained analytical twenty.
------------------------------------------------------------------------

record OfficialInquiryPerson : Set where
  constructor official-inquiry-person
  field
    person : String
    representedInRetainedTwenty : Bool
    directlyNamedInHouseLetter : Bool
    resolvedViaReportingCitedByHouse : Bool
    primaryIdentityEventAnchorPaid : Bool
    technicalRoleNeedsFurtherPrimaryWeld : Bool

open OfficialInquiryPerson public

hicks = official-inquiry-person "Michael David Hicks" true true false true false
reza = official-inquiry-person "Monica Jacinto / Monica Reza" true true false true false
mccasland = official-inquiry-person "William Neil McCasland" true true false true false
maiwald = official-inquiry-person "Frank W. Maiwald" true false true true false
grillmair = official-inquiry-person "Carl J. Grillmair" true false true true false
nuno = official-inquiry-person "Nuno F. G. Loureiro" true false true true false
chavez = official-inquiry-person "Anthony Chavez" true false true true false
thomas = official-inquiry-person "Jason R. Thomas" true false true true false
casias = official-inquiry-person "Melissa Casias" false false true true true
garcia = official-inquiry-person "Steven Abel Garcia" false false true true true

officialReportingTen : List OfficialInquiryPerson
officialReportingTen =
  hicks ∷ reza ∷ mccasland ∷ maiwald ∷ grillmair ∷ nuno ∷ chavez ∷ thomas ∷ casias ∷ garcia ∷ []

officialReportingCohortCount : Nat
officialReportingCohortCount = 10

retainedTwentyOverlapCount : Nat
retainedTwentyOverlapCount = 8

outsideRetainedTwentyCount : Nat
outsideRetainedTwentyCount = 2

melissaCasiasOutsideRetainedTwenty : Bool
melissaCasiasOutsideRetainedTwenty = true

stevenGarciaOutsideRetainedTwenty : Bool
stevenGarciaOutsideRetainedTwenty = true

officialPatternInquiryPaid : Bool
officialPatternInquiryPaid = true

houseInquiryDirectlyNamesOnlySubset : Bool
houseInquiryDirectlyNamesOnlySubset = true

reportingCitedByHouseResolvesRemainingCategories : Bool
reportingCitedByHouseResolvesRemainingCategories = true

officialInquiryDoesNotPaySharedProgramme : Bool
officialInquiryDoesNotPaySharedProgramme = true

officialInquiryDoesNotPayTargeting : Bool
officialInquiryDoesNotPayTargeting = true

comparisonCohortMustNotSilentlyRedefineRetainedTwenty : Bool
comparisonCohortMustNotSilentlyRedefineRetainedTwenty = true

casiasCurrentStatusMustUseUpdatedPrimaryEventRecord : Bool
casiasCurrentStatusMustUseUpdatedPrimaryEventRecord = true

garciaEmploymentAndClearanceClaimsNeedPrimaryWeld : Bool
garciaEmploymentAndClearanceClaimsNeedPrimaryWeld = true

round44G : Bool
round44G = true

round44H2PaidCount : Nat
round44H2PaidCount = 0

round44H3PaidCount : Nat
round44H3PaidCount = 0

round44NarrativeBoundary : String
round44NarrativeBoundary = "The U.S. House Oversight Committee formally opened an inquiry into a ten-person public-reporting pattern involving deaths and disappearances among personnel described as connected to sensitive U.S. scientific information. Eight of those ten are already represented in the retained analytical twenty; Melissa Casias and Steven Abel Garcia are not. This official-inquiry context is orthogonal to H2/H3: institutional concern does not establish a shared programme, targeting, common cause or wrongdoing."

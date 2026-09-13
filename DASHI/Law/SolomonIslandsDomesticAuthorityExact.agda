module DASHI.Law.SolomonIslandsDomesticAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.LegalAuthorityCitationExact as Legal

------------------------------------------------------------------------
-- SOLOMON ISLANDS DOMESTIC AUTHORITY FIXTURES
--
-- These authorities identify the domestic constitutional/parliamentary
-- coordinates surrounding the 2026 motion of no confidence.  They do not,
-- merely by citation, establish that any Australian conduct was unlawful.
------------------------------------------------------------------------

constitutionSection34 : Legal.LegalCitation
constitutionSection34 = Legal.legal-citation
  Legal.constitution
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Solomon Islands constitutional order"
  "Constitution of Solomon Islands"
  1978
  (Legal.statutoryCitation "Constitution of Solomon Islands, s 34")
  "section 34(1)-(2)"
  "a resolution of no confidence passed by an absolute majority requires removal of the Prime Minister; notice of the motion must be given to the Speaker at least seven clear days before introduction"
  false refl

constitutionSection94 : Legal.LegalCitation
constitutionSection94 = Legal.legal-citation
  Legal.constitution
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Solomon Islands constitutional order"
  "Constitution of Solomon Islands"
  1978
  (Legal.statutoryCitation "Constitution of Solomon Islands, s 94")
  "section 94(1)-(4)"
  "persons governed by the Leadership Code must avoid conflicts or compromised official duties, demeaning office, calling integrity into question, or diminishing confidence in government integrity; breach may constitute misconduct in office"
  false refl

parliamentWithdrawalRecord : Legal.LegalCitation
parliamentWithdrawalRecord = Legal.legal-citation
  Legal.parliamentaryRecord
  Legal.primaryTextEvidence
  "Solomon Islands"
  "National Parliament of Solomon Islands, Office of the Clerk"
  "Motion of No Confidence in the Prime Minister Withdrawn"
  2026
  (Legal.parliamentaryCitation "National Parliament press release, 7 September 2026")
  "notice 29 August 2026; withdrawal letter 6 September 2026; Standing Order 31(2)"
  "the Clerk confirmed that Manasseh Maelanga withdrew the notice of motion by written instruction before it was moved, pursuant to Standing Order 31(2)"
  false refl

------------------------------------------------------------------------
-- Authority-role boundaries.
------------------------------------------------------------------------

data Section34CreatesForeignInterferenceOffence : Set where
data Section94DirectlyBindsAustralianDiplomat : Set where
data WithdrawalRecordProvesForeignCausation : Set where

data ConstitutionalMechanismCoordinate : Set where
  noConfidenceMechanism : ConstitutionalMechanismCoordinate
  leadershipIntegrityDuties : ConstitutionalMechanismCoordinate
  withdrawalProcedure : ConstitutionalMechanismCoordinate

section34DoesNotCreateForeignInterferenceOffence :
  Section34CreatesForeignInterferenceOffence → ⊥
section34DoesNotCreateForeignInterferenceOffence ()

section94DoesNotDirectlyBindAustralianDiplomat :
  Section94DirectlyBindsAustralianDiplomat → ⊥
section94DoesNotDirectlyBindAustralianDiplomat ()

withdrawalRecordDoesNotProveForeignCausation :
  WithdrawalRecordProvesForeignCausation → ⊥
withdrawalRecordDoesNotProveForeignCausation ()

------------------------------------------------------------------------
-- Consumer-use receipts: proposition and jurisdictional fit must be reviewed.
------------------------------------------------------------------------

section34NoConfidenceUse : Legal.LegalAuthorityUseReceipt constitutionSection34
section34NoConfidenceUse = Legal.legal-authority-use-receipt
  "foreign-interference characterisation / identify protected domestic parliamentary process"
  "the motion of no confidence is a constitutionally regulated Solomon Islands parliamentary mechanism"
  true refl true refl true refl false refl

section94LeadershipIntegrityUse : Legal.LegalAuthorityUseReceipt constitutionSection94
section94LeadershipIntegrityUse = Legal.legal-authority-use-receipt
  "foreign-interference characterisation / recipient-side domestic integrity context"
  "Solomon Islands leaders are subject to constitutional integrity and conflict-of-interest duties; application to any specific leader requires separate facts and adjudication"
  true refl true refl true refl false refl

withdrawalChronologyUse : Legal.LegalAuthorityUseReceipt parliamentWithdrawalRecord
withdrawalChronologyUse = Legal.legal-authority-use-receipt
  "foreign-interference characterisation / official chronology"
  "the motion notice was withdrawn on 6 September 2026 before being moved, under Standing Order 31(2)"
  true refl true refl true refl false refl

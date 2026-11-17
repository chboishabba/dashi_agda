module DASHI.Culture.AmyEskridgeVideoEleventhMediaRosterWeldExact where

-- Source-entitled secondary media roster for video 00:21.
--
-- Original journalistic list: Morgan Phillips, "11th scientist death emerges
-- in string of missing, dead officials with access to US secrets",
-- Fox News Digital, 2026-04-17, 11:37am EDT:
-- https://www.foxnews.com/politics/11th-scientist-death-emerges-string-missing-dead-officials-access-us-secrets.amp
-- Other same-outlet report: Michael Dorgan, "White House reviewing cases
-- of missing, dead scientists for possible links as 11th person identified",
-- Fox News Digital, 2026-04-17, 3:02pm EDT:
-- https://www.foxnews.com/politics/white-house-reviewing-cases-missing-dead-scientists-possible-links-11th-person-identified.amp
-- Source-owner atoms already exist in AmyEskridgeOSINTSnowballExact.
--
-- The report NAMES ten cases + Amy, but does not establish that all are
-- research scientists, have classified access, share a programme, or were
-- victims of targeting. In particular this 2022 Amy case is historically
-- outside the House's 2023-onward media sequence, though a media list may
-- append her. Keep the two different sourcing criteria visible.
-- The list below is canonically reordered to put the ten previously
-- reconstructed House/reporting cases first, Amy last; this is a DASHI
-- normalization, NOT the Fox article's literal list order.

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as A
import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT
import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as House
import DASHI.Culture.MissingDeceasedRosterRoleAndCommitteeWeldAuditExact as Role
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Amy

data PersonKey : Set where
  hicksKey : PersonKey
  rezaKey : PersonKey
  mccaslandKey : PersonKey
  maiwaldKey : PersonKey
  grillmairKey : PersonKey
  nunoKey : PersonKey
  chavezKey : PersonKey
  thomasKey : PersonKey
  casiasKey : PersonKey
  garciaKey : PersonKey
  amyKey : PersonKey

data PriorEvidence : Set where
  houseReportingCase : House.OfficialInquiryPerson → PriorEvidence
  amyMemorial : Amy.DemiseSnowballAtom → PriorEvidence

record SecondaryReportedRosterMember : Set where
  constructor secondary-reported-roster-member
  field
    personKey : PersonKey
    nameInJournalism : String
    journalistCarrier : A.AttributedSource
    priorIndependentOwner : PriorEvidence
    roleOrEventBoundary : String

open SecondaryReportedRosterMember public

hicks : SecondaryReportedRosterMember
hicks = secondary-reported-roster-member hicksKey "Michael David Hicks"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.hicks)
  "Memorial establishes 2023 death; the report does not establish targeting"

reza : SecondaryReportedRosterMember
reza = secondary-reported-roster-member rezaKey "Monica Jacinto Reza"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.reza)
  "Original missing-person identity does not prove programme or motive"

mccasland : SecondaryReportedRosterMember
mccasland = secondary-reported-roster-member mccaslandKey "William Neil McCasland"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.mccasland)
  "Missing-person record and past institutional role do not prove UAP tasking"

maiwald : SecondaryReportedRosterMember
maiwald = secondary-reported-roster-member maiwaldKey "Frank Maiwald"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.maiwald)
  "Scientific PI/project role is independent of any common death cause"

grillmair : SecondaryReportedRosterMember
grillmair = secondary-reported-roster-member grillmairKey "Carl Grillmair"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.grillmair)
  "Prosecuted local crime must be treated as a competing mechanism, not erased"

nuno : SecondaryReportedRosterMember
nuno = secondary-reported-roster-member nunoKey "Nuno Loureiro"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.nuno)
  "Plasma scientist and event records do not prove coordinated targeting"

chavez : SecondaryReportedRosterMember
chavez = secondary-reported-roster-member chavezKey "Anthony Chavez"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.chavez)
  "Identity to Mark Anthony Chavez's LANL technical work remains OPEN"

thomas : SecondaryReportedRosterMember
thomas = secondary-reported-roster-member thomasKey "Jason Thomas"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.thomas)
  "Scientific-work attribution does not establish cause or manner"

casias : SecondaryReportedRosterMember
casias = secondary-reported-roster-member casiasKey "Melissa Casias"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.casias)
  "Administrative role; cannot be counted as a research scientist by article label"

garcia : SecondaryReportedRosterMember
garcia = secondary-reported-roster-member garciaKey "Steven Garcia"
  OSINT.foxDeathCharacterizationSource (houseReportingCase House.garcia)
  "Property custody role; cannot be counted as a research scientist by article label"

amy : SecondaryReportedRosterMember
amy = secondary-reported-roster-member amyKey "Amy Eskridge"
  OSINT.foxDeathCharacterizationSource (amyMemorial Amy.familyObituaryDateAtom)
  "Family obituary dates death 2022-06-11; Fox's list membership is a later secondary classification, not forensic or causal proof"

-- Exact media roster contents, normalized to existing ten-person order.
foxPublishedNamesNormalized : List SecondaryReportedRosterMember
foxPublishedNamesNormalized =
  hicks ∷ reza ∷ mccasland ∷ maiwald ∷ grillmair ∷
  nuno ∷ chavez ∷ thomas ∷ casias ∷ garcia ∷ amy ∷ []

houseTenCanonicalKeys : List PersonKey
houseTenCanonicalKeys =
  hicksKey ∷ rezaKey ∷ mccaslandKey ∷ maiwaldKey ∷ grillmairKey ∷
  nunoKey ∷ chavezKey ∷ thomasKey ∷ casiasKey ∷ garciaKey ∷ []

foxElevenCanonicalKeys : List PersonKey
foxElevenCanonicalKeys =
  hicksKey ∷ rezaKey ∷ mccaslandKey ∷ maiwaldKey ∷ grillmairKey ∷
  nunoKey ∷ chavezKey ∷ thomasKey ∷ casiasKey ∷ garciaKey ∷
  amyKey ∷ []

-- Repo-native list append, so this identity is proven against the
-- pre-existing ten-case normalized enumeration rather than a hand-copied
-- 11-person right-hand side.
append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

foxElevenEqualsHouseTenPlusAmyKeys :
  foxElevenCanonicalKeys ≡ append houseTenCanonicalKeys (amyKey ∷ [])
foxElevenEqualsHouseTenPlusAmyKeys = refl

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

foxReportedElevenCount : length foxPublishedNamesNormalized ≡ 11
foxReportedElevenCount = refl

houseContextTenCount : length houseTenCanonicalKeys ≡ 10
houseContextTenCount = refl

-- The two Fox pieces are not separate event verification. Their newsroom
-- enumeration is narrower than the video's causal/suppression implications.
data FoxListProvesCommonProgramme : Set where
data FoxListProvesAllScientistRoles : Set where
data FoxListProvesMurderOrSuppressor : Set where

-- The old role audit has explicit non-science roles for Casias and Garcia.
roleBoundaryRetained : Role.RoleType
roleBoundaryRetained = Role.roleType Role.melissaCasiasRole

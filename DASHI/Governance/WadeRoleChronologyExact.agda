module DASHI.Governance.WadeRoleChronologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ALAN WADE ROLE CHRONOLOGY
--
-- Separates official/independent role receipts from secondary TIA assertions.
-- A CIA/IC CIO role is not itself a TIA role; Chiliad affiliation is not TIA
-- participation; repeated secondary claims do not become independent receipts.
------------------------------------------------------------------------

nationalAcademiesWadeBio : Source.AttributedSource
nationalAcademiesWadeBio = Source.mkNoDOISource
  "National Academies / Federal Facilities Council"
  "Workshop speaker biography: Alan Wade"
  "National Academies"
  "2015"
  "https://sites.nationalacademies.org/cs/groups/depssite/documents/webpage/deps_169277.pdf"
  Source.institutionalSource
  "biographical receipt: 35-year CIA career; Director of Communications, Director of Security, CIA CIO; dual-hatted as CIO for the U.S. Intelligence Community; retirement in 2005"
  Source.publicAttribution

bloombergWadeChiliad : Source.AttributedSource
bloombergWadeChiliad = Source.mkNoDOISource
  "Bloomberg Markets"
  "Alan C Wade, Chiliad Inc: Profile and Biography"
  "Bloomberg"
  "undated profile accessed 2026"
  "https://www.bloomberg.com/profile/person/15334046"
  Source.newsSource
  "biographical receipt identifying Alan C. Wade as Chairman/Founder of Chiliad Inc.; does not establish a TIA role"
  Source.publicAttribution

webbSecondaryTIA : Source.AttributedSource
webbSecondaryTIA = Source.mkNoDOISource
  "Whitney Webb"
  "The Man Behind Trump's VP Pick: It's Worse Than You Think"
  "Unlimited Hangout"
  "2024"
  "https://unlimitedhangout.com/2024/07/reportaje-investigativo/the-man-behind-trumps-vp-pick-its-worse-than-you-think/"
  Source.newsSource
  "secondary assertion that Wade was a key Poindexter/TIA ally and coordinated intelligence-community nodes; retained as an acquisition lead, not primary proof"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Alan Wade role chronology source atlas"
  "DASHI.Governance.WadeRoleChronologyExact"
  (nationalAcademiesWadeBio ∷ bloombergWadeChiliad ∷ webbSecondaryTIA ∷ [])
  "official/institutional CIA and intelligence-community role, Chiliad affiliation, and separately attributed TIA claim"

data RoleKind : Set where
  ciaSeniorRole : RoleKind
  intelligenceCommunityCIO : RoleKind
  chiliadCorporateRole : RoleKind
  tiaParticipationCandidate : RoleKind

record RoleChronologyEntry : Set where
  constructor role-chronology-entry
  field
    role : RoleKind
    timeWindow : String
    organisationOrProgramme : String
    source : Source.AttributedSource
    primaryOrInstitutionalReceipt : Bool
    sameObjectTIARolePaid : Bool
    boundedReading : String

open RoleChronologyEntry public

ciaCIOEntry : RoleChronologyEntry
ciaCIOEntry = role-chronology-entry
  ciaSeniorRole
  "2001-2005"
  "Central Intelligence Agency"
  nationalAcademiesWadeBio
  true false
  "Wade held the CIA CIO role; this alone does not establish TIA participation."

icCIOEntry : RoleChronologyEntry
icCIOEntry = role-chronology-entry
  intelligenceCommunityCIO
  "during CIA CIO assignment"
  "United States Intelligence Community"
  nationalAcademiesWadeBio
  true false
  "National Academies biography states Wade was dual-hatted as Intelligence Community CIO."

chiliadEntry : RoleChronologyEntry
chiliadEntry = role-chronology-entry
  chiliadCorporateRole
  "public biographical period unresolved in this owner"
  "Chiliad Inc."
  bloombergWadeChiliad
  true false
  "Wade's Chiliad role is separately documented; no TIA edge is manufactured from corporate affiliation."

tiaCandidateEntry : RoleChronologyEntry
tiaCandidateEntry = role-chronology-entry
  tiaParticipationCandidate
  "2002-2003 candidate window"
  "Total/Terrorism Information Awareness"
  webbSecondaryTIA
  false false
  "secondary claim retained for exact-record search; no official/primary same-person TIA-role receipt acquired in this tranche."

chronology : List RoleChronologyEntry
chronology = ciaCIOEntry ∷ icCIOEntry ∷ chiliadEntry ∷ tiaCandidateEntry ∷ []

dualCIAAndICCIOReceiptPaid : Bool
dualCIAAndICCIOReceiptPaid = true

primaryWadeTIARoleReceiptPaid : Bool
primaryWadeTIARoleReceiptPaid = false

secondaryWadeTIAClaimRetained : Bool
secondaryWadeTIAClaimRetained = true

secondaryClaimCreatesPrimaryRole : Bool
secondaryClaimCreatesPrimaryRole = false

chiliadRoleCreatesTIARole : Bool
chiliadRoleCreatesTIARole = false

record WadeRoleBoundary : Set where
  constructor wade-role-boundary
  field
    ciaAuthorityImpliesTIAAssignment : Bool
    icCIOImpliesTIANodeManager : Bool
    chiliadFounderImpliesTIAArchitect : Bool
    repeatedSecondaryClaimsCountAsIndependentPrimaryReceipts : Bool

canonicalWadeRoleBoundary : WadeRoleBoundary
canonicalWadeRoleBoundary = wade-role-boundary false false false false

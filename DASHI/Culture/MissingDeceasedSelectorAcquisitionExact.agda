module DASHI.Culture.MissingDeceasedSelectorAcquisitionExact where

------------------------------------------------------------------------
-- PROOF-DIRECTED ACQUISITION FOR COMMON-SELECTOR HYPOTHESES
--
-- Public visibility is already source-backed but far too coarse to explain why
-- a small roster would be selected.  This module therefore searches for the
-- least stronger observer supported by evidence, without requiring the people
-- to know each other or share a programme.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as V
import DASHI.Core.ReopenableHypothesisForestExact as Forest

------------------------------------------------------------------------
-- Acquisition axes.
------------------------------------------------------------------------

data SelectorAcquisitionTarget : Set where
  crossInstitutionPersonnelDirectory
  sharedFundingOrAwardManagementSystem
  sharedPrimeOrSubcontractorRegistry
  sharedFacilityAccessOrVisitorSystem
  sharedClearanceOrSecurityAdministrationSystem
  sharedTechnicalConferenceOrAdvisoryNetwork
  sharedCounterintelligenceOrWatchlistingSystem
  sharedPublicTechnicalIndex
  : SelectorAcquisitionTarget

data TargetStatus : Set where
  targetPresent
  targetNotLocated
  targetKnownAbsent
  : TargetStatus

record SelectorAcquisition : Set where
  constructor selector-acquisition
  field
    target : SelectorAcquisitionTarget
    status : TargetStatus
    selectorClass : V.SelectorClass
    preferredEvidence : String
    fallbackEvidence : String
    promotionRule : String

open SelectorAcquisition public

publicTechnicalIndex : SelectorAcquisition
publicTechnicalIndex = selector-acquisition
  sharedPublicTechnicalIndex
  targetPresent
  V.publicInternetObserver
  "publication, patent, official biography, NTRS and institutional profile registry"
  "archived public technical directories"
  "establishes common public visibility only; does not establish selection or targeting"

personnelDirectoryAcquisition : SelectorAcquisition
personnelDirectoryAcquisition = selector-acquisition
  crossInstitutionPersonnelDirectory
  targetNotLocated
  V.institutionalPersonnelObserver
  "interagency personnel, directory, detail, visitor, project-staff or identity-management record covering roster members across institutions"
  "archived HR/personnel rosters or authenticated administrative correspondence"
  "promote only when the same observer/system has role-bearing access to multiple named roster identities"

fundingSystemAcquisition : SelectorAcquisition
fundingSystemAcquisition = selector-acquisition
  sharedFundingOrAwardManagementSystem
  targetNotLocated
  V.programmeManagementObserver
  "shared funding office, programme executive, award-management database, contract vehicle or procurement system"
  "award abstracts, contract numbers, grants, task orders, SBIR/STTR records or programme-management rosters"
  "a funding system can be a common selector even when funded persons do not collaborate"

contractorRegistryAcquisition : SelectorAcquisition
contractorRegistryAcquisition = selector-acquisition
  sharedPrimeOrSubcontractorRegistry
  targetNotLocated
  V.contractorOrProcurementObserver
  "shared prime/subcontractor, supplier or procurement registry spanning the relevant programmes/institutions"
  "supplier lists, purchase orders, contract announcements, teaming agreements or technology-transfer records"
  "common contractor visibility is distinct from common technical programme membership"

facilityAccessAcquisition : SelectorAcquisition
facilityAccessAcquisition = selector-acquisition
  sharedFacilityAccessOrVisitorSystem
  targetNotLocated
  V.facilityAccessObserver
  "facility badge/access, visitor, laboratory-user or secure-site access system"
  "visitor logs, badge records, facility user rosters, access-control policy records"
  "same access observer must be established; sensitive-work inference alone is insufficient"

securityAdministrationAcquisition : SelectorAcquisition
securityAdministrationAcquisition = selector-acquisition
  sharedClearanceOrSecurityAdministrationSystem
  targetNotLocated
  V.securityAdministrationObserver
  "clearance adjudication, security reporting, insider-threat, personnel-security or interagency security-administration records"
  "official/declassified security-program documentation or authenticated personnel-security records"
  "clearance/access must be source-backed per person; employer or technical sensitivity does not imply clearance"

professionalNetworkAcquisition : SelectorAcquisition
professionalNetworkAcquisition = selector-acquisition
  sharedTechnicalConferenceOrAdvisoryNetwork
  targetNotLocated
  V.professionalNetworkObserver
  "conference, advisory panel, review board, standards committee, working group or technical society roster spanning multiple people"
  "proceedings, panel agendas, workshop rosters, review-board membership or co-citation network with same-object identity receipts"
  "professional co-visibility may reveal a selector surface without requiring direct personal acquaintance"

intelligenceSelectorAcquisition : SelectorAcquisition
intelligenceSelectorAcquisition = selector-acquisition
  sharedCounterintelligenceOrWatchlistingSystem
  targetNotLocated
  V.intelligenceCollectionObserver
  "declassified or official counterintelligence, watchlisting, technical-intelligence targeting, threat-reporting or collection record"
  "FOIA/declassification releases, inspector-general records, congressional exhibits, court filings or authenticated government records"
  "promotion requires direct source evidence of a common observer/system; public suspicion is not sufficient"

------------------------------------------------------------------------
-- Reopenable hypothesis semantics.
------------------------------------------------------------------------

data SelectorHypothesis : Set where
  publicOnlySelector
  personnelSelector
  fundingOrContractSelector
  facilityOrSecuritySelector
  professionalNetworkSelector
  intelligenceSelector
  : SelectorHypothesis

selectorSemantics : Forest.HypothesisSemantics SelectorHypothesis
selectorSemantics = Forest.hypothesisSemantics
  (λ _ → ⊥)
  (λ _ _ → ⊤)

fundingSelectorDeferred :
  Forest.HypothesisTransition selectorSemantics fundingOrContractSelector
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
fundingSelectorDeferred = Forest.defer Forest.ambiguityUnresolved

securitySelectorDeferred :
  Forest.HypothesisTransition selectorSemantics facilityOrSecuritySelector
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
securitySelectorDeferred = Forest.defer Forest.ambiguityUnresolved

intelligenceSelectorDeferred :
  Forest.HypothesisTransition selectorSemantics intelligenceSelector
    Forest.active (Forest.reopenable Forest.ambiguityUnresolved)
intelligenceSelectorDeferred = Forest.defer Forest.ambiguityUnresolved

failedSearchDoesNotRefuteSelector :
  Forest.HypothesisTransition selectorSemantics intelligenceSelector
    (Forest.reopenable Forest.ambiguityUnresolved) Forest.refuted → ⊥
failedSearchDoesNotRefuteSelector = Forest.noDirectDormantRefutation

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SelectorAcquisitionBoundary : Set where
  constructor selector-acquisition-boundary
  field
    publicVisibilityCreatesCommonObserver : Bool
    publicVisibilityCreatesCommonObserverIsTrue :
      publicVisibilityCreatesCommonObserver ≡ true

    publicObserverExplainsWhyRosterWasSelected : Bool
    publicObserverExplainsWhyRosterWasSelectedIsFalse :
      publicObserverExplainsWhyRosterWasSelected ≡ false

    strongerObserverSearchRequiresVictimVictimContact : Bool
    strongerObserverSearchRequiresVictimVictimContactIsFalse :
      strongerObserverSearchRequiresVictimVictimContact ≡ false

    failedSearchEqualsKnownAbsence : Bool
    failedSearchEqualsKnownAbsenceIsFalse : failedSearchEqualsKnownAbsence ≡ false

    commonSelectorImpliesHarm : Bool
    commonSelectorImpliesHarmIsFalse : commonSelectorImpliesHarm ≡ false

canonicalSelectorAcquisitionBoundary : SelectorAcquisitionBoundary
canonicalSelectorAcquisitionBoundary = selector-acquisition-boundary
  true refl
  false refl
  false refl
  false refl
  false refl

module DASHI.Culture.MissingDeceasedSelectorDiscriminationFrontierExact where

------------------------------------------------------------------------
-- SELECTOR DISCRIMINATION FRONTIER FOR THE MISSING/DECEASED ROSTER
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as Visibility
import DASHI.Core.SelectorDiscriminationSearchExact as Search

------------------------------------------------------------------------
-- Current declared candidates.
------------------------------------------------------------------------

publicInternetCandidate : Search.SelectorSearchCandidate
publicInternetCandidate = Search.selector-search-candidate
  Visibility.publicInternetObserver
  Search.sourceBacked
  Search.extremelyCoarse
  0
  "publications, patents, NTRS, laboratory profiles, official biographies and public technical pages expose many roster identities/work areas"
  "the same observer covers an enormous comparison population; no roster-specific selection rule is supplied"
  "source-backed public registry"

personnelCandidate : Search.SelectorSearchCandidate
personnelCandidate = Search.selector-search-candidate
  Visibility.institutionalPersonnelObserver
  Search.unlocated
  Search.unresolvedDiscrimination
  2
  "cross-institution personnel/identity-management coverage not yet established"
  "potentially narrower than public visibility if one system actually spans multiple roster members"
  "requires primary personnel/directory/system receipt"

fundingCandidate : Search.SelectorSearchCandidate
fundingCandidate = Search.selector-search-candidate
  Visibility.programmeManagementObserver
  Search.partiallySourceBacked
  Search.intermediate
  1
  "individual funding/programme surfaces are documented for several people, but one cross-roster award-management observer is not yet established"
  "funding/contract administration is potentially more discriminating than generic public visibility because it records programme-specific roles"
  "primary award/contract/programme records required for cross-roster lift"

contractorCandidate : Search.SelectorSearchCandidate
contractorCandidate = Search.selector-search-candidate
  Visibility.contractorOrProcurementObserver
  Search.unlocated
  Search.unresolvedDiscrimination
  2
  "no common prime/subcontractor/procurement registry is presently established"
  "could span otherwise unrelated programmes through supplier/procurement infrastructure"
  "requires contract, supplier, procurement or technology-transfer receipts"

facilityCandidate : Search.SelectorSearchCandidate
facilityCandidate = Search.selector-search-candidate
  Visibility.facilityAccessObserver
  Search.unlocated
  Search.unresolvedDiscrimination
  3
  "no common facility-access system presently established"
  "facility access can be highly discriminating but only if one actual access observer spans named persons"
  "requires visitor/badge/lab-user/access-control records"

securityCandidate : Search.SelectorSearchCandidate
securityCandidate = Search.selector-search-candidate
  Visibility.securityAdministrationObserver
  Search.unlocated
  Search.unresolvedDiscrimination
  4
  "no common clearance/personnel-security observer presently established"
  "could be highly discriminating if source-backed per person and shared at system level"
  "requires clearance/access/security-administration evidence; sensitive work is not a substitute"

professionalCandidate : Search.SelectorSearchCandidate
professionalCandidate = Search.selector-search-candidate
  Visibility.professionalNetworkObserver
  Search.partiallySourceBacked
  Search.coarse
  1
  "publication/conference visibility exists individually; no one cross-roster panel/working-group observer yet established"
  "professional networks can narrow technical populations without implying collaboration"
  "requires common conference, advisory, standards, review-board, workshop or society roster"

intelligenceCandidate : Search.SelectorSearchCandidate
intelligenceCandidate = Search.selector-search-candidate
  Visibility.intelligenceCollectionObserver
  Search.unlocated
  Search.unresolvedDiscrimination
  5
  "no common intelligence/counterintelligence/watchlisting observer is presently established"
  "would be potentially highly discriminating, but discrimination cannot be assumed in advance of evidence"
  "requires declassified, official, judicial, congressional or authenticated government source"

------------------------------------------------------------------------
-- Public visibility covers but fails the discrimination gate.
------------------------------------------------------------------------

publicCoversRoster : Search.CoversDeclaredRoster publicInternetCandidate
publicCoversRoster = Search.covers-declared-roster
  "current source registry establishes public discoverability for multiple named roster members"

publicSourceBacked : Search.SourceBackedCandidate publicInternetCandidate
publicSourceBacked = Search.source-backed-candidate
  "DOI/patent/NTRS/institutional-source registry"

publicDiscriminationFrontier : Search.SelectorAcquisitionFrontier
publicDiscriminationFrontier = Search.selector-acquisition-frontier
  publicInternetCandidate
  Search.missingDiscrimination
  "define an explicit comparison population and recover a feature/observer that substantially narrows the roster relative to the public technical population"
  "common-selector explanatory search"

------------------------------------------------------------------------
-- Highest-alpha acquisition frontiers.
------------------------------------------------------------------------

fundingCoverageFrontier : Search.SelectorAcquisitionFrontier
fundingCoverageFrontier = Search.selector-acquisition-frontier
  fundingCandidate
  Search.missingCoverage
  "recover one award-management/funding/procurement system demonstrably spanning multiple named roster members or their exact programmes"
  "test funding-system common-selector hypothesis"

personnelCoverageFrontier : Search.SelectorAcquisitionFrontier
personnelCoverageFrontier = Search.selector-acquisition-frontier
  personnelCandidate
  Search.missingCoverage
  "recover a cross-institution personnel, detail, directory, visitor or identity-management system with named-person receipts"
  "test personnel-system common-selector hypothesis"

securityCoverageFrontier : Search.SelectorAcquisitionFrontier
securityCoverageFrontier = Search.selector-acquisition-frontier
  securityCandidate
  Search.missingCoverage
  "establish actual security/clearance/access visibility per named person and then prove one shared administering observer"
  "test security-administration common-selector hypothesis"

professionalCoverageFrontier : Search.SelectorAcquisitionFrontier
professionalCoverageFrontier = Search.selector-acquisition-frontier
  professionalCandidate
  Search.missingCoverage
  "search conference programmes, advisory boards, review panels, standards bodies, workshops and technical society rosters for repeated same-object names"
  "test professional-network common-selector hypothesis"

intelligenceProvenanceFrontier : Search.SelectorAcquisitionFrontier
intelligenceProvenanceFrontier = Search.selector-acquisition-frontier
  intelligenceCandidate
  Search.missingProvenance
  "recover a declassified/official source establishing a common CI/intelligence/watchlisting/technical-targeting observer before evaluating its coverage"
  "test intelligence-selector hypothesis without speculative promotion"

------------------------------------------------------------------------
-- Current ranking: not probability, merely acquisition priority.
-- Funding/procurement and professional-network surfaces are cheapest because
-- they have accessible public/archival records and can discriminate beyond
-- public searchability without requiring private security records.
------------------------------------------------------------------------

data AcquisitionPriority : Set where
  firstTier
  secondTier
  thirdTier
  : AcquisitionPriority

record PrioritisedSelectorTarget : Set where
  constructor prioritised-selector-target
  field
    priority : AcquisitionPriority
    candidate : Search.SelectorSearchCandidate
    reason : String

open PrioritisedSelectorTarget public

fundingPriority : PrioritisedSelectorTarget
fundingPriority = prioritised-selector-target
  firstTier fundingCandidate
  "programme/award records are sourceable, person-specific, and may span institutions without requiring victim-victim contact"

professionalPriority : PrioritisedSelectorTarget
professionalPriority = prioritised-selector-target
  firstTier professionalCandidate
  "conference/panel/working-group records are public or archival and can reveal cross-institution technical co-visibility"

personnelPriority : PrioritisedSelectorTarget
personnelPriority = prioritised-selector-target
  secondTier personnelCandidate
  "potentially discriminating but access to cross-institution personnel records is less straightforward"

contractorPriority : PrioritisedSelectorTarget
contractorPriority = prioritised-selector-target
  secondTier contractorCandidate
  "supplier/procurement networks can span programmes, but entity resolution and contract lineage are required"

facilityPriority : PrioritisedSelectorTarget
facilityPriority = prioritised-selector-target
  secondTier facilityCandidate
  "facility-access records can discriminate strongly but may be difficult to obtain"

securityPriority : PrioritisedSelectorTarget
securityPriority = prioritised-selector-target
  thirdTier securityCandidate
  "high potential discrimination but no per-person clearance/access receipt presently exists and records may be restricted"

intelligencePriority : PrioritisedSelectorTarget
intelligencePriority = prioritised-selector-target
  thirdTier intelligenceCandidate
  "requires unusually strong provenance before even the observer itself can be promoted"

record SelectorFrontierBoundary : Set where
  constructor selector-frontier-boundary
  field
    publicCoverageAlreadyEstablished : Bool
    publicCoverageAlreadyEstablishedIsTrue :
      publicCoverageAlreadyEstablished ≡ true

    publicCoverageCountsAsRosterExplanation : Bool
    publicCoverageCountsAsRosterExplanationIsFalse :
      publicCoverageCountsAsRosterExplanation ≡ false

    acquisitionPriorityEqualsProbabilityOfHypothesis : Bool
    acquisitionPriorityEqualsProbabilityOfHypothesisIsFalse :
      acquisitionPriorityEqualsProbabilityOfHypothesis ≡ false

    privateSelectorMustBeSearchedBeforePublicArchivalSelectors : Bool
    privateSelectorMustBeSearchedBeforePublicArchivalSelectorsIsFalse :
      privateSelectorMustBeSearchedBeforePublicArchivalSelectors ≡ false

canonicalSelectorFrontierBoundary : SelectorFrontierBoundary
canonicalSelectorFrontierBoundary = selector-frontier-boundary
  true refl
  false refl
  false refl
  false refl

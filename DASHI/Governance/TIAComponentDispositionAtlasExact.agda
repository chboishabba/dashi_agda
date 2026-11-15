module DASHI.Governance.TIAComponentDispositionAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- TIA COMPONENT DISPOSITION ATLAS
--
-- Source-bounded reconstruction of what the public record actually pays after
-- congressional termination.  A statutory exception/continuation category is
-- not a named successor component, custodian, asset transfer or Palantir edge.
------------------------------------------------------------------------

publicLaw10887 : Source.AttributedSource
publicLaw10887 = Source.mkNoDOISource
  "United States Congress"
  "Department of Defense Appropriations Act, 2004, Public Law 108-87, section 8131"
  "U.S. Statutes at Large / GovInfo"
  "2003"
  "https://www.govinfo.gov/content/pkg/PLAW-108publ87/html/PLAW-108publ87.htm"
  Source.governmentSource
  "primary statutory disposition: TIA funding restriction; exception for expressly funded NFIP processing, analysis and collaboration tools; definition includes successor programs and individual components"
  Source.publicAttribution

senateConference2003 : Source.AttributedSource
senateConference2003 = Source.mkNoDOISource
  "United States Senate Select Committee on Intelligence"
  "Conference Report on H.R. 2417, Intelligence Authorization Act for Fiscal Year 2004"
  "U.S. Senate Select Committee on Intelligence"
  "2003-11-19"
  "https://www.intelligence.senate.gov/2003/11/19/publications-conference-report-hr-2417-intelligence-authorization-act-fiscal-year-2004-november-19/"
  Source.governmentSource
  "congressional interpretation: DARPA TIA terminated while requested funds were supplied to NFIP for processing, analysis and collaboration tools for counterterrorism foreign intelligence"
  Source.publicAttribution

nationalAcademiesTIAHistory : Source.AttributedSource
nationalAcademiesTIAHistory = Source.mkNoDOISource
  "National Research Council"
  "Protecting Individual Privacy in the Struggle Against Terrorists: A Framework for Program Assessment, Appendix J"
  "National Academies Press"
  "2008"
  "https://www.nationalacademies.org/read/12452/chapter/16"
  Source.academicBookSource
  "authoritative retrospective synthesising public DARPA/government sources; records TIA research threads, prototype/testbed purpose, and the 2003 statutory disposition language"
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "TIA post-termination component disposition atlas"
  "DASHI.Governance.TIAComponentDispositionAtlasExact"
  (publicLaw10887 ∷ senateConference2003 ∷ nationalAcademiesTIAHistory ∷ [])
  "termination, statutory continuation exception, public component identity and unresolved classified-annex successor details"

data DispositionState : Set where
  terminatedByPublicRecord : DispositionState
  continuedByStatutoryException : DispositionState
  namedTransferredComponent : DispositionState
  classifiedOrUnresolvedDisposition : DispositionState

record ComponentDisposition : Set where
  constructor component-disposition
  field
    componentLabel : String
    state : DispositionState
    custodian : String
    fundingOrAuthority : String
    source : Source.AttributedSource
    boundedReading : String
    namedSameObjectIdentityPaid : Bool
    assetOrCodeTransferPaid : Bool

open ComponentDisposition public

tiaUmbrellaDisposition : ComponentDisposition
tiaUmbrellaDisposition = component-disposition
  "DARPA Terrorism/Total Information Awareness umbrella programme"
  terminatedByPublicRecord
  "DARPA public umbrella"
  "Public Law 108-87 section 8131"
  publicLaw10887
  "public funding for the umbrella programme was barred; this does not imply destruction of every research result or later independent capability"
  true false

nfipToolsDisposition : ComponentDisposition
nfipToolsDisposition = component-disposition
  "processing, analysis, and collaboration tools for counterterrorism foreign intelligence"
  continuedByStatutoryException
  "National Foreign Intelligence Program; exact classified programme/custodian unresolved in this public atlas"
  "expressly funded exception described by section 8131 and the conference report"
  senateConference2003
  "the continuation category is public; the named component/programme identity behind the classified annex remains unpaid"
  false false

publicDispositionAtlas : List ComponentDisposition
publicDispositionAtlas = tiaUmbrellaDisposition ∷ nfipToolsDisposition ∷ []

publicTerminationReceiptPaid : Bool
publicTerminationReceiptPaid = true

nfipContinuationExceptionPaid : Bool
nfipContinuationExceptionPaid = true

namedSuccessorComponentIdentityPaid : Bool
namedSuccessorComponentIdentityPaid = false

sameObjectCustodianPaid : Bool
sameObjectCustodianPaid = false

sameObjectAssetTransferPaid : Bool
sameObjectAssetTransferPaid = false

continuationExceptionMeansPalantir : Bool
continuationExceptionMeansPalantir = false

record DispositionBoundary : Set where
  constructor disposition-boundary
  field
    statutoryContinuationEqualsNamedSuccessor : Bool
    successorDefinitionProvesAnySpecificVendor : Bool
    continuedCapabilityProvesAssetTransfer : Bool
    classifiedAnnexMayBeFilledByInference : Bool

canonicalDispositionBoundary : DispositionBoundary
canonicalDispositionBoundary = disposition-boundary false false false false

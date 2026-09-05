module DASHI.Culture.MissingDeceasedCommonSelectorVisibilityExact where

------------------------------------------------------------------------
-- COMMON-SELECTOR VISIBILITY FIXTURE FOR THE MISSING/DECEASED ROSTER
--
-- This fixture asks a different question from the technical dependency graph:
-- what source-backed observer classes could see each person?  It does not
-- require victim-victim contact, one shared programme, or one shared employer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as V
import DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExact as Sources

------------------------------------------------------------------------
-- Publicly visible scientific / technical work receipts.
------------------------------------------------------------------------

hicksPublicWork : V.VisibilityReceipt
hicksPublicWork = V.visibility-receipt
  "Michael David Hicks"
  V.publicScientificWork
  "JPL comet/asteroid research; DART, NEAT, Dawn, Deep Space 1 science-team history"
  V.primaryInstitutionalReceipt
  Sources.hicksJPLFamilyNews
  "This establishes that Hicks's technical history was publicly/institutionally discoverable; it does not identify who actually observed it."

maiwaldPublicWork : V.VisibilityReceipt
maiwaldPublicWork = V.visibility-receipt
  "Frank W. Maiwald"
  V.publicScientificWork
  "planetary mass spectrometry and biosignature action-spectroscopy PI work"
  V.primaryInstitutionalReceipt
  Sources.maiwaldSURP2023
  "JPL publicly identifies Maiwald and the named project/PI role."

rezaPublicPatent : V.VisibilityReceipt
rezaPublicPatent = V.visibility-receipt
  "Monica A. Jacinto / Monica Reza"
  V.publicScientificWork
  "US20040208777A1 burn-resistant/high-strength alloy inventorship"
  V.primaryPublicReceipt
  Sources.jacintoHardwickPatent2004
  "Patent inventorship and technical subject are publicly searchable."

leblancPublicWork : V.VisibilityReceipt
leblancPublicWork = V.visibility-receipt
  "Joshua LeBlanc"
  V.publicScientificWork
  "NASA fission surface power / Space Nuclear Propulsion I&C authorship and technical-lead role"
  V.primaryInstitutionalReceipt
  Sources.leblancNTRS2025
  "NASA NTRS makes LeBlanc's authorship and SNP I&C TechMat lead role institutionally/publicly visible."

loureiroPublicWork : V.VisibilityReceipt
loureiroPublicWork = V.visibility-receipt
  "Nuno F. G. Loureiro"
  V.publicScientificWork
  "magnetic reconnection / strongly magnetized plasma / fusion research"
  V.primaryPublicReceipt
  Sources.loureiroViriato2016
  "Publication-level work makes a substantial part of Loureiro's technical profile publicly discoverable."

grillmairPublicWork : V.VisibilityReceipt
grillmairPublicWork = V.visibility-receipt
  "Carl J. Grillmair"
  V.publicScientificWork
  "stellar streams / Galactic structure / dark-matter work"
  V.primaryPublicReceipt
  Sources.grillmairCrossroads2017
  "Publication-level astronomy work is publicly discoverable."

mccaslandPublicRole : V.VisibilityReceipt
mccaslandPublicRole = V.visibility-receipt
  "William N. McCasland"
  V.publicInstitutionalRole
  "USAF/AFRL Space Vehicles, GPS, Space Based Laser and science-and-technology leadership history"
  V.primaryInstitutionalReceipt
  Sources.mccaslandUSAFBiography
  "Official USAF biography makes these career roles publicly/institutionally visible; it does not disclose classified programme details."

chavezPublicRole : V.VisibilityReceipt
chavezPublicRole = V.visibility-receipt
  "Anthony Chavez"
  V.publicInstitutionalRole
  "DARHT engineering and Scorpius accelerator design work"
  V.primaryInstitutionalReceipt
  Sources.anthonyChavezLANL2025
  "LANL's own profile made this technical role publicly/institutionally discoverable."

thomasPublicWork : V.VisibilityReceipt
thomasPublicWork = V.visibility-receipt
  "Jason R. Thomas"
  V.publicScientificWork
  "Novartis STING-IRF3/NFkB chemical-biology screen"
  V.primaryPublicReceipt
  Sources.thomasSTING2018
  "Publication authorship makes this work publicly discoverable."

------------------------------------------------------------------------
-- Public-observer witness language.
------------------------------------------------------------------------

data PubliclyVisible : V.VisibilityReceipt → Set where
  hicksVisible : PubliclyVisible hicksPublicWork
  maiwaldVisible : PubliclyVisible maiwaldPublicWork
  rezaVisible : PubliclyVisible rezaPublicPatent
  leblancVisible : PubliclyVisible leblancPublicWork
  loureiroVisible : PubliclyVisible loureiroPublicWork
  grillmairVisible : PubliclyVisible grillmairPublicWork
  mccaslandVisible : PubliclyVisible mccaslandPublicRole
  chavezVisible : PubliclyVisible chavezPublicRole
  thomasVisible : PubliclyVisible thomasPublicWork

publicInternet : V.SelectorCapability
publicInternet = V.selector-capability
  V.publicInternetObserver
  PubliclyVisible
  "canonical public/institutional publications, patents, official biographies, NTRS and laboratory profiles"

hicksPubliclyVisible : V.PersonVisibleTo publicInternet hicksPublicWork
hicksPubliclyVisible = V.person-visible-to hicksVisible

maiwaldPubliclyVisible : V.PersonVisibleTo publicInternet maiwaldPublicWork
maiwaldPubliclyVisible = V.person-visible-to maiwaldVisible

rezaPubliclyVisible : V.PersonVisibleTo publicInternet rezaPublicPatent
rezaPubliclyVisible = V.person-visible-to rezaVisible

leblancPubliclyVisible : V.PersonVisibleTo publicInternet leblancPublicWork
leblancPubliclyVisible = V.person-visible-to leblancVisible

loureiroPubliclyVisible : V.PersonVisibleTo publicInternet loureiroPublicWork
loureiroPubliclyVisible = V.person-visible-to loureiroVisible

grillmairPubliclyVisible : V.PersonVisibleTo publicInternet grillmairPublicWork
grillmairPubliclyVisible = V.person-visible-to grillmairVisible

mccaslandPubliclyVisible : V.PersonVisibleTo publicInternet mccaslandPublicRole
mccaslandPubliclyVisible = V.person-visible-to mccaslandVisible

chavezPubliclyVisible : V.PersonVisibleTo publicInternet chavezPublicRole
chavezPubliclyVisible = V.person-visible-to chavezVisible

thomasPubliclyVisible : V.PersonVisibleTo publicInternet thomasPublicWork
thomasPubliclyVisible = V.person-visible-to thomasVisible

------------------------------------------------------------------------
-- Important result: one does not need a shared programme to construct a common
-- PUBLIC visibility observer.  But that is a very coarse observer: many other
-- scientists/engineers are likewise publicly visible.  It cannot by itself
-- explain roster selection.
------------------------------------------------------------------------

hicksRezaCommonPublicVisibility : V.CommonVisibilityPair hicksPublicWork rezaPublicPatent
hicksRezaCommonPublicVisibility = V.common-visibility-pair
  publicInternet
  hicksPubliclyVisible
  rezaPubliclyVisible
  "both have source-backed public technical profiles"

loureiroLeBlancCommonPublicVisibility : V.CommonVisibilityPair loureiroPublicWork leblancPublicWork
loureiroLeBlancCommonPublicVisibility = V.common-visibility-pair
  publicInternet
  loureiroPubliclyVisible
  leblancPubliclyVisible
  "both are discoverable through public scientific/institutional records despite distinct programmes and institutions"

------------------------------------------------------------------------
-- Stronger selector classes remain unresolved acquisition targets.
------------------------------------------------------------------------

data SelectorStatus : Set where
  sourceBackedPresent
  candidateNotLocated
  candidateKnownAbsent
  : SelectorStatus

record SelectorLayerAssessment : Set where
  constructor selector-layer-assessment
  field
    selectorLayer : V.SelectorClass
    status : SelectorStatus
    evidenceNeeded : String
    boundedReading : String

publicLayer : SelectorLayerAssessment
publicLayer = selector-layer-assessment
  V.publicInternetObserver
  sourceBackedPresent
  "existing public source registry"
  "A public observer can see many roster members' identities and technical work; this is not yet a discriminating selector for the cluster."

personnelLayer : SelectorLayerAssessment
personnelLayer = selector-layer-assessment
  V.institutionalPersonnelObserver
  candidateNotLocated
  "personnel-directory, HR, interagency detail, visitor/access, contractor, clearance or programme-management records establishing a cross-institution observer"
  "No single cross-roster personnel observer is currently established."

contractorLayer : SelectorLayerAssessment
contractorLayer = selector-layer-assessment
  V.contractorOrProcurementObserver
  candidateNotLocated
  "shared prime/subcontractor, procurement platform, supplier, funding-office or award-management records"
  "A contractor/procurement observer could span people who never worked together, but requires source-backed receipts."

securityLayer : SelectorLayerAssessment
securityLayer = selector-layer-assessment
  V.securityAdministrationObserver
  candidateNotLocated
  "clearance/access adjudication, security reporting, facility-access, insider-threat or interagency personnel-system records"
  "Security visibility must not be inferred merely from sensitive work or employer."

intelligenceLayer : SelectorLayerAssessment
intelligenceLayer = selector-layer-assessment
  V.intelligenceCollectionObserver
  candidateNotLocated
  "declassified/official intelligence collection, counterintelligence, watchlisting or technical-targeting record"
  "No common intelligence selector is presently established."

------------------------------------------------------------------------
-- Current epistemic boundary.
------------------------------------------------------------------------

record CurrentSelectorAssessment : Set where
  constructor current-selector-assessment
  field
    commonPublicVisibilityEstablished : Bool
    commonPublicVisibilityEstablishedIsTrue :
      commonPublicVisibilityEstablished ≡ true

    publicVisibilityIsDiscriminatingEnoughToExplainRoster : Bool
    publicVisibilityIsDiscriminatingEnoughToExplainRosterIsFalse :
      publicVisibilityIsDiscriminatingEnoughToExplainRoster ≡ false

    oneCommonProgrammeRequired : Bool
    oneCommonProgrammeRequiredIsFalse : oneCommonProgrammeRequired ≡ false

    victimVictimContactRequired : Bool
    victimVictimContactRequiredIsFalse : victimVictimContactRequired ≡ false

    commonPrivateSelectorEstablished : Bool
    commonPrivateSelectorEstablishedIsFalse :
      commonPrivateSelectorEstablished ≡ false

    commonAdversaryEstablished : Bool
    commonAdversaryEstablishedIsFalse : commonAdversaryEstablished ≡ false

canonicalCurrentSelectorAssessment : CurrentSelectorAssessment
canonicalCurrentSelectorAssessment = current-selector-assessment
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl

module DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- MINETTE SAME-OBJECT MICROHISTORY
--
-- This owner pays finer chronology, benefit-performance, compensation and
-- legal-record coordinates without promoting them into completed settlement or
-- causal mobility. Apparent date disagreement remains explicit until the
-- underlying newspaper issue/image is inspected.
------------------------------------------------------------------------

prestMinetteMarsanSource : Source.AttributedSource
prestMinetteMarsanSource =
  Source.mkDOISource
    "Julia Prest"
    "Parisian Palimpsests and Creole Creations: Mme Marsan and Dlle Minette play Nina on the Caribbean Stage"
    "Early Modern French Studies 41(2)"
    "2019"
    "10.1080/20563035.2019.1592813"
    "https://research-repository.st-andrews.ac.uk/handle/10023/20801"
    Source.academicArticleSource
    "peer-reviewed same-object performance chronology, benefit-performance and contracted-salary evidence for Minette; cited newspaper/notarial coordinates remain distinct from direct inspection of each original"
    Source.publicAttribution

camierMinetteLifeSource : Source.AttributedSource
camierMinetteLifeSource =
  Source.mkDOISource
    "Bernard Camier"
    "A Free Artist of Color in Late-Eighteenth-Century Saint-Domingue: The Life and Times of Minette"
    "Music & Musical Performance: An International Journal 1(1), article 1, pp. 1-26"
    "2022"
    "10.34051/j/2026.1"
    "https://scholars.unh.edu/mmp/vol1/iss1/1/"
    Source.academicArticleSource
    "detailed biographical study with a full known-performance list and archival genealogy/legal coordinates; archival references do not mean DASHI inspected the underlying ANOM originals"
    Source.publicAttribution

colonialNetworksMinetteSource : Source.AttributedSource
colonialNetworksMinetteSource =
  Source.mkNoDOISource
    "Julia Prest"
    "A Creole Performer Onstage: Minette"
    "Colonial Networks public research presentation"
    "2025"
    "https://www.colonialnetworks.org/?p=803"
    Source.institutionalSource
    "public research synthesis distinguishing Minette's late-1780 concert appearance from her first full theatrical benefit performance; used as a bounded acquisition aid rather than primary-newspaper authority"
    Source.publicAttribution

------------------------------------------------------------------------
-- Event-type distinction.
------------------------------------------------------------------------

data CareerEventKind : Set where
  publicConcertAppearance : CareerEventKind
  retrospectiveTheatreDebut : CareerEventKind
  fullTheatricalBenefitPerformance : CareerEventKind
  selfOrganisedBenefitPerformance : CareerEventKind
  legalDisputeEvent : CareerEventKind
  legalNoticeEvent : CareerEventKind

record MinetteEventReceipt : Set where
  constructor minette-event-receipt
  field
    eventKind : CareerEventKind
    dateReference : String
    venueReference : String
    eventReference : String
    source : Source.AttributedSource
    citedPrimaryCoordinate : String
    primaryOriginalInspectedHere : Bool
    primaryOriginalInspectedHereIsFalse : primaryOriginalInspectedHere ≡ false

open MinetteEventReceipt public

christmas1780ConcertReceipt : MinetteEventReceipt
christmas1780ConcertReceipt =
  minette-event-receipt
    publicConcertAppearance
    "Christmas season 1780"
    "Port-au-Prince playhouse"
    "Prest's Colonial Networks synthesis identifies Minette's first public appearance as a soloist in a Christmas concert, while noting that the announcement calls her a young lady rather than naming her"
    colonialNetworksMinetteSource
    "Supplement aux Affiches americaines announcement identified by the research project; exact image/page still to root in this owner"
    false refl

moreauFebruary1781DebutReceipt : MinetteEventReceipt
moreauFebruary1781DebutReceipt =
  minette-event-receipt
    retrospectiveTheatreDebut
    "13 February 1781"
    "Port-au-Prince theatre"
    "Moreau de Saint-Mery retrospectively describes a first theatre debut in the role of Isabelle in Isabelle et Gertrude; Prest 2019 reproduces and analyses this passage"
    prestMinetteMarsanSource
    "Moreau de Saint-Mery, Description topographique, volume II, p. 989"
    false refl

march1781BenefitReceipt : MinetteEventReceipt
march1781BenefitReceipt =
  minette-event-receipt
    fullTheatricalBenefitPerformance
    "6 March 1781"
    "Port-au-Prince theatre"
    "Prest's Colonial Networks synthesis distinguishes Minette's first full theatrical performance as a benefit performance organised by her mentor Mme Acquaire"
    colonialNetworksMinetteSource
    "local newspaper announcement underlying the Theatre in Saint-Domingue database; exact issue/page remains an acquisition target"
    false refl

zemire1783BenefitReceipt : MinetteEventReceipt
zemire1783BenefitReceipt =
  minette-event-receipt
    selfOrganisedBenefitPerformance
    "1783"
    "Port-au-Prince theatre"
    "Prest 2019 reports that Minette cast herself in the lead of Zemire et Azor in a benefit performance that she organised herself"
    prestMinetteMarsanSource
    "Prest 2019 performance reconstruction from local newspaper documentation"
    false refl

nina1787BenefitReceipt : MinetteEventReceipt
nina1787BenefitReceipt =
  minette-event-receipt
    selfOrganisedBenefitPerformance
    "announcement 1 March 1787; review 10 March 1787"
    "Port-au-Prince theatre"
    "Prest 2019 reports Minette's first Nina as a benefit performance she arranged herself and roots the announcement/review in the Affiches americaines"
    prestMinetteMarsanSource
    "Affiches americaines, 1 March 1787 announcement; 10 March 1787 review"
    false refl

minette1789LegalDisputeReceipt : MinetteEventReceipt
minette1789LegalDisputeReceipt =
  minette-event-receipt
    legalDisputeEvent
    "complaint 25-27 November 1789; judgment 15 December 1789"
    "Port-au-Prince"
    "Camier identifies a legal case involving Minette, Mozart, Dlle Marthe, Sr Simon, Daubagna and Parizet"
    camierMinetteLifeSource
    "Greffe de Port-au-Prince, gr 31 fols. 94-96, DPPC, ANOM"
    false refl

------------------------------------------------------------------------
-- Contracted salary / nonpayment same-object receipt.
------------------------------------------------------------------------

record MinetteSalaryNonpaymentReceipt : Set where
  constructor minette-salary-nonpayment-receipt
  field
    contractDateReference : String
    contractTermReference : String
    annualSalaryReference : String
    nonpaymentReference : String
    archivalCoordinate : String
    source : Source.AttributedSource
    primaryOriginalInspectedHere : Bool
    primaryOriginalInspectedHereIsFalse :
      primaryOriginalInspectedHere ≡ false
    contractAmountSameObjectPaid : Bool
    contractAmountSameObjectPaidIsTrue :
      contractAmountSameObjectPaid ≡ true
    nonpaymentSameObjectPaid : Bool
    nonpaymentSameObjectPaidIsTrue :
      nonpaymentSameObjectPaid ≡ true
    actualSettlementSameObjectPaid : Bool
    actualSettlementSameObjectPaidIsFalse :
      actualSettlementSameObjectPaid ≡ false

open MinetteSalaryNonpaymentReceipt public

minette1784SalaryNonpaymentReceipt : MinetteSalaryNonpaymentReceipt
minette1784SalaryNonpaymentReceipt =
  minette-salary-nonpayment-receipt
    "9 June 1784"
    "private contract for three years"
    "8000 livres per year"
    "Prest 2019 reports that Saint-Martin's will revealed the contracted salary had never been paid"
    "ANOM, DPPC, Notaire Michel, minutes of 9 June 1784, Testament du Sr Saint-Martin"
    prestMinetteMarsanSource
    false refl
    true refl
    true refl
    false refl

data ContractAndNonpaymentProveSettlement : Set where

contractAndNonpaymentDoNotProveSettlement :
  ContractAndNonpaymentProveSettlement → ⊥
contractAndNonpaymentDoNotProveSettlement ()

------------------------------------------------------------------------
-- A secondary-source date discrepancy is retained rather than silently chosen.
------------------------------------------------------------------------

prestLegalNoticeDateReceipt : MinetteEventReceipt
prestLegalNoticeDateReceipt =
  minette-event-receipt
    legalNoticeEvent
    "1 July 1790"
    "Port-au-Prince"
    "Prest's Iphigenie study cites the Affiches Americaines legal-dispute notice at page 368"
    Atlas.prestIphigenieSource
    "Affiches Americaines, 1 July 1790, p. 368"
    false refl

lamecaLegalNoticeDateReceipt : MinetteEventReceipt
lamecaLegalNoticeDateReceipt =
  minette-event-receipt
    legalNoticeEvent
    "17 July 1790"
    "Port-au-Prince"
    "the Laméca dossier reproduces the same Périgord/Minette legal-notice wording but labels it 17 July 1790"
    Atlas.lamecaSaintDomingueOperaSource
    "Affiches Americaines, Port-au-Prince, date given by Laméca as 17 July 1790"
    false refl

data SecondaryDateDisagreementResolvedWithoutPrimaryInspection : Set where

secondaryDateDisagreementNeedsPrimaryInspection :
  SecondaryDateDisagreementResolvedWithoutPrimaryInspection → ⊥
secondaryDateDisagreementNeedsPrimaryInspection ()

------------------------------------------------------------------------
-- Benefit performances establish a compensation/revenue mechanism surface, but
-- not contractual entitlement, gross receipts, expenses, net benefit or actual
-- settlement to the performer.
------------------------------------------------------------------------

data BenefitPerformancePaysSettlement : Set where

benefitPerformanceDoesNotProveSettlement :
  BenefitPerformancePaysSettlement → ⊥
benefitPerformanceDoesNotProveSettlement ()

record MinetteMicrohistoryBoundary : Set where
  constructor minette-microhistory-boundary
  field
    chronologyHasMultipleEventPredicates : Bool
    chronologyHasMultipleEventPredicatesIsTrue :
      chronologyHasMultipleEventPredicates ≡ true
    benefitMechanismSameObjectEvidencePaid : Bool
    benefitMechanismSameObjectEvidencePaidIsTrue :
      benefitMechanismSameObjectEvidencePaid ≡ true
    contractedSalaryAmountSameObjectEvidencePaid : Bool
    contractedSalaryAmountSameObjectEvidencePaidIsTrue :
      contractedSalaryAmountSameObjectEvidencePaid ≡ true
    documentedSalaryNonpaymentSameObjectEvidencePaid : Bool
    documentedSalaryNonpaymentSameObjectEvidencePaidIsTrue :
      documentedSalaryNonpaymentSameObjectEvidencePaid ≡ true
    actualSalarySettlementSameObjectEvidencePaid : Bool
    actualSalarySettlementSameObjectEvidencePaidIsFalse :
      actualSalarySettlementSameObjectEvidencePaid ≡ false
    benefitPerformanceProvesNetSettlement : Bool
    benefitPerformanceProvesNetSettlementIsFalse :
      benefitPerformanceProvesNetSettlement ≡ false
    secondaryDateDisagreementCanBeSilentlyCollapsed : Bool
    secondaryDateDisagreementCanBeSilentlyCollapsedIsFalse :
      secondaryDateDisagreementCanBeSilentlyCollapsed ≡ false
    archivalCoordinateEqualsArchiveInspection : Bool
    archivalCoordinateEqualsArchiveInspectionIsFalse :
      archivalCoordinateEqualsArchiveInspection ≡ false

canonicalMinetteMicrohistoryBoundary : MinetteMicrohistoryBoundary
canonicalMinetteMicrohistoryBoundary =
  minette-microhistory-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

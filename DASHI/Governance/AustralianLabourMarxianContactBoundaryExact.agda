module DASHI.Governance.AustralianLabourMarxianContactBoundaryExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- AUSTRALIAN LABOUR / MARXIAN CONTACT BOUNDARY
--
-- Direct contact exists at several historical layers, but Australian Labor,
-- the labour movement, Australian Marxism and later communist organisations
-- are not one object.
------------------------------------------------------------------------

eurekaMarxReception : Source.AttributedSource
eurekaMarxReception = Source.mkNoDOISource
  "Australian Communist Party historical archive / Marx reception"
  "History of the Australian Labor Movement - Chapter 1"
  "Australian Communist Party archive"
  "historical source citing Marx on Eureka"
  "https://www.auscp.org.au/history-of-the-australian-labor-movement-chapter-1"
  Source.archivalSource
  "secondary archival carrier reporting Marx's article on Eureka and his worker-versus-monopolist reading; stronger primary-carrier recovery remains desirable"
  Source.publicAttribution

leninAustralianLabor1913 : Source.AttributedSource
leninAustralianLabor1913 = Source.mkNoDOISource
  "V. I. Lenin"
  "In Australia"
  "1913 political article, available through Marxists Internet Archive"
  "1913"
  "https://www.marxists.org/archive/lenin/works/1913/jun/13.htm"
  Source.archivalSource
  "primary historical Marxist analysis distinguishing the Australian Labor Party from socialist politics and characterising it as non-socialist trade-union labourism"
  Source.publicAttribution

fisherNationalMuseum : Source.AttributedSource
fisherNationalMuseum = Source.mkNoDOISource
  "National Museum of Australia"
  "The last man: the making of Andrew Fisher and the Australian Labor Party"
  "National Museum historical interpretation"
  "2017"
  "https://www.nma.gov.au/audio/historical-interpretation-series/transcripts/the-last-man-the-making-of-andrew-fisher-and-the-australian-labor-party"
  Source.institutionalSource
  "historical source noting occasional Marx references in Fisher's Gympie labour newspaper while describing Fisher's socialism as moderate"
  Source.publicAttribution

data LabourHistoricalLayer : Set where
  colonialWorkerMovement : LabourHistoricalLayer
  australianLaborParty : LabourHistoricalLayer
  marxistSocialistGroups : LabourHistoricalLayer
  communistPartyAustralia : LabourHistoricalLayer
  tradeUnionMovement : LabourHistoricalLayer

data HistoricalContactKind : Set where
  textualObservation : HistoricalContactKind
  ideologicalReception : HistoricalContactKind
  organisationalOverlap : HistoricalContactKind
  criticalMarxistAnalysis : HistoricalContactKind

record ContactReceipt : Set where
  constructor contact-receipt
  field
    left : LabourHistoricalLayer
    right : LabourHistoricalLayer
    kind : HistoricalContactKind
    source : Source.AttributedSource
    provesIdentity : Bool
    provesDirectOrganisationalLineage : Bool

open ContactReceipt public

marxEurekaContact : ContactReceipt
marxEurekaContact = contact-receipt
  colonialWorkerMovement marxistSocialistGroups textualObservation
  eurekaMarxReception false false

leninLaborCritique : ContactReceipt
leninLaborCritique = contact-receipt
  australianLaborParty marxistSocialistGroups criticalMarxistAnalysis
  leninAustralianLabor1913 false false

fisherModerateSocialistContact : ContactReceipt
fisherModerateSocialistContact = contact-receipt
  australianLaborParty marxistSocialistGroups ideologicalReception
  fisherNationalMuseum false false

data AustralianLaborEqualsMarxism : Set where
data MarxCommentOnAustraliaMeansLaborFoundedByMarxism : Set where
data LabourMovementEqualsLaborParty : Set where

australianLaborDoesNotDefinitionallyEqualMarxism :
  AustralianLaborEqualsMarxism → ⊥
australianLaborDoesNotDefinitionallyEqualMarxism ()

marxCommentDoesNotCreateLaborLineage :
  MarxCommentOnAustraliaMeansLaborFoundedByMarxism → ⊥
marxCommentDoesNotCreateLaborLineage ()

labourMovementDoesNotDefinitionallyEqualLaborParty :
  LabourMovementEqualsLaborParty → ⊥
labourMovementDoesNotDefinitionallyEqualLaborParty ()

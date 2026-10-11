module DASHI.Cognition.EpsteinNaturePublishingBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- NATURE / SCIENTIFIC-PUBLISHING GENEALOGY BOUNDARY
--
-- The relevant documented genealogy is Robert Maxwell -> Pergamon -> later
-- Elsevier acquisition, alongside a separate Nature/Macmillan/Holtzbrinck ->
-- Springer Nature ownership line.  Jeffrey Epstein's science-network role does
-- not create ownership or privatization lineage into Nature.
------------------------------------------------------------------------

data PublishingActor : Set where
  robertMaxwell : PublishingActor
  jeffreyEpstein : PublishingActor
  pergamonPress : PublishingActor
  elsevier : PublishingActor
  macmillan : PublishingActor
  holtzbrinck : PublishingActor
  springerNature : PublishingActor
  natureJournal : PublishingActor

actorName : PublishingActor → String
actorName robertMaxwell = "Robert Maxwell"
actorName jeffreyEpstein = "Jeffrey Epstein"
actorName pergamonPress = "Pergamon Press"
actorName elsevier = "Elsevier"
actorName macmillan = "Macmillan"
actorName holtzbrinck = "Holtzbrinck"
actorName springerNature = "Springer Nature"
actorName natureJournal = "Nature"

data PublishingEdge : Set where
  foundedOrBuilt : PublishingEdge
  distributionRelationship : PublishingEdge
  acquiredBy : PublishingEdge
  majorityOwnership : PublishingEdge
  mergedInto : PublishingEdge
  scientificNetworkContact : PublishingEdge

record PublishingGenealogyReceipt : Set where
  constructor publishing-genealogy-receipt
  field
    from to : PublishingActor
    edge : PublishingEdge
    sourceBounded : Bool
    ownershipEdge : Bool
open PublishingGenealogyReceipt public

maxwellPergamonReceipt : PublishingGenealogyReceipt
maxwellPergamonReceipt = publishing-genealogy-receipt
  robertMaxwell pergamonPress foundedOrBuilt true true

pergamonElsevierReceipt : PublishingGenealogyReceipt
pergamonElsevierReceipt = publishing-genealogy-receipt
  pergamonPress elsevier acquiredBy true true

natureMacmillanReceipt : PublishingGenealogyReceipt
natureMacmillanReceipt = publishing-genealogy-receipt
  natureJournal macmillan majorityOwnership true true

macmillanHoltzbrinckReceipt : PublishingGenealogyReceipt
macmillanHoltzbrinckReceipt = publishing-genealogy-receipt
  macmillan holtzbrinck acquiredBy true true

natureSpringerNatureReceipt : PublishingGenealogyReceipt
natureSpringerNatureReceipt = publishing-genealogy-receipt
  natureJournal springerNature mergedInto true true

record EpsteinNaturePublishingStatus : Set where
  constructor epstein-nature-publishing-status
  field
    jeffreyEpsteinPrivatisedNature : Bool
    jeffreyEpsteinOwnedNature : Bool
    robertMaxwellCommercialisedScientificPublishing : Bool
    maxwellPergamonLineDocumented : Bool
    natureMacmillanHoltzbrinckLineDocumented : Bool
    sameSurnameFamilyAssociationCreatesCorporateLineage : Bool
open EpsteinNaturePublishingStatus public

currentEpsteinNaturePublishingStatus : EpsteinNaturePublishingStatus
currentEpsteinNaturePublishingStatus = epstein-nature-publishing-status
  false false true true true false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data MaxwellGenealogyCreatesEpsteinOwnership : Set where
data ScientificContactCreatesPublisherControl : Set where
data EditorialCoverageCreatesOwnershipConflict : Set where
data CommercialPublishingHistoryCreatesEpsteinCausation : Set where

maxwellPublishingGenealogyDoesNotCreateEpsteinOwnership :
  MaxwellGenealogyCreatesEpsteinOwnership → ⊥
maxwellPublishingGenealogyDoesNotCreateEpsteinOwnership ()

scientificContactDoesNotCreatePublisherControl :
  ScientificContactCreatesPublisherControl → ⊥
scientificContactDoesNotCreatePublisherControl ()

natureReportingOnEpsteinDoesNotCreateOwnershipConflict :
  EditorialCoverageCreatesOwnershipConflict → ⊥
natureReportingOnEpsteinDoesNotCreateOwnershipConflict ()

commercialPublishingHistoryDoesNotCreateEpsteinCausation :
  CommercialPublishingHistoryCreatesEpsteinCausation → ⊥
commercialPublishingHistoryDoesNotCreateEpsteinCausation ()

module DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.ComparativeInstitutionalMeaningExact as Comparative
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence

------------------------------------------------------------------------
-- DIGITAL-ESD POLITICAL ECONOMY / PROVISIONING
--
-- This is an education-facing composition layer, not a new political-economy
-- ontology.  It keeps regime labels, mechanisms, material/service carriers and
-- measured/modelled outcomes separate.
--
-- Attribution rule:
--   external source proposition != DASHI reconstruction != DASHI theorem.
-- The transcript motivates the research question but is not used below as
-- empirical authority for any world claim.
------------------------------------------------------------------------

buttelTreadmillReview : Attr.AttributedSource
buttelTreadmillReview = Attr.mkDOISource
  "Frederick H. Buttel"
  "The Treadmill of Production: An Appreciation, Assessment, and Agenda for Research"
  "Organization & Environment 17(3)"
  "2004"
  "10.1177/1086026604267938"
  "https://doi.org/10.1177/1086026604267938"
  Attr.academicArticleSource
  "Peer-reviewed theoretical/review source on the treadmill-of-production tradition and its limitations. Supports bounded growth/production/environment mechanism context; does not prove that every environmental harm or every capitalist arrangement has one cause."
  Attr.publicAttribution

curranTreadmillConsumption : Attr.AttributedSource
curranTreadmillConsumption = Attr.mkDOISource
  "Dean Curran"
  "The Treadmill of Production and the Positional Economy of Consumption"
  "Canadian Review of Sociology 54(1)"
  "2017"
  "10.1111/cars.12137"
  "https://doi.org/10.1111/cars.12137"
  Attr.academicArticleSource
  "Peer-reviewed theoretical source connecting growth-oriented production and consumption dynamics to environmental damage. Used as mechanism context, not as a universal empirical waste estimate."
  Attr.publicAttribution

correaniFoodWasteModel : Attr.AttributedSource
correaniFoodWasteModel = Attr.mkDOISource
  "Luca Correani; Patrizio Morganti; Cecilia Silvestri; Alessandro Ruggieri"
  "Food waste, circular economy, and policy with oligopolistic retailers"
  "Journal of Cleaner Production 407, 137092"
  "2023"
  "10.1016/j.jclepro.2023.137092"
  "https://doi.org/10.1016/j.jclepro.2023.137092"
  Attr.academicArticleSource
  "Theoretical oligopoly model in which food waste is endogenous to strategic interaction between differentiated retailers and consumers; source reports positive relation between individual retailer waste and market concentration/quality under the model. It is model evidence, not measured food-waste prevalence and not a universal capitalism theorem."
  Attr.publicAttribution

canonicalPoliticalEconomySourceAtlas : Attr.AttributedSourceAtlas
canonicalPoliticalEconomySourceAtlas = Attr.mkSourceAtlas
  "digital ESD political economy / waste mechanism source atlas"
  "DASHI.Education.DigitalESDPoliticalEconomyProvisioningExact"
  (buttelTreadmillReview ∷ curranTreadmillConsumption ∷ correaniFoodWasteModel ∷ [])
  "Mechanism-discriminating sources only. Regime identity, mechanism, material/service carrier and measured/modelled outcome remain separate."

------------------------------------------------------------------------
-- Education-facing political-economy coordinates.
------------------------------------------------------------------------

data PoliticalEconomyCoordinate : Set where
  ownershipProvisionForm : PoliticalEconomyCoordinate
  profitRevenueModel : PoliticalEconomyCoordinate
  accumulationGrowthPressure : PoliticalEconomyCoordinate
  competitionCooperation : PoliticalEconomyCoordinate
  intellectualPropertyLicensing : PoliticalEconomyCoordinate
  procurementCapitalFinancing : PoliticalEconomyCoordinate
  subsidyPublicFinancing : PoliticalEconomyCoordinate
  vendorPlatformDependence : PoliticalEconomyCoordinate
  labourSupportMaintenance : PoliticalEconomyCoordinate
  externalityAllocation : PoliticalEconomyCoordinate
  participantDecisionAuthority : PoliticalEconomyCoordinate
  recurrentFundingTCO : PoliticalEconomyCoordinate

politicalEconomyCoordinates : List PoliticalEconomyCoordinate
politicalEconomyCoordinates =
  ownershipProvisionForm
  ∷ profitRevenueModel
  ∷ accumulationGrowthPressure
  ∷ competitionCooperation
  ∷ intellectualPropertyLicensing
  ∷ procurementCapitalFinancing
  ∷ subsidyPublicFinancing
  ∷ vendorPlatformDependence
  ∷ labourSupportMaintenance
  ∷ externalityAllocation
  ∷ participantDecisionAuthority
  ∷ recurrentFundingTCO
  ∷ []

data ProvisioningRegime : Set where
  capitalistGrowthProvision : ProvisioningRegime
  publicProvision : ProvisioningRegime
  cooperativeCommonsProvision : ProvisioningRegime
  mixedProvision : ProvisioningRegime

data WasteMechanism : Set where
  accumulationExpansion : WasteMechanism
  competitiveTurnover : WasteMechanism
  externalisation : WasteMechanism
  perishableStockCompetition : WasteMechanism

data OutcomeKind : Set where measuredOutcome modelledOutcome : OutcomeKind

record WasteMechanismReceipt : Set where
  constructor waste-mechanism-receipt
  field
    regime : ProvisioningRegime
    mechanism : WasteMechanism
    materialOrServiceCarrier : String
    outcomeKind : OutcomeKind
    wasteOrThroughputOutcome : String
    sourceScope : String

open WasteMechanismReceipt public

correaniModelReceipt : WasteMechanismReceipt
correaniModelReceipt = waste-mechanism-receipt
  capitalistGrowthProvision
  perishableStockCompetition
  "differentiated perishable retail food in the source's oligopoly model"
  modelledOutcome
  "food waste generated endogenously in the model; individual retailer waste positively related to market concentration and quality under the model"
  "Correani et al. 2023 DOI 10.1016/j.jclepro.2023.137092; theoretical model only"

record BoundedWastePressureProposition : Set where
  constructor bounded-waste-pressure
  field
    receipt : WasteMechanismReceipt
    interpretation : String

correaniBoundedWastePressure : BoundedWastePressureProposition
correaniBoundedWastePressure = bounded-waste-pressure
  correaniModelReceipt
  "Within the source model, specified market-structure/strategic-interaction conditions can generate bounded food-waste pressure. This does not transport to all markets, all waste, all education systems or capitalism as a universal whole."

------------------------------------------------------------------------
-- Bare political-economy labels cannot manufacture the mechanism receipt.
------------------------------------------------------------------------

data CapitalismLabelCreatesWastePressure : Set where

capitalismLabelDoesNotCreateWastePressure : CapitalismLabelCreatesWastePressure → ⊥
capitalismLabelDoesNotCreateWastePressure ()

comparativeBoundary : Comparative.ComparativeInstitutionalMeaningBoundary
comparativeBoundary = Comparative.canonicalComparativeInstitutionalMeaningBoundary

canonicalIncidenceBoundary : Incidence.ExternalityIncidenceBoundary
canonicalIncidenceBoundary = Incidence.canonicalExternalityIncidenceBoundary

------------------------------------------------------------------------
-- Intersectionality is a mandatory challenge surface, not a side appendix.
------------------------------------------------------------------------

record PoliticalEconomyIntersectionalChallenge : Set where
  constructor political-economy-intersectional-challenge
  field
    disabilityBoundary : Disability.DisabilityDigitalESDBoundary
    absenceQuestionCount : Nat
    incidenceBoundary : Incidence.ExternalityIncidenceBoundary
    challengeReading : String

open PoliticalEconomyIntersectionalChallenge public

canonicalPoliticalEconomyIntersectionalChallenge : PoliticalEconomyIntersectionalChallenge
canonicalPoliticalEconomyIntersectionalChallenge = political-economy-intersectional-challenge
  Disability.canonicalDisabilityDigitalESDBoundary
  Absence.absenceAuditQuestionCount
  Incidence.canonicalExternalityIncidenceBoundary
  "Every political-economy claim must ask who is represented, who is missing, who benefits, who bears burden, who controls, who can exit, what disability/access costs are shifted, and whether disclosure or participation conditions hide affected groups."

record DigitalESDPoliticalEconomyBoundary : Set where
  constructor digital-esd-political-economy-boundary
  field
    politicalEconomyExplicitlyRepresented : Bool
    politicalEconomyExplicitlyRepresentedIsTrue : politicalEconomyExplicitlyRepresented ≡ true
    sourceMechanismAndRegimeRemainDistinct : Bool
    sourceMechanismAndRegimeRemainDistinctIsTrue : sourceMechanismAndRegimeRemainDistinct ≡ true
    bareCapitalismLabelCreatesWasteOutcome : Bool
    bareCapitalismLabelCreatesWasteOutcomeIsFalse : bareCapitalismLabelCreatesWasteOutcome ≡ false
    intersectionalChallengeRequired : Bool
    intersectionalChallengeRequiredIsTrue : intersectionalChallengeRequired ≡ true
    transcriptCreatesExternalEmpiricalAuthority : Bool
    transcriptCreatesExternalEmpiricalAuthorityIsFalse : transcriptCreatesExternalEmpiricalAuthority ≡ false

open DigitalESDPoliticalEconomyBoundary public

canonicalDigitalESDPoliticalEconomyBoundary : DigitalESDPoliticalEconomyBoundary
canonicalDigitalESDPoliticalEconomyBoundary = digital-esd-political-economy-boundary
  true refl
  true refl
  false refl
  true refl
  false refl

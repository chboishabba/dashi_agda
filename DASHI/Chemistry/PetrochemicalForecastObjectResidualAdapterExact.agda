module DASHI.Chemistry.PetrochemicalForecastObjectResidualAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ObjectDecompositionResidualRouterExact as Router
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Industry

------------------------------------------------------------------------
-- PETROCHEMICAL OBJECT-DECOMPOSITION ADAPTER FOR FORECAST RESEARCH
--
-- The existing IndustrialTransformationEdge is already the substantive
-- ontology.  This module merely exposes its coordinates to the generic
-- consumer-relative reverse-acquisition router.
------------------------------------------------------------------------

data PetrochemicalForecastConsumer : Set where
  explainProcessOutage
  explainSupplyConstraint
  explainProductLineage :
    PetrochemicalForecastConsumer

data PetrochemicalCoordinate
    (edge : Industry.IndustrialTransformationEdge) : Set where
  processCoordinate
  inputACoordinate
  inputBCoordinate
  outputCoordinate
  materialBalanceCoordinate
  operatingEnvelopeCoordinate
  separationCoordinate
  safetyCoordinate
  validationCoordinate :
    PetrochemicalCoordinate edge

PetrochemicalValue :
  (edge : Industry.IndustrialTransformationEdge) →
  PetrochemicalCoordinate edge →
  Set
PetrochemicalValue edge processCoordinate =
  Industry.IndustrialProcessKind
PetrochemicalValue edge inputACoordinate =
  Industry.MaterialFamily
PetrochemicalValue edge inputBCoordinate =
  Industry.MaterialFamily
PetrochemicalValue edge outputCoordinate =
  Industry.MaterialFamily
PetrochemicalValue edge materialBalanceCoordinate = String
PetrochemicalValue edge operatingEnvelopeCoordinate = String
PetrochemicalValue edge separationCoordinate = String
PetrochemicalValue edge safetyCoordinate = String
PetrochemicalValue edge validationCoordinate = String

coordinateStatus :
  (edge : Industry.IndustrialTransformationEdge) →
  PetrochemicalCoordinate edge →
  Router.CoordinateStatus
coordinateStatus edge processCoordinate = Router.paidCoordinate
coordinateStatus edge inputACoordinate = Router.paidCoordinate
coordinateStatus edge inputBCoordinate = Router.paidCoordinate
coordinateStatus edge outputCoordinate = Router.paidCoordinate
coordinateStatus edge materialBalanceCoordinate = Router.partialCoordinate
coordinateStatus edge operatingEnvelopeCoordinate = Router.partialCoordinate
coordinateStatus edge separationCoordinate = Router.partialCoordinate
coordinateStatus edge safetyCoordinate = Router.partialCoordinate
coordinateStatus edge validationCoordinate = Router.partialCoordinate

data RequiredBy :
  (consumer : PetrochemicalForecastConsumer) →
  (edge : Industry.IndustrialTransformationEdge) →
  PetrochemicalCoordinate edge →
  Set where

  outageNeedsProcess :
    ∀ {edge} →
    RequiredBy explainProcessOutage edge processCoordinate
  outageNeedsOperatingEnvelope :
    ∀ {edge} →
    RequiredBy explainProcessOutage edge operatingEnvelopeCoordinate
  outageNeedsSeparation :
    ∀ {edge} →
    RequiredBy explainProcessOutage edge separationCoordinate
  outageNeedsSafety :
    ∀ {edge} →
    RequiredBy explainProcessOutage edge safetyCoordinate
  outageNeedsValidation :
    ∀ {edge} →
    RequiredBy explainProcessOutage edge validationCoordinate

  supplyNeedsInputA :
    ∀ {edge} →
    RequiredBy explainSupplyConstraint edge inputACoordinate
  supplyNeedsInputB :
    ∀ {edge} →
    RequiredBy explainSupplyConstraint edge inputBCoordinate
  supplyNeedsProcess :
    ∀ {edge} →
    RequiredBy explainSupplyConstraint edge processCoordinate
  supplyNeedsOutput :
    ∀ {edge} →
    RequiredBy explainSupplyConstraint edge outputCoordinate
  supplyNeedsOperatingEnvelope :
    ∀ {edge} →
    RequiredBy explainSupplyConstraint edge operatingEnvelopeCoordinate

  lineageNeedsInputA :
    ∀ {edge} →
    RequiredBy explainProductLineage edge inputACoordinate
  lineageNeedsInputB :
    ∀ {edge} →
    RequiredBy explainProductLineage edge inputBCoordinate
  lineageNeedsProcess :
    ∀ {edge} →
    RequiredBy explainProductLineage edge processCoordinate
  lineageNeedsOutput :
    ∀ {edge} →
    RequiredBy explainProductLineage edge outputCoordinate
  lineageNeedsMaterialBalance :
    ∀ {edge} →
    RequiredBy explainProductLineage edge materialBalanceCoordinate

ownerReference :
  (edge : Industry.IndustrialTransformationEdge) →
  PetrochemicalCoordinate edge →
  String
ownerReference edge coordinate =
  "DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact.IndustrialTransformationEdge"

reverseReference :
  PetrochemicalForecastConsumer →
  (edge : Industry.IndustrialTransformationEdge) →
  PetrochemicalCoordinate edge →
  String
reverseReference explainProcessOutage edge processCoordinate =
  "process kind is already paid by the edge"
reverseReference explainProcessOutage edge operatingEnvelopeCoordinate =
  Industry.operatingEnvelopeReference edge
reverseReference explainProcessOutage edge separationCoordinate =
  Industry.separationPurificationReference edge
reverseReference explainProcessOutage edge safetyCoordinate =
  Industry.safetyReference edge
reverseReference explainProcessOutage edge validationCoordinate =
  Industry.validationReference edge
reverseReference explainSupplyConstraint edge inputACoordinate =
  "input-A material identity is already paid by the edge"
reverseReference explainSupplyConstraint edge inputBCoordinate =
  "input-B material identity is already paid by the edge"
reverseReference explainSupplyConstraint edge processCoordinate =
  "process kind is already paid by the edge"
reverseReference explainSupplyConstraint edge outputCoordinate =
  "output material identity is already paid by the edge"
reverseReference explainSupplyConstraint edge operatingEnvelopeCoordinate =
  Industry.operatingEnvelopeReference edge
reverseReference explainProductLineage edge inputACoordinate =
  "input-A material identity is already paid by the edge"
reverseReference explainProductLineage edge inputBCoordinate =
  "input-B material identity is already paid by the edge"
reverseReference explainProductLineage edge processCoordinate =
  "process kind is already paid by the edge"
reverseReference explainProductLineage edge outputCoordinate =
  "output material identity is already paid by the edge"
reverseReference explainProductLineage edge materialBalanceCoordinate =
  Industry.stoichiometryOrMaterialBalanceReference edge

petrochemicalForecastDecomposition :
  Router.ObjectDecompositionSystem
    Industry.IndustrialTransformationEdge
    PetrochemicalForecastConsumer
petrochemicalForecastDecomposition =
  Router.object-decomposition-system
    PetrochemicalCoordinate
    PetrochemicalValue
    coordinateStatus
    RequiredBy
    ownerReference
    reverseReference

------------------------------------------------------------------------
-- Concrete residual: the canonical steam-cracking edge already identifies the
-- process and material family, but its plant-specific operating envelope is an
-- explicit application debt.  That is exactly the reverse-search coordinate
-- needed by an outage/supply forecast consumer.
------------------------------------------------------------------------

steamCrackingOperatingEnvelopeResidual :
  Router.ConsumerRelevantObjectResidual
    petrochemicalForecastDecomposition
steamCrackingOperatingEnvelopeResidual =
  Router.consumer-relevant-object-residual
    explainProcessOutage
    Industry.hydrocarbonToEthylene
    operatingEnvelopeCoordinate
    outageNeedsOperatingEnvelope
    Router.partialCoordinate
    refl
    (ownerReference Industry.hydrocarbonToEthylene operatingEnvelopeCoordinate)
    (reverseReference
      explainProcessOutage
      Industry.hydrocarbonToEthylene
      operatingEnvelopeCoordinate)
    "plant operating envelope can change outage/restart interpretation"

------------------------------------------------------------------------
-- Boundary: process/material identity does not silently pay plant state.
------------------------------------------------------------------------

record PetrochemicalForecastAdapterBoundary : Set where
  constructor petrochemical-forecast-adapter-boundary
  field
    industrialOntologyReused : Bool
    processAndMaterialIdentityPaid : Bool
    plantSpecificOperatingEnvelopeAutomaticallyPaid : Bool
    plantSpecificOperatingEnvelopeAutomaticallyPaidIsFalse :
      plantSpecificOperatingEnvelopeAutomaticallyPaid ≡ false
    partialCoordinateCanBecomeReverseSearchTarget : Bool

canonicalPetrochemicalForecastAdapterBoundary :
  PetrochemicalForecastAdapterBoundary
canonicalPetrochemicalForecastAdapterBoundary =
  petrochemical-forecast-adapter-boundary
    true
    true
    false refl
    true

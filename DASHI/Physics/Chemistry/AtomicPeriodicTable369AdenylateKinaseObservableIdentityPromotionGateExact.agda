module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObservableIdentityPromotionGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseEndpointDLnAcquisitionExact as Endpoint
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- OBSERVABLE-IDENTITY PROMOTION GATE
--
-- A numeric value is not admitted merely because it uses the same symbol or
-- appears under the same DOI.  Promotion requires the claimed measurement to
-- preserve the observable identity actually paid by the source: article/source
-- identity, source locator, carrier/selection definition, measurement
-- construction, compatible units and a locator-specific numeric receipt.
--
-- This owner is a DASHI acquisition rule.  Li-Liu-Ji pay the concrete AdK CV
-- definitions and endpoint dLN values; they are not attributed with this generic
-- promotion policy.
------------------------------------------------------------------------

data ObservableIdentityRole : Set where
  exactPaidObservable : ObservableIdentityRole
  labelOnlyObservable : ObservableIdentityRole
  articleIdentityOnlyObservable : ObservableIdentityRole

record ObservablePromotionReceipt : Set where
  constructor observable-promotion-receipt
  field
    claimedLabel : String
    expectedDefinition : CV.CollectiveVariableDefinition
    sourceIdentityRetained : Bool
    sourceLocatorRetained : Bool
    carrierDefinitionRetained : Bool
    measurementConstructionRetained : Bool
    unitCompatibilityPaid : Bool
    locatorSpecificNumericReceiptPaid : Bool
    identityRole : ObservableIdentityRole
    numericPromotionAllowed : Bool
    interpretation : String
open ObservablePromotionReceipt public

------------------------------------------------------------------------
-- Positive same-object witness: the article-text open-endpoint dLN cell.
--
-- The value is paid in EndpointDLnAcquisitionExact, while the definition is
-- paid independently in CollectiveVariableDefinitionAcquisitionExact.  This
-- module only records that the two payments are compatible at the declared
-- acquisition interface.
------------------------------------------------------------------------

openEndpointDLnPromotionReceipt : ObservablePromotionReceipt
openEndpointDLnPromotionReceipt = observable-promotion-receipt
  "open endpoint dLN / 4AKE"
  CV.dLnDefinition
  true
  true
  true
  true
  true
  true
  exactPaidObservable
  true
  "same Li-Liu-Ji article; dLN center-of-mass observable definition retained; exact endpoint article-text locator retained; approximately 38 A remains approximate-source data rather than exact physical truth"

closedEndpointDLnPromotionReceipt : ObservablePromotionReceipt
closedEndpointDLnPromotionReceipt = observable-promotion-receipt
  "closed endpoint dLN / 1AKE"
  CV.dLnDefinition
  true
  true
  true
  true
  true
  true
  exactPaidObservable
  true
  "same Li-Liu-Ji article; dLN center-of-mass observable definition retained; exact endpoint article-text locator retained; approximately 20 A remains approximate-source data rather than exact physical truth"

openEndpointNumericDonor : Endpoint.EndpointDLnAcquisition
openEndpointNumericDonor = Endpoint.openEndpointDLnAcquisition

closedEndpointNumericDonor : Endpoint.EndpointDLnAcquisition
closedEndpointNumericDonor = Endpoint.closedEndpointDLnAcquisition

articleAttributionDonor : Attribution.AttributedSource
articleAttributionDonor = Attr.liLiuJiSource

------------------------------------------------------------------------
-- Negative fixtures.
--
-- These are repository-local counterexamples to unsafe promotion policies. They
-- do not assert that a particular external paper made these mistakes.
------------------------------------------------------------------------

sameLabelOnlyDLnPromotionAttempt : ObservablePromotionReceipt
sameLabelOnlyDLnPromotionAttempt = observable-promotion-receipt
  "dLN"
  CV.dLnDefinition
  false
  false
  false
  false
  false
  false
  labelOnlyObservable
  false
  "repository-local negative fixture: matching the string dLN alone does not identify the Li-Liu-Ji center-of-mass observable or pay a numeric cell"

articleIdentityOnlyPromotionAttempt : ObservablePromotionReceipt
articleIdentityOnlyPromotionAttempt = observable-promotion-receipt
  "unlocated Li-Liu-Ji dLN value"
  CV.dLnDefinition
  true
  false
  false
  false
  false
  false
  articleIdentityOnlyObservable
  false
  "repository-local negative fixture: DOI/PMID/PMCID/QID identity without retained observable definition and exact state/value locator cannot promote a numeric coordinate"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SameVariableLabelCreatesSameObservable : Set where
data SameArticleCreatesSameMeasurement : Set where
data QidCreatesObservableIdentity : Set where
data PdbOrUniProtCreatesNumericMeasurement : Set where
data ObservableDefinitionCreatesNumericValue : Set where

sameVariableLabelDoesNotCreateSameObservable :
  SameVariableLabelCreatesSameObservable → ⊥
sameVariableLabelDoesNotCreateSameObservable ()

sameArticleDoesNotCreateSameMeasurement :
  SameArticleCreatesSameMeasurement → ⊥
sameArticleDoesNotCreateSameMeasurement ()

qidDoesNotCreateObservableIdentity :
  QidCreatesObservableIdentity → ⊥
qidDoesNotCreateObservableIdentity ()

pdbOrUniProtDoesNotCreateNumericMeasurement :
  PdbOrUniProtCreatesNumericMeasurement → ⊥
pdbOrUniProtDoesNotCreateNumericMeasurement ()

observableDefinitionDoesNotCreateNumericValue :
  ObservableDefinitionCreatesNumericValue → ⊥
observableDefinitionDoesNotCreateNumericValue ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKObservableIdentityPromotionBoundary : Set where
  constructor adk-observable-identity-promotion-boundary
  field
    observableDefinitionRequired : Bool
    sourceLocatorRequired : Bool
    carrierDefinitionRequired : Bool
    measurementConstructionRequired : Bool
    unitCompatibilityRequired : Bool
    locatorSpecificNumericReceiptRequired : Bool
    articleIdentityRetained : Bool
    endpointDLnPositiveWitnessPaid : Bool
    sameVariableLabelCreatesSameObservable : Bool
    sameArticleCreatesSameMeasurement : Bool
    qidCreatesObservableIdentity : Bool
    pdbOrUniProtCreatesNumericMeasurement : Bool
    observableDefinitionCreatesNumericValue : Bool
    nextResidual : String
open AdKObservableIdentityPromotionBoundary public

canonicalAdKObservableIdentityPromotionBoundary :
  AdKObservableIdentityPromotionBoundary
canonicalAdKObservableIdentityPromotionBoundary =
  adk-observable-identity-promotion-boundary
    true true true true true true true true
    false false false false false
    "apply this gate to every future cross-paper or supplement calibration cell; matching theta1/theta2/dLN labels are insufficient unless the underlying residue/domain center-of-mass construction and exact state/value locator are compatible. DOI/QID/PDB/UniProt remain provenance/identity coordinates, never numeric payment."

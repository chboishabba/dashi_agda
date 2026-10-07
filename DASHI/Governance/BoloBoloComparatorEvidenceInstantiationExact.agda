module DASHI.Governance.BoloBoloComparatorEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact as Atlas
import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Spokes
import DASHI.Governance.BoloBoloOWSSpokesRateShiftExact as SpokesShift
import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Polycentric
import DASHI.Governance.BoloBoloOrganizationalNetworkEvidenceExact as NetworkEvidence
import DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact as Frontier

record BoloComparatorEvidenceInstantiation : Set where
  constructor boloComparatorEvidenceInstantiation
  field
    comparatorCases : List Atlas.ComparatorEvidenceCase
    comparatorBoundary : Atlas.ComparatorEvidenceBoundary
    owsScaleShock : Spokes.OWSScaleShockContext
    owsSpokesWindow : Spokes.InterruptedTransitionWindow
    owsSpokesMechanisms : Spokes.SpokesMechanismObservations
    owsSpokesBoundary : Spokes.OWSSpokesTransitionBoundary
    owsSpokesRateShiftRows : List SpokesShift.RateShiftRow
    owsSpokesRateShiftBoundary : SpokesShift.RateShiftBoundary
    polycentricSynthesis : Polycentric.PolycentricEvidenceSynthesis
    organizationalNetworkBoundary : NetworkEvidence.OrganizationalNetworkEvidenceBoundary
    structuralCoordinates : Frontier.ComparatorStructuralCoordinates
    workloadCoordinates : Frontier.ComparatorWorkloadCoordinates
    primitiveFrontier : Frontier.PrimitiveCalibrationFrontier
    acquisitionRoadmap : Frontier.ComparatorAcquisitionRoadmap
    calibrationBoundary : Frontier.ComparatorCalibrationBoundary

open BoloComparatorEvidenceInstantiation public

canonicalBoloComparatorEvidenceInstantiation : BoloComparatorEvidenceInstantiation
canonicalBoloComparatorEvidenceInstantiation = record
  { comparatorCases = Atlas.canonicalComparatorEvidenceCases
  ; comparatorBoundary = Atlas.canonicalComparatorEvidenceBoundary
  ; owsScaleShock = Spokes.canonicalOWSScaleShockContext
  ; owsSpokesWindow = Spokes.canonicalTransitionWindow
  ; owsSpokesMechanisms = Spokes.canonicalSpokesMechanismObservations
  ; owsSpokesBoundary = Spokes.canonicalOWSSpokesTransitionBoundary
  ; owsSpokesRateShiftRows = SpokesShift.canonicalRateShiftRows
  ; owsSpokesRateShiftBoundary = SpokesShift.canonicalRateShiftBoundary
  ; polycentricSynthesis = Polycentric.canonicalPolycentricEvidenceSynthesis
  ; organizationalNetworkBoundary = NetworkEvidence.canonicalOrganizationalNetworkEvidenceBoundary
  ; structuralCoordinates = Frontier.canonicalComparatorStructuralCoordinates
  ; workloadCoordinates = Frontier.canonicalComparatorWorkloadCoordinates
  ; primitiveFrontier = Frontier.canonicalPrimitiveCalibrationFrontier
  ; acquisitionRoadmap = Frontier.canonicalComparatorAcquisitionRoadmap
  ; calibrationBoundary = Frontier.canonicalComparatorCalibrationBoundary
  }

record ComparatorEvidenceInstantiationBoundary : Set where
  constructor comparatorEvidenceInstantiationBoundary
  field
    independentComparatorProvenancePreserved : Bool
    owsScaleShockContextPaid : Bool
    sameContextOWSStructuralTransitionPaid : Bool
    mixedSpokesMechanismEvidencePaid : Bool
    normalizedSpokesTransitionCheckPaid : Bool
    crossDomainPolycentricComparativeEvidencePaid : Bool
    taskContingentNetworkEvidencePaid : Bool
    largeUrbanNestedParticipationComparatorPaid : Bool
    durableFederatedCooperativeComparatorPaid : Bool
    comparatorGovernanceCadenceCoordinatesPaid : Bool
    underlyingPrimarySpokesMinutesPaid : Bool
    targetQualifiedPrimitiveBoloCostBoundsPaid : Bool
    comparatorEvidenceAloneEstablishesBoloSuperiority : Bool

open ComparatorEvidenceInstantiationBoundary public

canonicalComparatorEvidenceInstantiationBoundary : ComparatorEvidenceInstantiationBoundary
canonicalComparatorEvidenceInstantiationBoundary =
  comparatorEvidenceInstantiationBoundary
    true true true true true true true true true true false false false

canonicalBoloComparatorEvidenceInstantiationReceipt : GenericReceipt.GenericReceipt
canonicalBoloComparatorEvidenceInstantiationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo comparator evidence instantiation capstone"
    "DASHI.Governance.BoloBoloComparatorEvidenceInstantiationExact"
    "canonicalBoloComparatorEvidenceInstantiation / canonicalComparatorEvidenceInstantiationBoundary"
    "assembles independently attributed comparator evidence for the reported OWS scale shock and GA-to-Spokes transition, its normalized development-only lexical transition check, Porto Alegre nested participatory budgeting, Mondragon multi-level cooperative governance, comparative/systematic polycentric-governance evidence and task-contingent organizational-network experiments, including source-explicit scale and cadence coordinates"
    "the underlying November 2011 Spokes minutes remain unmaterialised and none of the comparator observations supplies a target-qualified primitive bolo cost/weight bound or political-superiority claim; comparator evidence constrains mechanism plausibility and admissible model design only until explicit transport or direct target measurement is paid"
    "agda -i . DASHI/Governance/BoloBoloComparatorEvidenceInstantiationRegression.agda"

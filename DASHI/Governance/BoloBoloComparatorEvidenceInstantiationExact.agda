module DASHI.Governance.BoloBoloComparatorEvidenceInstantiationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloComparatorEvidenceAtlasExact as Atlas
import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Spokes
import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Polycentric
import DASHI.Governance.BoloBoloComparatorCalibrationFrontierExact as Frontier

------------------------------------------------------------------------
-- COMPARATOR-EVIDENCE CAPSTONE.
--
-- Kept separate from the older Occupy evidence ledger because these sources
-- have independent provenance, domains and outcome definitions.  They inform
-- model-family plausibility and measurement design without becoming replicas
-- of OWS, p.m. or each other.
------------------------------------------------------------------------

record BoloComparatorEvidenceInstantiation : Set where
  constructor boloComparatorEvidenceInstantiation
  field
    comparatorCases : List Atlas.ComparatorEvidenceCase
    comparatorBoundary : Atlas.ComparatorEvidenceBoundary
    owsSpokesWindow : Spokes.InterruptedTransitionWindow
    owsSpokesMechanisms : Spokes.SpokesMechanismObservations
    owsSpokesBoundary : Spokes.OWSSpokesTransitionBoundary
    polycentricSynthesis : Polycentric.PolycentricEvidenceSynthesis
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
  ; owsSpokesWindow = Spokes.canonicalTransitionWindow
  ; owsSpokesMechanisms = Spokes.canonicalSpokesMechanismObservations
  ; owsSpokesBoundary = Spokes.canonicalOWSSpokesTransitionBoundary
  ; polycentricSynthesis = Polycentric.canonicalPolycentricEvidenceSynthesis
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
    sameContextOWSStructuralTransitionPaid : Bool
    mixedSpokesMechanismEvidencePaid : Bool
    crossDomainPolycentricComparativeEvidencePaid : Bool
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
    true true true true true true true false false false

canonicalBoloComparatorEvidenceInstantiationReceipt : GenericReceipt.GenericReceipt
canonicalBoloComparatorEvidenceInstantiationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo comparator evidence instantiation capstone"
    "DASHI.Governance.BoloBoloComparatorEvidenceInstantiationExact"
    "canonicalBoloComparatorEvidenceInstantiation / canonicalComparatorEvidenceInstantiationBoundary"
    "assembles independently attributed comparator evidence for the OWS GA-to-Spokes transition, Porto Alegre nested participatory budgeting, Mondragon multi-level cooperative governance and comparative/systematic polycentric-governance evidence, including source-explicit scale and cadence coordinates"
    "the underlying November 2011 Spokes minutes remain unmaterialised and none of the comparator observations supplies a target-qualified primitive bolo cost/weight bound or political-superiority claim; comparator evidence constrains mechanism plausibility and admissible model design only until explicit transport or direct target measurement is paid"
    "agda -i . DASHI/Governance/BoloBoloComparatorEvidenceInstantiationRegression.agda"

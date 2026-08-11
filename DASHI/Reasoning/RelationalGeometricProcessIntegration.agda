module DASHI.Reasoning.RelationalGeometricProcessIntegration where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Reasoning.RelationalProcessMemoryHyperfabric as Process
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Cobordism
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as Ternary

------------------------------------------------------------------------
-- Integration seam from process-bearing PNF memory to finite branch geometry.
--
-- The qualitative family remains the intake/narrative carrier.  A geometric
-- promotion requires explicit channels, path markers, attractor projections,
-- a ternary-geometry choice, and receipts.  No values are inferred from prose.
------------------------------------------------------------------------

record GeometricBranchMemory : Set where
  constructor geometricBranchMemory
  field
    processMemory : Process.BranchMemory
    geometricChannel : Cobordism.BranchChannel
    pathMarker : Cobordism.PersistentPathMarker
    coarseBoundaryRetained : Bool
    fineBoundaryRetained : Bool
    phaseRelationRetained : Bool
    capacityProvenanceRetained : Bool
    expiryAndClosureRetained : Bool
    geometricMemoryReceipt : String

record GeometricFamilyRefinement : Set where
  constructor geometricFamilyRefinement
  field
    processFamily : Process.BranchFamily
    quantitativeFamily : Process.QuantitativeFamilyRefinement
    branchingJunction : Cobordism.OneToNBranching
    attractorBranches : List Cobordism.AttractorBranch
    pathMarkers : List Cobordism.PersistentPathMarker
    ternaryGeometryChoice : Ternary.TernaryGeometryChoice
    splitResidual : Interference.BranchWave
    splitResidualExact :
      splitResidual
      ≡ Cobordism.splitRecombineResidual branchingJunction
    continuousAnglesEmpiricallyAvailable : Bool
    branchWeightsEmpiricallyCalibrated : Bool
    geometricFamilyReceipt : String

record PNFGeometryCompressionInvariant : Set where
  field
    preservesCoarseBoundary : Bool
    preservesLiveFineBoundaries : Bool
    preservesBlockedExpiredAndRejectedDistinctions : Bool
    preservesPathMarkersWhenTheyChangeInterference : Bool
    preservesReusableOverlapWhenItEnablesTransfer : Bool
    preservesCapacityAndDeadlineProvenance : Bool
    preservesSplitRecombineResidual : Bool
    doesNotInferContinuousAnglesFromTrits : Bool
    doesNotEquateJScaleLabelsWithModularJ : Bool

canonicalPNFGeometryCompressionInvariant :
  PNFGeometryCompressionInvariant
canonicalPNFGeometryCompressionInvariant = record
  { preservesCoarseBoundary = true
  ; preservesLiveFineBoundaries = true
  ; preservesBlockedExpiredAndRejectedDistinctions = true
  ; preservesPathMarkersWhenTheyChangeInterference = true
  ; preservesReusableOverlapWhenItEnablesTransfer = true
  ; preservesCapacityAndDeadlineProvenance = true
  ; preservesSplitRecombineResidual = true
  ; doesNotInferContinuousAnglesFromTrits = true
  ; doesNotEquateJScaleLabelsWithModularJ = true
  }

------------------------------------------------------------------------
-- Trauma-sensitive path transport remains defeasible and context indexed.
------------------------------------------------------------------------

record TraumaSensitivePathTransport : Set where
  constructor traumaSensitivePathTransport
  field
    priorDeformation : Process.TraumaDeformation
    transportedMarker : Cobordism.PersistentPathMarker
    currentContextEvidence : List String
    transportRemainsContextSensitive : Bool
    currentBranchAutomaticallyClassifiedUnsafe : Bool
    transportReceipt : String

record GeometryPromotionBoundary : Set where
  field
    proseCreatesBranchMetric : Bool
    endpointEqualityErasesPathDifference : Bool
    pathDifferenceAlwaysMeansTrauma : Bool
    strongMarkerAlwaysMeansCurrentDanger : Bool
    symmetricTernaryEqualsOrderedTernary : Bool
    finitePantsCarrierIsSmoothCobordism : Bool
    finitePhaseIsPhysicalQuantumPhase : Bool
    boundaryNote : String

canonicalGeometryPromotionBoundary : GeometryPromotionBoundary
canonicalGeometryPromotionBoundary = record
  { proseCreatesBranchMetric = false
  ; endpointEqualityErasesPathDifference = false
  ; pathDifferenceAlwaysMeansTrauma = false
  ; strongMarkerAlwaysMeansCurrentDanger = false
  ; symmetricTernaryEqualsOrderedTernary = false
  ; finitePantsCarrierIsSmoothCobordism = false
  ; finitePhaseIsPhysicalQuantumPhase = false
  ; boundaryNote =
      "Process memory may be refined by finite branch geometry only through explicit receipt-bearing channels and marker data. Path-sensitive memory can be adaptive or overtransported; the carrier itself neither diagnoses trauma nor infers current danger."
  }

module DASHI.Biology.Levin.FungalPolycomputationAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ObserverRelativePolycomputation as Poly
import DASHI.Biology.Levin.FungalElectrochemicalHydraulicCoupling as Coupling
import DASHI.Biology.Levin.MycelialTransportTopology as Topology

record FungalComputationReading : Set where
  field
    physicalEventsSpecified : Bool
    selectedObservableSpecified : Bool
    coarseGrainingSpecified : Bool
    inputEncodingSpecified : Bool
    outputDecodingSpecified : Bool
    repeatableOperationSpecified : Bool
    interventionSemanticsSpecified : Bool
    energeticAndGrowthSideEffectsAccounted : Bool

record FungalPolycomputationAdapter : Set where
  field
    observerRelativeBoundary : Poly.ObserverRelativePolycomputationBoundary
    couplingBoundary : Coupling.FungalElectrochemicalHydraulicBoundary
    topologyBoundary : Topology.MycelialTransportTopologyBoundary
    sameMyceliumMaySupportMultipleReadings : Bool
    logicGateReadingNotUniqueInternalSemantics : Bool
    experimenterEncodingNotFungalRepresentationByDefinition : Bool
    usefulPhysicalComputationStillAdmissible : Bool
    remodellingMayChangeComputedMap : Bool
    reproducibilityWindowMustBeSpecified : Bool
    interpretation : String

canonicalFungalPolycomputationAdapter : FungalPolycomputationAdapter
canonicalFungalPolycomputationAdapter = record
  { observerRelativeBoundary = Poly.canonicalObserverRelativePolycomputationBoundary
  ; couplingBoundary = Coupling.canonicalFungalElectrochemicalHydraulicBoundary
  ; topologyBoundary = Topology.canonicalMycelialTransportTopologyBoundary
  ; sameMyceliumMaySupportMultipleReadings = true
  ; logicGateReadingNotUniqueInternalSemantics = true
  ; experimenterEncodingNotFungalRepresentationByDefinition = true
  ; usefulPhysicalComputationStillAdmissible = true
  ; remodellingMayChangeComputedMap = true
  ; reproducibilityWindowMustBeSpecified = true
  ; interpretation = "A fungal substrate may realise useful analogue, reservoir or logic-level computations under an explicit observer-relative encoding, while its changing biological topology and side processes prevent identification of that reading with a unique internal fungal semantics"
  }

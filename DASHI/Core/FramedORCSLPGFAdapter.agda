module DASHI.Core.FramedORCSLPGFAdapter where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.ControlCardCore as Control
import DASHI.Foundations.CanonicalHalfFrameScaleValuation as CanonicalFrame
import DASHI.Foundations.RepresentationChartInvariant as Representation

------------------------------------------------------------------------
-- Explicit adapter from X/R/C/E/T/S/V to the repository control-card surface.
------------------------------------------------------------------------

data FramedCoordinate : Set where
  invariantX : FramedCoordinate
  representationR : FramedCoordinate
  chartC : FramedCoordinate
  evaluationE : FramedCoordinate
  transitionT : FramedCoordinate
  scaleS : FramedCoordinate
  valuationV : FramedCoordinate

coordinateSlot : FramedCoordinate → Control.ControlCardSlot
coordinateSlot invariantX = Control.surfaceSlot
coordinateSlot representationR = Control.lensSlot
coordinateSlot chartC = Control.orchestrationSlot
coordinateSlot evaluationE = Control.receiptSlot
coordinateSlot transitionT = Control.governanceSlot
coordinateSlot scaleS = Control.candidateSlot
coordinateSlot valuationV = Control.receiptSlot

data CarrierRegistryEntry : Set where
  genericRegisteredCarrier : CarrierRegistryEntry
  monsterFactorVec15Carrier : CarrierRegistryEntry
  primeLocalCarrier : CarrierRegistryEntry
  compositeJoinedChartCarrier : CarrierRegistryEntry

record FramedCoordinateControlRow : Set where
  field
    coordinate : FramedCoordinate
    slot : Control.ControlCardSlot
    slotMatches : slot ≡ coordinateSlot coordinate
    responsibility : String
    authorityPromoted : Bool

canonicalCoordinateRows : List FramedCoordinateControlRow
canonicalCoordinateRows =
  record
    { coordinate = invariantX
    ; slot = Control.surfaceSlot
    ; slotMatches = refl
    ; responsibility = "observed or candidate invariant payload"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = representationR
    ; slot = Control.lensSlot
    ; slotMatches = refl
    ; responsibility = "representation and formal-role lens"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = chartC
    ; slot = Control.orchestrationSlot
    ; slotMatches = refl
    ; responsibility = "registry-selected carrier/chart"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = evaluationE
    ; slot = Control.receiptSlot
    ; slotMatches = refl
    ; responsibility = "evaluation evidence and lineage receipt"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = transitionT
    ; slot = Control.governanceSlot
    ; slotMatches = refl
    ; responsibility = "target-correct, evaluation-preserving transition plus admissibility gate"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = scaleS
    ; slot = Control.candidateSlot
    ; slotMatches = refl
    ; responsibility = "scale, stage and scope candidate state"
    ; authorityPromoted = false
    }
  ∷ record
    { coordinate = valuationV
    ; slot = Control.receiptSlot
    ; slotMatches = refl
    ; responsibility = "valuation depth and resolution diagnostic"
    ; authorityPromoted = false
    }
  ∷ []

framedDynamicRow : Control.ControlCardRow
framedDynamicRow =
  Control.mkControlCardRow
    "framed-logistic-adic-stage-adapter"
    "DASHI.Core.FramedORCSLPGFAdapter"
    "X/R/C/E/T/S/V -> control-card envelope"
    Control.governanceSlot
    "The rational logistic carrier, p-adic/residue charts and Stage interpretation are separate surfaces joined only by proof-carrying and candidate-only bridges."
    "Real-analysis, p-adic analytic, empirical stage-lens and Monster-origin obligations remain independently gated."

framedDynamicRowReceipt :
  Control.ControlCardRowReceipt framedDynamicRow
framedDynamicRowReceipt =
  Control.controlCardRowReceipt
    refl refl refl refl refl refl
    refl refl refl refl refl

record FramedORCSLPGFAdapter : Set₁ where
  field
    CoordinateValue : Set
    coordinateRows : List FramedCoordinateControlRow
    selectedCarrier : CarrierRegistryEntry
    monsterSpecificCarrierRequiresAdmission : Bool
    frameObject :
      Representation.FramedScaleValuationObject
        Representation.RatioRepresentation
        CanonicalFrame.ChartedHalfRepresentation
        Representation.PresentationChart
        Nat
        Nat
    controlRow : Control.ControlCardRow
    controlReceipt : Control.ControlCardRowReceipt controlRow
    interpretationBridge : Bridge.BridgeRequirementRow
    interpretationBridgeReceipt :
      Bridge.BridgeRequirementRowReceipt interpretationBridge
    transitionCannotBypassGovernance : Bool
    promotedByAdapter : Bool

canonicalFramedORCSLPGFAdapter : FramedORCSLPGFAdapter
canonicalFramedORCSLPGFAdapter = record
  { CoordinateValue = Representation.RatioRepresentation
  ; coordinateRows = canonicalCoordinateRows
  ; selectedCarrier = genericRegisteredCarrier
  ; monsterSpecificCarrierRequiresAdmission = true
  ; frameObject = CanonicalFrame.canonicalHalfFrameScaleValuation
  ; controlRow = framedDynamicRow
  ; controlReceipt = framedDynamicRowReceipt
  ; interpretationBridge =
      Bridge.canonicalBridgeRequirementRow
        "finite residue orbit"
        "domain-qualified Stage interpretation"
        Bridge.bridgeSuppliedCandidateOnly
        true
        true
        true
  ; interpretationBridgeReceipt =
      Bridge.bridgeRequirementRowReceipt refl refl refl
  ; transitionCannotBypassGovernance = true
  ; promotedByAdapter = false
  }

record MonsterCarrierAdmission : Set where
  field
    requestedCarrier : CarrierRegistryEntry
    requestedCarrierIsFactorVec15 :
      requestedCarrier ≡ monsterFactorVec15Carrier
    domainSpecificConsumer : Bool
    carrierReceiptSupplied : Bool
    promotionAuthorityGranted : Bool

canonicalMonsterCarrierAdmissionCandidate : MonsterCarrierAdmission
canonicalMonsterCarrierAdmissionCandidate = record
  { requestedCarrier = monsterFactorVec15Carrier
  ; requestedCarrierIsFactorVec15 = refl
  ; domainSpecificConsumer = true
  ; carrierReceiptSupplied = true
  ; promotionAuthorityGranted = false
  }

record FramedORCSLPGFAuthorityBoundary : Set where
  field
    genericFrameSecretlyMonsterSpecific : Bool
    monsterCarrierAvailableByExplicitAdmission : Bool
    valuationAutomaticallyPromotesStage : Bool
    chartTransitionAutomaticallyPromotesAuthority : Bool
    semanticBottomArrowCandidateOnly : Bool

canonicalFramedORCSLPGFAuthorityBoundary :
  FramedORCSLPGFAuthorityBoundary
canonicalFramedORCSLPGFAuthorityBoundary = record
  { genericFrameSecretlyMonsterSpecific = false
  ; monsterCarrierAvailableByExplicitAdmission = true
  ; valuationAutomaticallyPromotesStage = false
  ; chartTransitionAutomaticallyPromotesAuthority = false
  ; semanticBottomArrowCandidateOnly = true
  }

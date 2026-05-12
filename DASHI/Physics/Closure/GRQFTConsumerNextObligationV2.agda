module DASHI.Physics.Closure.GRQFTConsumerNextObligationV2 where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.GaugeGroupContract as Gauge
import DASHI.Physics.Bridge as Bridge
import DASHI.Physics.ClosureGlue as Glue
import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5
import DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem as GR
import DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem as QFT
import DASHI.Physics.GR as PhysGR

------------------------------------------------------------------------
-- W5/Lane 5 GR/QFT consumer scoping V2.
--
-- This is a typed diagnostic over the eight carrier fields already named by
-- GRQFTDownstreamConsumerFields.  It classifies current availability without
-- constructing downstreamConsumerFields, GRQFTClosurePromotionReceipt,
-- LimitedSMQFTGRPromotionPrerequisiteGate, or any GR/QFT closure claim.

data GRQFTEightConsumerField : Set where
  spacetimeCarrierField :
    GRQFTEightConsumerField
  stressEnergyCarrierField :
    GRQFTEightConsumerField
  curvatureCarrierField :
    GRQFTEightConsumerField
  einsteinEquationCarrierField :
    GRQFTEightConsumerField
  waveStateCarrierField :
    GRQFTEightConsumerField
  spinorCarrierField :
    GRQFTEightConsumerField
  gaugeRepresentationCarrierField :
    GRQFTEightConsumerField
  interactionClosureCarrierField :
    GRQFTEightConsumerField

data GRQFTConsumerFieldAvailability : Set where
  inhabitedNow :
    GRQFTConsumerFieldAvailability
  internallyAdapterable :
    GRQFTConsumerFieldAvailability
  externalGated :
    GRQFTConsumerFieldAvailability
  missingTheorem :
    GRQFTConsumerFieldAvailability

record GRQFTConsumerFieldScope : Set where
  field
    carrierField :
      GRQFTEightConsumerField

    availability :
      GRQFTConsumerFieldAvailability

    currentSource :
      String

    requiredNext :
      String

    promotionBoundary :
      String

record GRQFTConsumerEightFieldScopeReceipt : Setω where
  field
    currentW5Status :
      W5.GRQFTConsumerNextObligationCurrentStatus

    currentGRBridge :
      GR.KnownLimitsGRBridgeTheorem

    currentQFTBridge :
      QFT.KnownLimitsQFTBridgeTheorem

    directWaveStateCarrier :
      Set

    eightFieldScopes :
      List GRQFTConsumerFieldScope

    downstreamFieldsRecordName :
      String

    closureReceiptName :
      String

    nonPromotionBoundary :
      List String

spacetimeCarrierScope :
  GRQFTConsumerFieldScope
spacetimeCarrierScope =
  record
    { carrierField =
        spacetimeCarrierField
    ; availability =
        internallyAdapterable
    ; currentSource =
        "KnownLimitsGRBridgeTheorem.canonicalKnownLimitsGRBridgeTheorem provides a GRAdapter/Lorentz bridge surface"
    ; requiredNext =
        "choose a downstream spacetimeCarrier adapter from the known-limits GR bridge without claiming full GR recovery"
    ; promotionBoundary =
        "adapterable carrier only; no Einstein equation law or GRQFTClosurePromotionReceipt follows"
    }

stressEnergyCarrierScope :
  GRQFTConsumerFieldScope
stressEnergyCarrierScope =
  record
    { carrierField =
        stressEnergyCarrierField
    ; availability =
        externalGated
    ; currentSource =
        "W4 matter/stress-energy surfaces are blocked on Candidate256 physical calibration, accepted DY/PDF adequacy, and W4 authority-backed matter"
    ; requiredNext =
        "supply W4 matter field and stress-energy tensor through accepted W4/W5 external authority before consuming this field"
    ; promotionBoundary =
        "no stress-energy carrier is promoted from current W4 candidate or PDF diagnostics"
    }

curvatureCarrierScope :
  GRQFTConsumerFieldScope
curvatureCarrierScope =
  record
    { carrierField =
        curvatureCarrierField
    ; availability =
        internallyAdapterable
    ; currentSource =
        "known-limits GR bridge and discrete Einstein candidate surfaces provide a local curvature-facing adapter vocabulary"
    ; requiredNext =
        "bind the adapter vocabulary to a downstream curvatureCarrier and keep sourced/non-flat curvature obligations separate"
    ; promotionBoundary =
        "adapterable carrier only; no sourced curvature law or Einstein equation consumer is constructed"
    }

einsteinEquationCarrierScope :
  GRQFTConsumerFieldScope
einsteinEquationCarrierScope =
  record
    { carrierField =
        einsteinEquationCarrierField
    ; availability =
        missingTheorem
    ; currentSource =
        "EinsteinEquationCandidate records flat-vacuum/current obligation shape but not the sourced discrete Einstein equation law"
    ; requiredNext =
        "prove or receive a discrete Einstein equation law after W4 stress-energy is available"
    ; promotionBoundary =
        "no G_mu_nu = 8pi T_mu_nu consumer law is constructed here"
    }

waveStateCarrierScope :
  GRQFTConsumerFieldScope
waveStateCarrierScope =
  record
    { carrierField =
        waveStateCarrierField
    ; availability =
        inhabitedNow
    ; currentSource =
        "KnownLimitsQFTBridgeTheorem.physicalWaveState on canonicalKnownLimitsQFTBridgeTheorem"
    ; requiredNext =
        "thread the existing wave-state carrier into a downstream consumer only with the remaining GR/QFT fields and laws"
    ; promotionBoundary =
        "inhabited carrier alone does not construct qftInteractionLaw or empirical validation"
    }

spinorCarrierScope :
  GRQFTConsumerFieldScope
spinorCarrierScope =
  record
    { carrierField =
        spinorCarrierField
    ; availability =
        internallyAdapterable
    ; currentSource =
        "KnownLimitsQFTBridgeTheorem carries contraction-signature-to-spin/Dirac and Clifford/even-wave bridge surfaces"
    ; requiredNext =
        "select a downstream spinorCarrier and spinorRealizationMap from the known-limits QFT bridge path"
    ; promotionBoundary =
        "adapterable carrier only; no QFT interaction closure follows"
    }

gaugeRepresentationCarrierScope :
  GRQFTConsumerFieldScope
gaugeRepresentationCarrierScope =
  record
    { carrierField =
        gaugeRepresentationCarrierField
    ; availability =
        internallyAdapterable
    ; currentSource =
        "known-limits full matter/gauge recovery and abstract gauge-matter bundle surfaces provide gauge-representation vocabulary"
    ; requiredNext =
        "bind the gauge vocabulary to a downstream gaugeRepresentationCarrier and gaugeRepresentationMap"
    ; promotionBoundary =
        "adapterable carrier only; no SM/QFT interaction representation theorem is promoted"
    }

interactionClosureCarrierScope :
  GRQFTConsumerFieldScope
interactionClosureCarrierScope =
  record
    { carrierField =
        interactionClosureCarrierField
    ; availability =
        externalGated
    ; currentSource =
        "current W5 status still requires qftInteractionLaw, qftInteractionLawAtConsumer, PDF carrier prerequisite, and empirical GR/QFT validation"
    ; requiredNext =
        "supply an accepted interaction-closure consumer together with W5 PDF carrier authority and empirical validation"
    ; promotionBoundary =
        "no interaction closure carrier or qftInteractionLaw is constructed here"
    }

canonicalGRQFTConsumerEightFieldScopes :
  List GRQFTConsumerFieldScope
canonicalGRQFTConsumerEightFieldScopes =
  spacetimeCarrierScope
  ∷ stressEnergyCarrierScope
  ∷ curvatureCarrierScope
  ∷ einsteinEquationCarrierScope
  ∷ waveStateCarrierScope
  ∷ spinorCarrierScope
  ∷ gaugeRepresentationCarrierScope
  ∷ interactionClosureCarrierScope
  ∷ []

canonicalGRQFTConsumerEightFieldScopeReceipt :
  GRQFTConsumerEightFieldScopeReceipt
canonicalGRQFTConsumerEightFieldScopeReceipt =
  record
    { currentW5Status =
        W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; currentGRBridge =
        GR.canonicalKnownLimitsGRBridgeTheorem
    ; currentQFTBridge =
        QFT.canonicalKnownLimitsQFTBridgeTheorem
    ; directWaveStateCarrier =
        QFT.KnownLimitsQFTBridgeTheorem.physicalWaveState
          QFT.canonicalKnownLimitsQFTBridgeTheorem
    ; eightFieldScopes =
        canonicalGRQFTConsumerEightFieldScopes
    ; downstreamFieldsRecordName =
        "DASHI.Physics.Closure.GRQFTConsumerNextObligation.GRQFTDownstreamConsumerFields"
    ; closureReceiptName =
        "DASHI.Physics.Closure.GRQFTConsumerNextObligation.GRQFTClosurePromotionReceipt"
    ; nonPromotionBoundary =
        "This V2 receipt classifies the eight downstream consumer carrier fields only"
        ∷ "It does not construct GRQFTDownstreamConsumerFields"
        ∷ "It does not construct GRQFTClosurePromotionAuthorityToken"
        ∷ "It does not construct GRQFTClosurePromotionReceipt"
        ∷ "It does not prove grEquationLaw, qftInteractionLaw, consumer witnesses, or empirical GR/QFT validation"
        ∷ "It makes no full SM, GR, QFT, GR/QFT, limited-promotion, or unification claim"
        ∷ []
    }

------------------------------------------------------------------------
-- Partial internally adaptable consumer receipt.
--
-- This receipt only inhabits the carrier fields that can be named from current
-- internal bridge surfaces.  It deliberately does not assemble
-- GRQFTDownstreamConsumerFields, because that record also requires
-- stress-energy, curvature/Einstein, interaction closure, and consumer laws.

knownLimitsSpacetimeCarrier : Set
knownLimitsSpacetimeCarrier =
  Glue.ClosureAxioms.S
    (Bridge.BridgeSurface.A
      (PhysGR.GRAdapter.bridge
        (GR.KnownLimitsGRBridgeTheorem.grAdapter
          GR.canonicalKnownLimitsGRBridgeTheorem)))

knownLimitsWaveStateCarrier : Set
knownLimitsWaveStateCarrier =
  QFT.KnownLimitsQFTBridgeTheorem.physicalWaveState
    QFT.canonicalKnownLimitsQFTBridgeTheorem

knownLimitsSpinorCarrier : Set
knownLimitsSpinorCarrier =
  knownLimitsWaveStateCarrier

knownLimitsGaugeRepresentationCarrier : Set
knownLimitsGaugeRepresentationCarrier =
  Gauge.Gauge

knownLimitsSpinorRealizationMap :
  knownLimitsWaveStateCarrier →
  knownLimitsSpinorCarrier
knownLimitsSpinorRealizationMap x = x

knownLimitsGaugeRepresentationMap :
  knownLimitsSpinorCarrier →
  knownLimitsGaugeRepresentationCarrier
knownLimitsGaugeRepresentationMap _ = Gauge.SU3×SU2×U1

data GRQFTPartialExternalGate : Set where
  stressEnergyExternalGate :
    GRQFTPartialExternalGate
  curvatureLawExternalGate :
    GRQFTPartialExternalGate
  einsteinEquationLawExternalGate :
    GRQFTPartialExternalGate
  interactionClosureExternalGate :
    GRQFTPartialExternalGate
  empiricalValidationExternalGate :
    GRQFTPartialExternalGate
  promotionAuthorityExternalGate :
    GRQFTPartialExternalGate

record GRQFTPartialConsumerReceipt : Setω where
  field
    grBridge :
      GR.KnownLimitsGRBridgeTheorem

    qftBridge :
      QFT.KnownLimitsQFTBridgeTheorem

    spacetimeCarrier :
      Set

    waveStateCarrier :
      Set

    spinorCarrier :
      Set

    gaugeRepresentationCarrier :
      Set

    spinorRealizationMap :
      waveStateCarrier →
      spinorCarrier

    gaugeRepresentationMap :
      spinorCarrier →
      gaugeRepresentationCarrier

    externalGates :
      List GRQFTPartialExternalGate

    adapterBoundary :
      List String

    nonPromotionBoundary :
      List String

canonicalGRQFTPartialConsumerReceipt :
  GRQFTPartialConsumerReceipt
canonicalGRQFTPartialConsumerReceipt =
  record
    { grBridge =
        GR.canonicalKnownLimitsGRBridgeTheorem
    ; qftBridge =
        QFT.canonicalKnownLimitsQFTBridgeTheorem
    ; spacetimeCarrier =
        knownLimitsSpacetimeCarrier
    ; waveStateCarrier =
        knownLimitsWaveStateCarrier
    ; spinorCarrier =
        knownLimitsSpinorCarrier
    ; gaugeRepresentationCarrier =
        knownLimitsGaugeRepresentationCarrier
    ; spinorRealizationMap =
        knownLimitsSpinorRealizationMap
    ; gaugeRepresentationMap =
        knownLimitsGaugeRepresentationMap
    ; externalGates =
        stressEnergyExternalGate
        ∷ curvatureLawExternalGate
        ∷ einsteinEquationLawExternalGate
        ∷ interactionClosureExternalGate
        ∷ empiricalValidationExternalGate
        ∷ promotionAuthorityExternalGate
        ∷ []
    ; adapterBoundary =
        "spacetimeCarrier is adapted from the canonical KnownLimitsGRBridgeTheorem GRAdapter bridge carrier"
        ∷ "waveStateCarrier is the physicalWaveState carrier already exposed by KnownLimitsQFTBridgeTheorem"
        ∷ "spinorCarrier is an internal adapter carrier over the known-limits wave state; this is not a Dirac equation solution space"
        ∷ "gaugeRepresentationCarrier is the internal Gauge contract carrier with canonical SU3xSU2xU1 projection"
        ∷ []
    ; nonPromotionBoundary =
        "This partial receipt inhabits only internally adaptable carrier fields"
        ∷ "It does not construct GRQFTDownstreamConsumerFields"
        ∷ "It does not construct GRQFTClosurePromotionReceipt or GRQFTClosurePromotionAuthorityToken"
        ∷ "Stress-energy remains external-gated through the W4/Lane 5 matter/stress-energy path"
        ∷ "Curvature and Einstein-equation consumers remain external-gated until a sourced curvature and discrete Einstein law are supplied"
        ∷ "QFT interaction closure and empirical GR/QFT validation remain external-gated"
        ∷ "No full GR/QFT closure, limited SM+GR promotion, or unification claim is made"
        ∷ []
    }

grqftClosurePromotionAuthorityUnavailable :
  W5.GRQFTClosurePromotionAuthorityToken →
  ⊥
grqftClosurePromotionAuthorityUnavailable ()

grqftClosurePromotionReceiptImpossibleHere :
  W5.GRQFTClosurePromotionReceipt →
  ⊥
grqftClosurePromotionReceiptImpossibleHere receipt =
  grqftClosurePromotionAuthorityUnavailable
    (W5.GRQFTClosurePromotionReceipt.promotionAuthority receipt)

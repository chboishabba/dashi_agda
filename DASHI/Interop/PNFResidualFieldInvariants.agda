module DASHI.Interop.PNFResidualFieldInvariants where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Interop.PNFSpectralFieldCore as Core
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.PNFResidualSpectralSeverityReceipt as SeverityReceipt
import DASHI.Interop.SensibLawResidualLattice as Residual
import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- Residual field invariant receipt surface.
--
-- This module packages checked invariants for PNF residual fields:
-- structural projection, same-fibre comparability, explicit bridge transport
-- exception handling, finite residual severity, contradiction monotonicity,
-- and vector/spectral non-authority gates.  It is a receipt surface only.

data PNFResidualFieldInvariantStatus : Set where
  residualFieldInvariants_checkedNoAuthorityPromotion :
    PNFResidualFieldInvariantStatus

data PNFResidualFieldInvariantComponent : Set where
  structuralProjectionComponent :
    PNFResidualFieldInvariantComponent

  sameFibreComparabilityComponent :
    PNFResidualFieldInvariantComponent

  explicitBridgeTransportExceptionComponent :
    PNFResidualFieldInvariantComponent

  fourLevelResidualSeverityComponent :
    PNFResidualFieldInvariantComponent

  severityMaxJoinComponent :
    PNFResidualFieldInvariantComponent

  contradictionMonotonicityComponent :
    PNFResidualFieldInvariantComponent

  visibleResidualSeverityComponent :
    PNFResidualFieldInvariantComponent

  residualCorroboratedProximityComponent :
    PNFResidualFieldInvariantComponent

  vectorSpectralNonAuthorityComponent :
    PNFResidualFieldInvariantComponent

canonicalPNFResidualFieldInvariantComponents :
  List PNFResidualFieldInvariantComponent
canonicalPNFResidualFieldInvariantComponents =
  structuralProjectionComponent
  ∷ sameFibreComparabilityComponent
  ∷ explicitBridgeTransportExceptionComponent
  ∷ fourLevelResidualSeverityComponent
  ∷ severityMaxJoinComponent
  ∷ contradictionMonotonicityComponent
  ∷ visibleResidualSeverityComponent
  ∷ residualCorroboratedProximityComponent
  ∷ vectorSpectralNonAuthorityComponent
  ∷ []

data PNFResidualFieldInvariantPromotion : Set where

pnfResidualFieldInvariantPromotionImpossible :
  PNFResidualFieldInvariantPromotion →
  ⊥
pnfResidualFieldInvariantPromotionImpossible ()

------------------------------------------------------------------------
-- Re-exported four-level names for the user-facing receipt row.

EXACT : Residual.ResidualLevel
EXACT = Residual.exact

PARTIAL : Residual.ResidualLevel
PARTIAL = Residual.partial

NO_TYPED_MEET : Residual.ResidualLevel
NO_TYPED_MEET = Residual.noTypedMeet

CONTRADICTION : Residual.ResidualLevel
CONTRADICTION = Residual.contradiction

residualSeverityScore :
  Residual.ResidualLevel →
  UFTC.Severity
residualSeverityScore =
  Residual.residualSeverity

severityMaxJoin :
  Residual.ResidualLevel →
  Residual.ResidualLevel →
  Residual.ResidualLevel
severityMaxJoin =
  Residual.joinResidual

severityMaxJoinScore :
  ∀ r s →
  residualSeverityScore (severityMaxJoin r s)
  ≡
  UFTC._⊔s_ (residualSeverityScore r) (residualSeverityScore s)
severityMaxJoinScore =
  Residual.residualJoinSeverity

exactSeverityScoreIsZero :
  residualSeverityScore EXACT ≡ 0
exactSeverityScoreIsZero =
  SeverityReceipt.exactSeverityIsZero

partialSeverityScoreIsOne :
  residualSeverityScore PARTIAL ≡ 1
partialSeverityScoreIsOne =
  SeverityReceipt.partialSeverityIsOne

noTypedMeetSeverityScoreIsThree :
  residualSeverityScore NO_TYPED_MEET ≡ 3
noTypedMeetSeverityScoreIsThree =
  SeverityReceipt.noTypedMeetSeverityIsThree

contradictionSeverityScoreIsNine :
  residualSeverityScore CONTRADICTION ≡ 9
contradictionSeverityScoreIsNine =
  SeverityReceipt.contradictionSeverityIsNine

contradictionIsSeverityTop :
  ∀ r →
  residualSeverityScore r ≤ residualSeverityScore CONTRADICTION
contradictionIsSeverityTop Residual.exact =
  z≤n
contradictionIsSeverityTop Residual.partial =
  s≤s z≤n
contradictionIsSeverityTop Residual.noTypedMeet =
  s≤s (s≤s (s≤s z≤n))
contradictionIsSeverityTop Residual.contradiction =
  s≤s
    (s≤s
      (s≤s
        (s≤s
          (s≤s
            (s≤s
              (s≤s
                (s≤s
                  (s≤s z≤n))))))))

joinWithContradictionRight :
  ∀ r →
  severityMaxJoin r CONTRADICTION ≡ CONTRADICTION
joinWithContradictionRight Residual.exact =
  refl
joinWithContradictionRight Residual.partial =
  refl
joinWithContradictionRight Residual.noTypedMeet =
  refl
joinWithContradictionRight Residual.contradiction =
  refl

joinWithContradictionLeft :
  ∀ r →
  severityMaxJoin CONTRADICTION r ≡ CONTRADICTION
joinWithContradictionLeft r =
  refl

------------------------------------------------------------------------
-- Structural projection and same-fibre comparability.

record StructuralProjectionInvariant : Set where
  constructor structuralProjectionInvariant
  field
    sourceReceipt :
      Residual.PNFEmissionReceipt

    objectRef :
      Core.PredicateObjectRef

    structuralBase :
      Core.PNFStructuralBase

    chamberProjection :
      Core.PNFChamberProjection

    coordinateProjection :
      Core.PNFCoordinateShape

    structuralBaseIsCanonical :
      structuralBase
      ≡
      Core.pnfStructuralBaseOf
        (Residual.PNFEmissionReceipt.emittedAtom sourceReceipt)

    chamberProjectionIsCanonical :
      chamberProjection
      ≡
      Core.pnfChamberProjectionOfReceipt objectRef sourceReceipt

    coordinateProjectionIsCanonical :
      coordinateProjection
      ≡
      Core.pnfCoordinateOfReceipt sourceReceipt

open StructuralProjectionInvariant public

structuralProjectionOfReceipt :
  Core.PredicateObjectRef →
  Residual.PNFEmissionReceipt →
  StructuralProjectionInvariant
structuralProjectionOfReceipt obj receipt =
  structuralProjectionInvariant
    receipt
    obj
    (Core.pnfStructuralBaseOf
      (Residual.PNFEmissionReceipt.emittedAtom receipt))
    (Core.pnfChamberProjectionOfReceipt obj receipt)
    (Core.pnfCoordinateOfReceipt receipt)
    refl
    refl
    refl

record SameFibreComparabilityInvariant : Set where
  constructor sameFibreComparabilityInvariant
  field
    leftReceipt :
      Residual.PNFEmissionReceipt

    rightReceipt :
      Residual.PNFEmissionReceipt

    fibre :
      Core.FibreRef

    leftObject :
      Core.ObjectInFibre

    rightObject :
      Core.ObjectInFibre

    comparableInsideFibre :
      Bool

    comparableInsideFibreIsTrue :
      comparableInsideFibre ≡ true

    residual :
      Residual.ResidualLevel

    residualIsReceiptResidual :
      residual ≡ Residual.receiptResidual leftReceipt rightReceipt

    residualSeverity :
      UFTC.Severity

    residualSeverityIsVisible :
      residualSeverity ≡ residualSeverityScore residual

open SameFibreComparabilityInvariant public

sameFibreComparabilityOfReceipts :
  Core.PredicateObjectRef →
  Core.PredicateObjectRef →
  Core.FibreRef →
  Residual.PNFEmissionReceipt →
  Residual.PNFEmissionReceipt →
  SameFibreComparabilityInvariant
sameFibreComparabilityOfReceipts leftObj rightObj fibre left right =
  sameFibreComparabilityInvariant
    left
    right
    fibre
    (Core.objectInFibreOfReceipt leftObj fibre left)
    (Core.objectInFibreOfReceipt rightObj fibre right)
    true
    refl
    (Residual.receiptResidual left right)
    refl
    (residualSeverityScore (Residual.receiptResidual left right))
    refl

data BridgeTransportMode : Set where
  sameFibreTransport :
    BridgeTransportMode

  explicitBridgeTransportException :
    BridgeTransportMode

bridgeTransportMayCrossFibre :
  BridgeTransportMode →
  Bool
bridgeTransportMayCrossFibre sameFibreTransport =
  false
bridgeTransportMayCrossFibre explicitBridgeTransportException =
  true

bridgeTransportAssertsSameFibreComparability :
  BridgeTransportMode →
  Bool
bridgeTransportAssertsSameFibreComparability sameFibreTransport =
  true
bridgeTransportAssertsSameFibreComparability explicitBridgeTransportException =
  false

explicitBridgeTransportExceptionMayCross :
  bridgeTransportMayCrossFibre explicitBridgeTransportException ≡ true
explicitBridgeTransportExceptionMayCross =
  refl

explicitBridgeTransportExceptionDoesNotCompare :
  bridgeTransportAssertsSameFibreComparability
    explicitBridgeTransportException
  ≡
  false
explicitBridgeTransportExceptionDoesNotCompare =
  refl

------------------------------------------------------------------------
-- Visible residual severity packaging.

record VisibleResidualSeverity : Set where
  constructor visibleResidualSeverity
  field
    residualLevel :
      Residual.ResidualLevel

    severityScore :
      UFTC.Severity

    severityScoreIsResidual :
      severityScore ≡ residualSeverityScore residualLevel

    signedResidualWeight :
      Graph.SignedResidualWeight

    signedResidualWeightIsCanonical :
      signedResidualWeight ≡ Graph.residualSignedWeight residualLevel

open VisibleResidualSeverity public

visibleResidualSeverityOf :
  Residual.ResidualLevel →
  VisibleResidualSeverity
visibleResidualSeverityOf residual =
  visibleResidualSeverity
    residual
    (residualSeverityScore residual)
    refl
    (Graph.residualSignedWeight residual)
    refl

visibleContradictionIsNegative :
  Graph.sign
    (signedResidualWeight (visibleResidualSeverityOf CONTRADICTION))
  ≡
  Graph.negativeResidualWeight
visibleContradictionIsNegative =
  refl

visibleJoinSeverityMax :
  ∀ r s →
  severityScore
    (visibleResidualSeverityOf (severityMaxJoin r s))
  ≡
  UFTC._⊔s_
    (severityScore (visibleResidualSeverityOf r))
    (severityScore (visibleResidualSeverityOf s))
visibleJoinSeverityMax =
  severityMaxJoinScore

------------------------------------------------------------------------
-- Vector and spectral non-authority gates.

data NonAuthorityCarrier : Set where
  textEmbeddingCarrier :
    NonAuthorityCarrier

  vectorProximityCarrier :
    NonAuthorityCarrier

  spectralCoordinateCarrier :
    NonAuthorityCarrier

  signedLaplacianCarrier :
    NonAuthorityCarrier

vectorOrSpectralPromotesTruth :
  NonAuthorityCarrier →
  Bool
vectorOrSpectralPromotesTruth _ =
  false

vectorOrSpectralPromotesSupport :
  NonAuthorityCarrier →
  Bool
vectorOrSpectralPromotesSupport _ =
  false

vectorOrSpectralPromotesAdmissibility :
  NonAuthorityCarrier →
  Bool
vectorOrSpectralPromotesAdmissibility _ =
  false

vectorOrSpectralPromotesAuthority :
  NonAuthorityCarrier →
  Bool
vectorOrSpectralPromotesAuthority _ =
  false

vectorSpectralTruthGateIsFalse :
  ∀ carrier →
  vectorOrSpectralPromotesTruth carrier ≡ false
vectorSpectralTruthGateIsFalse carrier =
  refl

vectorSpectralSupportGateIsFalse :
  ∀ carrier →
  vectorOrSpectralPromotesSupport carrier ≡ false
vectorSpectralSupportGateIsFalse carrier =
  refl

vectorSpectralAdmissibilityGateIsFalse :
  ∀ carrier →
  vectorOrSpectralPromotesAdmissibility carrier ≡ false
vectorSpectralAdmissibilityGateIsFalse carrier =
  refl

vectorSpectralAuthorityGateIsFalse :
  ∀ carrier →
  vectorOrSpectralPromotesAuthority carrier ≡ false
vectorSpectralAuthorityGateIsFalse carrier =
  refl

------------------------------------------------------------------------
-- Residual-corroborated proximity product invariant.

residualCanCorroborateCompatibility :
  Residual.ResidualLevel →
  Bool
residualCanCorroborateCompatibility Residual.exact =
  true
residualCanCorroborateCompatibility Residual.partial =
  true
residualCanCorroborateCompatibility Residual.noTypedMeet =
  false
residualCanCorroborateCompatibility Residual.contradiction =
  false

proximityCanRecordCorroboratedCandidate :
  Bool →
  Residual.ResidualLevel →
  Bool
proximityCanRecordCorroboratedCandidate false _ =
  false
proximityCanRecordCorroboratedCandidate true residual =
  residualCanCorroborateCompatibility residual

residualGraphEdgeKind :
  Residual.ResidualLevel →
  Graph.PNFGraphEdgeKind
residualGraphEdgeKind Residual.exact =
  Graph.exactResidualEdge
residualGraphEdgeKind Residual.partial =
  Graph.partialResidualEdge
residualGraphEdgeKind Residual.noTypedMeet =
  Graph.noTypedMeetEdge
residualGraphEdgeKind Residual.contradiction =
  Graph.contradictionEdge

residualGraphEdgeEvidence :
  (r : Residual.ResidualLevel) →
  Graph.PNFGraphEdgeEvidence (residualGraphEdgeKind r)
residualGraphEdgeEvidence Residual.exact =
  Graph.exactResidualEvidence
residualGraphEdgeEvidence Residual.partial =
  Graph.partialResidualEvidence
residualGraphEdgeEvidence Residual.noTypedMeet =
  Graph.noTypedMeetEvidence
residualGraphEdgeEvidence Residual.contradiction =
  Graph.contradictionEvidence

record ResidualCorroboratedProximity : Set where
  constructor residualCorroboratedProximity
  field
    proximityCandidate :
      Core.CandidateRef

    proximityFibre :
      Core.FibreRef

    proximityInsideFibre :
      Bool

    spectralRow :
      Graph.CheckedSpectralCoordinateRow

    proximityCarrier :
      NonAuthorityCarrier

    proximityResidualLevel :
      Residual.ResidualLevel

    residualCompatibility :
      Bool

    residualCompatibilityIsCanonical :
      residualCompatibility
      ≡
      residualCanCorroborateCompatibility proximityResidualLevel

    residualVisibleSeverity :
      VisibleResidualSeverity

    residualVisibleSeverityIsCanonical :
      residualVisibleSeverity ≡ visibleResidualSeverityOf proximityResidualLevel

    edgeKind :
      Graph.PNFGraphEdgeKind

    edgeKindIsResidual :
      edgeKind ≡ residualGraphEdgeKind proximityResidualLevel

    edgeEvidence :
      Graph.PNFGraphEdgeEvidence edgeKind

    candidateRecorded :
      Bool

    candidateRecordedIsCompatibilityConjunction :
      candidateRecorded
      ≡
      proximityCanRecordCorroboratedCandidate
        proximityInsideFibre
        proximityResidualLevel

    proximityPromotesTruth :
      Bool

    proximityPromotesTruthIsFalse :
      proximityPromotesTruth ≡ false

    proximityPromotesSupport :
      Bool

    proximityPromotesSupportIsFalse :
      proximityPromotesSupport ≡ false

    proximityPromotesAdmissibility :
      Bool

    proximityPromotesAdmissibilityIsFalse :
      proximityPromotesAdmissibility ≡ false

    proximityPromotesAuthority :
      Bool

    proximityPromotesAuthorityIsFalse :
      proximityPromotesAuthority ≡ false

open ResidualCorroboratedProximity public

residualCorroboratedProximityOf :
  Core.CandidateRef →
  Graph.PNFGraphVertex →
  Bool →
  Residual.ResidualLevel →
  ResidualCorroboratedProximity
residualCorroboratedProximityOf candidate vertex insideFibre residual =
  residualCorroboratedProximity
    candidate
    Core.fibreFallback
    insideFibre
    (Graph.canonicalCheckedSpectralCoordinateRow vertex)
    spectralCoordinateCarrier
    residual
    (residualCanCorroborateCompatibility residual)
    refl
    (visibleResidualSeverityOf residual)
    refl
    (residualGraphEdgeKind residual)
    refl
    (residualGraphEdgeEvidence residual)
    (proximityCanRecordCorroboratedCandidate insideFibre residual)
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalExactCorroboratedProximity :
  ResidualCorroboratedProximity
canonicalExactCorroboratedProximity =
  residualCorroboratedProximityOf
    Core.candidateFallback
    (Graph.pnfGraphVertex 0)
    true
    EXACT

canonicalPartialCorroboratedProximity :
  ResidualCorroboratedProximity
canonicalPartialCorroboratedProximity =
  residualCorroboratedProximityOf
    Core.candidateFallback
    (Graph.pnfGraphVertex 1)
    true
    PARTIAL

canonicalContradictionProximity :
  ResidualCorroboratedProximity
canonicalContradictionProximity =
  residualCorroboratedProximityOf
    Core.candidateFallback
    (Graph.pnfGraphVertex 2)
    true
    CONTRADICTION

canonicalNoTypedMeetProximity :
  ResidualCorroboratedProximity
canonicalNoTypedMeetProximity =
  residualCorroboratedProximityOf
    Core.candidateFallback
    (Graph.pnfGraphVertex 3)
    false
    NO_TYPED_MEET

canonicalExactProximityIsCorroboratedCompatibility :
  candidateRecorded canonicalExactCorroboratedProximity ≡ true
canonicalExactProximityIsCorroboratedCompatibility =
  refl

canonicalPartialProximityIsCorroboratedCompatibility :
  candidateRecorded canonicalPartialCorroboratedProximity ≡ true
canonicalPartialProximityIsCorroboratedCompatibility =
  refl

canonicalExactProximityIsInsideFibre :
  proximityInsideFibre canonicalExactCorroboratedProximity ≡ true
canonicalExactProximityIsInsideFibre =
  refl

canonicalPartialProximityIsInsideFibre :
  proximityInsideFibre canonicalPartialCorroboratedProximity ≡ true
canonicalPartialProximityIsInsideFibre =
  refl

canonicalContradictionDoesNotBecomeCorroboratedCompatibility :
  candidateRecorded canonicalContradictionProximity ≡ false
canonicalContradictionDoesNotBecomeCorroboratedCompatibility =
  refl

canonicalNoTypedMeetDoesNotBecomeCorroboratedCompatibility :
  candidateRecorded canonicalNoTypedMeetProximity ≡ false
canonicalNoTypedMeetDoesNotBecomeCorroboratedCompatibility =
  refl

canonicalNoTypedMeetProximityIsNotInsideFibre :
  proximityInsideFibre canonicalNoTypedMeetProximity ≡ false
canonicalNoTypedMeetProximityIsNotInsideFibre =
  refl

canonicalExactProximityTruthGateFalse :
  proximityPromotesTruth canonicalExactCorroboratedProximity ≡ false
canonicalExactProximityTruthGateFalse =
  refl

canonicalPartialProximitySupportGateFalse :
  proximityPromotesSupport canonicalPartialCorroboratedProximity ≡ false
canonicalPartialProximitySupportGateFalse =
  refl

canonicalPartialProximityAdmissibilityGateFalse :
  proximityPromotesAdmissibility canonicalPartialCorroboratedProximity
  ≡
  false
canonicalPartialProximityAdmissibilityGateFalse =
  refl

canonicalPartialProximityAuthorityGateFalse :
  proximityPromotesAuthority canonicalPartialCorroboratedProximity ≡ false
canonicalPartialProximityAuthorityGateFalse =
  refl

canonicalVectorProximityAloneAuthorityGateFalse :
  vectorOrSpectralPromotesAuthority vectorProximityCarrier ≡ false
canonicalVectorProximityAloneAuthorityGateFalse =
  refl

------------------------------------------------------------------------
-- Canonical example rows.

canonicalPredicate :
  Residual.PredicatePNF
canonicalPredicate =
  Residual.predicatePNF
    "canonical predicate"
    Residual.sig-agent-theme
    (Residual.opaqueArg "agent")
    (Residual.opaqueArg "theme")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "canonical-example"

canonicalPositiveReceipt :
  Residual.PNFEmissionReceipt
canonicalPositiveReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical positive source span"
    canonicalPredicate

canonicalNegatedPredicate :
  Residual.PredicatePNF
canonicalNegatedPredicate =
  Residual.predicatePNF
    "canonical predicate"
    Residual.sig-agent-theme
    (Residual.opaqueArg "agent")
    (Residual.opaqueArg "theme")
    Residual.absent
    Residual.negated
    Residual.directEvidence
    "canonical-example"

canonicalNegatedReceipt :
  Residual.PNFEmissionReceipt
canonicalNegatedReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical negated source span"
    canonicalNegatedPredicate

canonicalHedgedPredicate :
  Residual.PredicatePNF
canonicalHedgedPredicate =
  Residual.predicatePNF
    "canonical predicate"
    Residual.sig-agent-theme
    (Residual.opaqueArg "agent")
    (Residual.opaqueArg "theme")
    Residual.absent
    Residual.positive
    Residual.hedgedEvidence
    "canonical-example"

canonicalHedgedReceipt :
  Residual.PNFEmissionReceipt
canonicalHedgedReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical hedged source span"
    canonicalHedgedPredicate

canonicalCrossSignaturePredicate :
  Residual.PredicatePNF
canonicalCrossSignaturePredicate =
  Residual.predicatePNF
    "canonical predicate"
    Residual.sig-theme-only
    Residual.absent
    (Residual.opaqueArg "theme")
    Residual.absent
    Residual.positive
    Residual.directEvidence
    "canonical-example"

canonicalCrossSignatureReceipt :
  Residual.PNFEmissionReceipt
canonicalCrossSignatureReceipt =
  Residual.pnfEmissionReceipt
    "canonical-parser"
    "canonical-reducer"
    "canonical cross signature source span"
    canonicalCrossSignaturePredicate

record CanonicalResidualExampleRow : Set where
  constructor canonicalResidualExampleRow
  field
    exampleLabel :
      String

    exampleLeftReceipt :
      Residual.PNFEmissionReceipt

    exampleRightReceipt :
      Residual.PNFEmissionReceipt

    exampleResidual :
      Residual.ResidualLevel

    exampleResidualIsComputed :
      exampleResidual
      ≡
      Residual.receiptResidual exampleLeftReceipt exampleRightReceipt

    exampleVisibleSeverity :
      VisibleResidualSeverity

    exampleVisibleSeverityIsCanonical :
      exampleVisibleSeverity ≡ visibleResidualSeverityOf exampleResidual

    exampleSameFibreComparable :
      Bool

    exampleBridgeException :
      Bool

    exampleVectorTruthGate :
      Bool

    exampleSpectralAuthorityGate :
      Bool

open CanonicalResidualExampleRow public

canonicalExactRow :
  CanonicalResidualExampleRow
canonicalExactRow =
  canonicalResidualExampleRow
    "same fibre exact"
    canonicalPositiveReceipt
    canonicalPositiveReceipt
    EXACT
    refl
    (visibleResidualSeverityOf EXACT)
    refl
    true
    false
    false
    false

canonicalPartialRow :
  CanonicalResidualExampleRow
canonicalPartialRow =
  canonicalResidualExampleRow
    "same fibre partial"
    canonicalPositiveReceipt
    canonicalHedgedReceipt
    PARTIAL
    refl
    (visibleResidualSeverityOf PARTIAL)
    refl
    true
    false
    false
    false

canonicalContradictionRow :
  CanonicalResidualExampleRow
canonicalContradictionRow =
  canonicalResidualExampleRow
    "same fibre contradiction"
    canonicalPositiveReceipt
    canonicalNegatedReceipt
    CONTRADICTION
    refl
    (visibleResidualSeverityOf CONTRADICTION)
    refl
    true
    false
    false
    false

canonicalNoTypedMeetBridgeExceptionRow :
  CanonicalResidualExampleRow
canonicalNoTypedMeetBridgeExceptionRow =
  canonicalResidualExampleRow
    "cross fibre explicit bridge exception"
    canonicalPositiveReceipt
    canonicalCrossSignatureReceipt
    NO_TYPED_MEET
    refl
    (visibleResidualSeverityOf NO_TYPED_MEET)
    refl
    false
    true
    false
    false

canonicalRows :
  List CanonicalResidualExampleRow
canonicalRows =
  canonicalExactRow
  ∷ canonicalPartialRow
  ∷ canonicalContradictionRow
  ∷ canonicalNoTypedMeetBridgeExceptionRow
  ∷ []

canonicalExactRowSeverityIsZero :
  severityScore (exampleVisibleSeverity canonicalExactRow) ≡ 0
canonicalExactRowSeverityIsZero =
  refl

canonicalContradictionRowSeverityIsNine :
  severityScore (exampleVisibleSeverity canonicalContradictionRow) ≡ 9
canonicalContradictionRowSeverityIsNine =
  refl

canonicalPartialRowSeverityIsOne :
  severityScore (exampleVisibleSeverity canonicalPartialRow) ≡ 1
canonicalPartialRowSeverityIsOne =
  refl

canonicalBridgeExceptionRowResidualIsNoTypedMeet :
  exampleResidual canonicalNoTypedMeetBridgeExceptionRow ≡ NO_TYPED_MEET
canonicalBridgeExceptionRowResidualIsNoTypedMeet =
  refl

canonicalBridgeExceptionRowDoesNotAssertComparability :
  exampleSameFibreComparable canonicalNoTypedMeetBridgeExceptionRow ≡ false
canonicalBridgeExceptionRowDoesNotAssertComparability =
  refl

canonicalBridgeExceptionRowUsesException :
  exampleBridgeException canonicalNoTypedMeetBridgeExceptionRow ≡ true
canonicalBridgeExceptionRowUsesException =
  refl

canonicalRowsVectorTruthGateFalse :
  exampleVectorTruthGate canonicalExactRow
  ≡
  false
canonicalRowsVectorTruthGateFalse =
  refl

canonicalRowsSpectralAuthorityGateFalse :
  exampleSpectralAuthorityGate canonicalContradictionRow
  ≡
  false
canonicalRowsSpectralAuthorityGateFalse =
  refl

------------------------------------------------------------------------
-- End-to-end receipt.

pnfResidualFieldInvariantStatement :
  String
pnfResidualFieldInvariantStatement =
  "PNF residual field invariants expose structural projection, same-fibre comparability, explicit bridge transport exception, finite residual severity, severity-max join, visible residual severity, residual-corroborated proximity candidates, and false vector/spectral authority gates."

pnfResidualFieldInvariantBoundary :
  String
pnfResidualFieldInvariantBoundary =
  "Residual severity is visible bookkeeping over typed PNF receipts only. Vector proximity, spectral rows, signed Laplacians, and candidate status alone do not promote truth, support, admissibility, legal/policy/Wikidata authority, or cross-fibre comparability. Only EXACT/PARTIAL residuals inside a fibre can be recorded as corroborated compatibility; CONTRADICTION and NO_TYPED_MEET fail closed."

record PNFResidualFieldInvariantReceipt : Set where
  field
    status :
      PNFResidualFieldInvariantStatus

    statusIsCheckedNoAuthorityPromotion :
      status
      ≡
      residualFieldInvariants_checkedNoAuthorityPromotion

    components :
      List PNFResidualFieldInvariantComponent

    componentsAreCanonical :
      components ≡ canonicalPNFResidualFieldInvariantComponents

    severityReceipt :
      SeverityReceipt.PNFResidualSpectralSeverityReceipt

    severityReceiptIsCanonical :
      severityReceipt
      ≡
      SeverityReceipt.canonicalPNFResidualSpectralSeverityReceipt

    structuralProjection :
      StructuralProjectionInvariant

    structuralProjectionIsCanonical :
      structuralProjection
      ≡
      structuralProjectionOfReceipt
        Core.canonicalPredicateObjectRef
        canonicalPositiveReceipt

    sameFibreComparability :
      SameFibreComparabilityInvariant

    sameFibreComparabilityIsCanonical :
      sameFibreComparability
      ≡
      sameFibreComparabilityOfReceipts
        Core.canonicalPredicateObjectRef
        Core.canonicalPredicateObjectRef
        Core.fibreFallback
        canonicalPositiveReceipt
        canonicalNegatedReceipt

    levels :
      List Residual.ResidualLevel

    levelsAreCanonical :
      levels
      ≡
      EXACT ∷ PARTIAL ∷ NO_TYPED_MEET ∷ CONTRADICTION ∷ []

    exactScore :
      residualSeverityScore EXACT ≡ 0

    partialScore :
      residualSeverityScore PARTIAL ≡ 1

    noTypedMeetScore :
      residualSeverityScore NO_TYPED_MEET ≡ 3

    contradictionScore :
      residualSeverityScore CONTRADICTION ≡ 9

    joinIsSeverityMax :
      ∀ r s →
      residualSeverityScore (severityMaxJoin r s)
      ≡
      UFTC._⊔s_ (residualSeverityScore r) (residualSeverityScore s)

    contradictionMonotone :
      ∀ r →
      residualSeverityScore r ≤ residualSeverityScore CONTRADICTION

    contradictionJoinAbsorbsRight :
      ∀ r →
      severityMaxJoin r CONTRADICTION ≡ CONTRADICTION

    contradictionJoinAbsorbsLeft :
      ∀ r →
      severityMaxJoin CONTRADICTION r ≡ CONTRADICTION

    visibleContradiction :
      VisibleResidualSeverity

    visibleContradictionIsCanonical :
      visibleContradiction ≡ visibleResidualSeverityOf CONTRADICTION

    visibleContradictionSign :
      Graph.sign (signedResidualWeight visibleContradiction)
      ≡
      Graph.negativeResidualWeight

    explicitBridgeExceptionCrosses :
      bridgeTransportMayCrossFibre explicitBridgeTransportException ≡ true

    explicitBridgeExceptionDoesNotCompare :
      bridgeTransportAssertsSameFibreComparability
        explicitBridgeTransportException
      ≡
      false

    exampleRows :
      List CanonicalResidualExampleRow

    exampleRowsAreCanonical :
      exampleRows ≡ canonicalRows

    exactCorroboratedProximity :
      ResidualCorroboratedProximity

    exactCorroboratedProximityIsCanonical :
      exactCorroboratedProximity
      ≡
      canonicalExactCorroboratedProximity

    partialCorroboratedProximity :
      ResidualCorroboratedProximity

    partialCorroboratedProximityIsCanonical :
      partialCorroboratedProximity
      ≡
      canonicalPartialCorroboratedProximity

    exactCorroboratedProximityInsideFibre :
      proximityInsideFibre canonicalExactCorroboratedProximity ≡ true

    partialCorroboratedProximityInsideFibre :
      proximityInsideFibre canonicalPartialCorroboratedProximity ≡ true

    contradictionDoesNotCorroborateCompatibility :
      candidateRecorded canonicalContradictionProximity ≡ false

    noTypedMeetDoesNotCorroborateCompatibility :
      candidateRecorded canonicalNoTypedMeetProximity ≡ false

    noTypedMeetCorroboratedProximityOutsideFibre :
      proximityInsideFibre canonicalNoTypedMeetProximity ≡ false

    corroboratedCandidateTruthGate :
      proximityPromotesTruth canonicalExactCorroboratedProximity ≡ false

    corroboratedCandidateSupportGate :
      proximityPromotesSupport canonicalPartialCorroboratedProximity ≡ false

    corroboratedCandidateAdmissibilityGate :
      proximityPromotesAdmissibility canonicalPartialCorroboratedProximity
      ≡
      false

    corroboratedCandidateAuthorityGate :
      proximityPromotesAuthority canonicalPartialCorroboratedProximity
      ≡
      false

    vectorProximityAloneAuthorityGate :
      vectorOrSpectralPromotesAuthority vectorProximityCarrier ≡ false

    vectorTruthGate :
      vectorOrSpectralPromotesTruth vectorProximityCarrier ≡ false

    vectorSupportGate :
      vectorOrSpectralPromotesSupport vectorProximityCarrier ≡ false

    vectorAdmissibilityGate :
      vectorOrSpectralPromotesAdmissibility vectorProximityCarrier ≡ false

    spectralAuthorityGate :
      vectorOrSpectralPromotesAuthority spectralCoordinateCarrier ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfResidualFieldInvariantStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ pnfResidualFieldInvariantBoundary

    semanticTruthPromotion :
      Bool

    semanticTruthPromotionIsFalse :
      semanticTruthPromotion ≡ false

    supportPromotion :
      Bool

    supportPromotionIsFalse :
      supportPromotion ≡ false

    admissibilityPromotion :
      Bool

    admissibilityPromotionIsFalse :
      admissibilityPromotion ≡ false

    policyLegalWikidataAuthority :
      Bool

    policyLegalWikidataAuthorityIsFalse :
      policyLegalWikidataAuthority ≡ false

    promotionFlags :
      List PNFResidualFieldInvariantPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open PNFResidualFieldInvariantReceipt public

canonicalPNFResidualFieldInvariantReceipt :
  PNFResidualFieldInvariantReceipt
canonicalPNFResidualFieldInvariantReceipt =
  record
    { status =
        residualFieldInvariants_checkedNoAuthorityPromotion
    ; statusIsCheckedNoAuthorityPromotion =
        refl
    ; components =
        canonicalPNFResidualFieldInvariantComponents
    ; componentsAreCanonical =
        refl
    ; severityReceipt =
        SeverityReceipt.canonicalPNFResidualSpectralSeverityReceipt
    ; severityReceiptIsCanonical =
        refl
    ; structuralProjection =
        structuralProjectionOfReceipt
          Core.canonicalPredicateObjectRef
          canonicalPositiveReceipt
    ; structuralProjectionIsCanonical =
        refl
    ; sameFibreComparability =
        sameFibreComparabilityOfReceipts
          Core.canonicalPredicateObjectRef
          Core.canonicalPredicateObjectRef
          Core.fibreFallback
          canonicalPositiveReceipt
          canonicalNegatedReceipt
    ; sameFibreComparabilityIsCanonical =
        refl
    ; levels =
        EXACT ∷ PARTIAL ∷ NO_TYPED_MEET ∷ CONTRADICTION ∷ []
    ; levelsAreCanonical =
        refl
    ; exactScore =
        exactSeverityScoreIsZero
    ; partialScore =
        partialSeverityScoreIsOne
    ; noTypedMeetScore =
        noTypedMeetSeverityScoreIsThree
    ; contradictionScore =
        contradictionSeverityScoreIsNine
    ; joinIsSeverityMax =
        severityMaxJoinScore
    ; contradictionMonotone =
        contradictionIsSeverityTop
    ; contradictionJoinAbsorbsRight =
        joinWithContradictionRight
    ; contradictionJoinAbsorbsLeft =
        joinWithContradictionLeft
    ; visibleContradiction =
        visibleResidualSeverityOf CONTRADICTION
    ; visibleContradictionIsCanonical =
        refl
    ; visibleContradictionSign =
        refl
    ; explicitBridgeExceptionCrosses =
        refl
    ; explicitBridgeExceptionDoesNotCompare =
        refl
    ; exampleRows =
        canonicalRows
    ; exampleRowsAreCanonical =
        refl
    ; exactCorroboratedProximity =
        canonicalExactCorroboratedProximity
    ; exactCorroboratedProximityIsCanonical =
        refl
    ; partialCorroboratedProximity =
        canonicalPartialCorroboratedProximity
    ; partialCorroboratedProximityIsCanonical =
        refl
    ; exactCorroboratedProximityInsideFibre =
        refl
    ; partialCorroboratedProximityInsideFibre =
        refl
    ; contradictionDoesNotCorroborateCompatibility =
        refl
    ; noTypedMeetDoesNotCorroborateCompatibility =
        refl
    ; noTypedMeetCorroboratedProximityOutsideFibre =
        refl
    ; corroboratedCandidateTruthGate =
        refl
    ; corroboratedCandidateSupportGate =
        refl
    ; corroboratedCandidateAdmissibilityGate =
        refl
    ; corroboratedCandidateAuthorityGate =
        refl
    ; vectorProximityAloneAuthorityGate =
        refl
    ; vectorTruthGate =
        refl
    ; vectorSupportGate =
        refl
    ; vectorAdmissibilityGate =
        refl
    ; spectralAuthorityGate =
        refl
    ; statement =
        pnfResidualFieldInvariantStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        pnfResidualFieldInvariantBoundary
    ; boundaryIsCanonical =
        refl
    ; semanticTruthPromotion =
        false
    ; semanticTruthPromotionIsFalse =
        refl
    ; supportPromotion =
        false
    ; supportPromotionIsFalse =
        refl
    ; admissibilityPromotion =
        false
    ; admissibilityPromotionIsFalse =
        refl
    ; policyLegalWikidataAuthority =
        false
    ; policyLegalWikidataAuthorityIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

canonicalReceiptStatementProjection :
  statement canonicalPNFResidualFieldInvariantReceipt
  ≡
  pnfResidualFieldInvariantStatement
canonicalReceiptStatementProjection =
  refl

canonicalReceiptBoundaryProjection :
  boundary canonicalPNFResidualFieldInvariantReceipt
  ≡
  pnfResidualFieldInvariantBoundary
canonicalReceiptBoundaryProjection =
  refl

canonicalReceiptNoAuthorityProjection :
  policyLegalWikidataAuthority canonicalPNFResidualFieldInvariantReceipt
  ≡
  false
canonicalReceiptNoAuthorityProjection =
  refl

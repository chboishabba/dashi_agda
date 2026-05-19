module DASHI.Physics.Closure.G2SFGCPrimeLatticeOrbit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.PrimeLattice as PL
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2PrimeLatticeCoefficientBridge as G2PLCB
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- SFGC / prime-lattice orbit diagnostic.
--
-- The inspected SFGC lane is a three-point right-link process chain:
-- SFGC.GaugeField = ShiftPressurePoint -> Phase4.  PrimeLattice is a
-- standalone FactorVec geometry.  This module records the honest overlap and
-- the exact missing interface needed before the two can be promoted into a
-- curvature bridge.

data G2SFGCPrimeLatticeOrbitStatus : Set where
  noHonestSFGCToFactorVecOrbit :
    G2SFGCPrimeLatticeOrbitStatus

data G2SFGCPrimeLatticeOrbitMissing : Set where
  missingShiftPressurePointToFactorVecEmbedding :
    G2SFGCPrimeLatticeOrbitMissing

  missingShiftPressurePointP2OrbitLaw :
    G2SFGCPrimeLatticeOrbitMissing

  missingPrimeLatticeEdgeToShiftPressurePoint :
    G2SFGCPrimeLatticeOrbitMissing

  missingPrimeIndexedSFGCLinkAction :
    G2SFGCPrimeLatticeOrbitMissing

  missingNondegenerateSFGCPlaquetteGeometry :
    G2SFGCPrimeLatticeOrbitMissing

shiftRightOrbit-start :
  SSL.rightNeighbor SPTI.shiftStartPoint
    ≡
  SPTI.shiftNextPoint
shiftRightOrbit-start =
  refl

shiftRightOrbit-next :
  SSL.rightNeighbor SPTI.shiftNextPoint
    ≡
  SPTI.shiftHeldExitPoint
shiftRightOrbit-next =
  refl

shiftRightOrbit-exit :
  SSL.rightNeighbor SPTI.shiftHeldExitPoint
    ≡
  SPTI.shiftHeldExitPoint
shiftRightOrbit-exit =
  refl

shiftLeftOrbit-start :
  SSL.leftNeighbor SPTI.shiftStartPoint
    ≡
  SPTI.shiftStartPoint
shiftLeftOrbit-start =
  refl

shiftLeftOrbit-next :
  SSL.leftNeighbor SPTI.shiftNextPoint
    ≡
  SPTI.shiftStartPoint
shiftLeftOrbit-next =
  refl

shiftLeftOrbit-exit :
  SSL.leftNeighbor SPTI.shiftHeldExitPoint
    ≡
  SPTI.shiftNextPoint
shiftLeftOrbit-exit =
  refl

record G2SFGCPrimeLatticeOrbitDiagnostic : Set₁ where
  field
    status :
      G2SFGCPrimeLatticeOrbitStatus

    inspectedGaugeField :
      Set

    inspectedGaugeFieldIsSFGC :
      inspectedGaugeField ≡ SFGC.GaugeField

    inspectedPointCarrier :
      Set

    inspectedPointCarrierIsShiftPressurePoint :
      inspectedPointCarrier ≡ SPTI.ShiftPressurePoint

    inspectedPhaseCarrier :
      Set

    inspectedPhaseCarrierIsPhase4 :
      inspectedPhaseCarrier ≡ SPTI4.Phase4

    primeLatticeVertexCarrier :
      Set

    primeLatticeVertexCarrierIsFactorVec :
      primeLatticeVertexCarrier ≡ PL.FactorVec

    primeLatticeEdgeCarrier :
      Set

    primeLatticeEdgeCarrierIsPrimeLatticeEdge :
      primeLatticeEdgeCarrier ≡ PL.PrimeLatticeEdge

    availablePointLinkBridge :
      G2DCC.SFGCPointLink1FormBridge

    availableRightEdgeBridge :
      G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge

    availableCoefficientBridge :
      G2PLCB.G2PrimeLatticeCoefficientBridgeReceipt

    rightNeighborStartLaw :
      SSL.rightNeighbor SPTI.shiftStartPoint ≡ SPTI.shiftNextPoint

    rightNeighborNextLaw :
      SSL.rightNeighbor SPTI.shiftNextPoint ≡ SPTI.shiftHeldExitPoint

    rightNeighborExitLaw :
      SSL.rightNeighbor SPTI.shiftHeldExitPoint ≡ SPTI.shiftHeldExitPoint

    leftNeighborStartLaw :
      SSL.leftNeighbor SPTI.shiftStartPoint ≡ SPTI.shiftStartPoint

    leftNeighborNextLaw :
      SSL.leftNeighbor SPTI.shiftNextPoint ≡ SPTI.shiftStartPoint

    leftNeighborExitLaw :
      SSL.leftNeighbor SPTI.shiftHeldExitPoint ≡ SPTI.shiftNextPoint

    firstMissing :
      G2SFGCPrimeLatticeOrbitMissing

    remainingMissing :
      List G2SFGCPrimeLatticeOrbitMissing

    exactMissingInterface :
      String

    nonPromotionBoundary :
      List String

canonicalG2SFGCPrimeLatticeOrbitDiagnostic :
  G2SFGCPrimeLatticeOrbitDiagnostic
canonicalG2SFGCPrimeLatticeOrbitDiagnostic =
  record
    { status =
        noHonestSFGCToFactorVecOrbit
    ; inspectedGaugeField =
        SFGC.GaugeField
    ; inspectedGaugeFieldIsSFGC =
        refl
    ; inspectedPointCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedPointCarrierIsShiftPressurePoint =
        refl
    ; inspectedPhaseCarrier =
        SPTI4.Phase4
    ; inspectedPhaseCarrierIsPhase4 =
        refl
    ; primeLatticeVertexCarrier =
        PL.FactorVec
    ; primeLatticeVertexCarrierIsFactorVec =
        refl
    ; primeLatticeEdgeCarrier =
        PL.PrimeLatticeEdge
    ; primeLatticeEdgeCarrierIsPrimeLatticeEdge =
        refl
    ; availablePointLinkBridge =
        G2DCC.canonicalSFGCPointLink1FormBridge
    ; availableRightEdgeBridge =
        G2DCC.canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; availableCoefficientBridge =
        G2PLCB.canonicalG2PrimeLatticeCoefficientBridgeReceipt
    ; rightNeighborStartLaw =
        shiftRightOrbit-start
    ; rightNeighborNextLaw =
        shiftRightOrbit-next
    ; rightNeighborExitLaw =
        shiftRightOrbit-exit
    ; leftNeighborStartLaw =
        shiftLeftOrbit-start
    ; leftNeighborNextLaw =
        shiftLeftOrbit-next
    ; leftNeighborExitLaw =
        shiftLeftOrbit-exit
    ; firstMissing =
        missingShiftPressurePointToFactorVecEmbedding
    ; remainingMissing =
        missingShiftPressurePointToFactorVecEmbedding
        ∷ missingShiftPressurePointP2OrbitLaw
        ∷ missingPrimeLatticeEdgeToShiftPressurePoint
        ∷ missingPrimeIndexedSFGCLinkAction
        ∷ missingNondegenerateSFGCPlaquetteGeometry
        ∷ []
    ; exactMissingInterface =
        "shiftPressurePointToFactorVec : ShiftPressurePoint -> FactorVec, plus a p2 coherence law tying SSL.rightNeighbor to PL.primeBump p2; alternatively provide PrimeLatticeEdge -> ShiftPressurePoint or FactorVec -> SSP -> Phase4 for SFGC links"
    ; nonPromotionBoundary =
        "SFGC.GaugeField is definitionally ShiftPressurePoint -> Phase4"
        ∷ "SSL.rightNeighbor and SSL.leftNeighbor give a coherent three-point process chain with reflected endpoints"
        ∷ "PrimeLattice vertices are FactorVec values and edges are prime-indexed FactorVec bumps"
        ∷ "The inspected API provides no sfgcToFactorVec, p2 orbit law, PrimeLatticeEdge -> ShiftPressurePoint projection, or prime-indexed SFGC link sampler"
        ∷ "The available G2 right-edge bridge is local to ShiftPressurePoint and does not construct DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ "No inverse, arbitrary constant embedding, degenerate return plaquette, or coefficient-only d2 law is promoted to an SFGC prime-lattice curvature bridge here"
        ∷ []
    }

g2SFGCPrimeLatticeOrbitFirstMissing :
  G2SFGCPrimeLatticeOrbitDiagnostic.firstMissing
    canonicalG2SFGCPrimeLatticeOrbitDiagnostic
    ≡
  missingShiftPressurePointToFactorVecEmbedding
g2SFGCPrimeLatticeOrbitFirstMissing =
  refl

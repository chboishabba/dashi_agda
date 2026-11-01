module DASHI.Physics.Closure.G2TransverseEdgeAPI where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftSpatialLaplacian as SSL
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2

------------------------------------------------------------------------
-- G2 transverse-edge API sidecar.
--
-- This module audits the actual SFGC/G2 shift edge surface.  It does not
-- construct a DiscreteCurvatureCarrier for SFGC.GaugeField.

record NondegenerateTwoDirectionPlaquetteAPI : Set₁ where
  field
    Vertex :
      Set

    RightEdge :
      Set

    TransverseEdge :
      Set

    Plaquette :
      Set

    rightSource :
      RightEdge →
      Vertex

    rightTarget :
      RightEdge →
      Vertex

    transverseSource :
      TransverseEdge →
      Vertex

    transverseTarget :
      TransverseEdge →
      Vertex

    bottomEdge :
      Plaquette →
      RightEdge

    rightEdge :
      Plaquette →
      TransverseEdge

    topEdge :
      Plaquette →
      RightEdge

    leftEdge :
      Plaquette →
      TransverseEdge

    southwest :
      Plaquette →
      Vertex

    southeast :
      Plaquette →
      Vertex

    northeast :
      Plaquette →
      Vertex

    northwest :
      Plaquette →
      Vertex

    bottomSourceLaw :
      (p : Plaquette) →
      rightSource (bottomEdge p) ≡ southwest p

    bottomTargetLaw :
      (p : Plaquette) →
      rightTarget (bottomEdge p) ≡ southeast p

    rightSourceLaw :
      (p : Plaquette) →
      transverseSource (rightEdge p) ≡ southeast p

    rightTargetLaw :
      (p : Plaquette) →
      transverseTarget (rightEdge p) ≡ northeast p

    topSourceLaw :
      (p : Plaquette) →
      rightSource (topEdge p) ≡ northwest p

    topTargetLaw :
      (p : Plaquette) →
      rightTarget (topEdge p) ≡ northeast p

    leftSourceLaw :
      (p : Plaquette) →
      transverseSource (leftEdge p) ≡ southwest p

    leftTargetLaw :
      (p : Plaquette) →
      transverseTarget (leftEdge p) ≡ northwest p

    primeBumpCommutes :
      (p : Plaquette) →
      transverseTarget (rightEdge p) ≡ rightTarget (topEdge p)

    signedPlaquetteBoundary :
      Plaquette →
      List (G2.SignedBoundaryEdge RightEdge)

    apiBoundary :
      List String

data G2TransverseEdgeAPIStatus : Set where
  onlyRightEdgeNoIndependentTransverseEdge :
    G2TransverseEdgeAPIStatus

data G2TransverseEdgeMissingAPI : Set where
  missingSFGCShiftTransverseEdge :
    G2TransverseEdgeMissingAPI

  missingSFGCShiftTransverseEdgeSource :
    G2TransverseEdgeMissingAPI

  missingSFGCShiftTransverseEdgeTarget :
    G2TransverseEdgeMissingAPI

  missingSFGCShiftTransverseEndpointLaws :
    G2TransverseEdgeMissingAPI

  missingSFGCTwoDirectionPlaquetteConstructor :
    G2TransverseEdgeMissingAPI

  missingSFGCPlaquettePrimeBumpCommutationLaw :
    G2TransverseEdgeMissingAPI

  missingSFGCNondegenerateSignedPlaquetteBoundary :
    G2TransverseEdgeMissingAPI

  missingSFGCBoundaryOfBoundaryZeroLaw :
    G2TransverseEdgeMissingAPI

record G2SFGCTransverseEdgeAPIRequest : Set₁ where
  field
    status :
      G2TransverseEdgeAPIStatus

    inspectedGaugeField :
      Set

    inspectedGaugeFieldIsSFGC :
      inspectedGaugeField ≡ SFGC.GaugeField

    inspectedGaugeFieldShape :
      String

    inspectedRightEdge :
      Set

    inspectedRightEdgeIsCurrentG2RightEdge :
      inspectedRightEdge ≡ G2.SFGCShiftRightEdge

    inspectedRightEdgeSource :
      inspectedRightEdge →
      SPTI.ShiftPressurePoint

    inspectedRightEdgeTarget :
      inspectedRightEdge →
      SPTI.ShiftPressurePoint

    inspectedRightEdgeTargetLawName :
      String

    inspectedRightEdgeTargetLawShape :
      String

    inspectedRightEdge1Form :
      Set

    inspectedRightEdge1FormBridge :
      G2.SFGCShiftRightEdgePrimeLattice1FormBridge

    availableDegenerateReturnPlaquette :
      G2.SFGCShiftRightEdgePlaquetteNormalizerSurface

    availableDegenerateTwoStepReturnPlaquette :
      G2.SFGCShiftRightEdgeTwoStepPlaquetteSurface

    missingAPIs :
      List G2TransverseEdgeMissingAPI

    exactMissingConstructor :
      String

    exactMissingConstructorShape :
      String

    exactMissingEndpointLaw :
      String

    exactMissingEndpointLawShape :
      String

    exactMissingPrimeLaw :
      String

    exactMissingPrimeLawShape :
      String

    blockedCarrierTarget :
      String

    requestBoundary :
      List String

canonicalG2SFGCTransverseEdgeAPIRequest :
  G2SFGCTransverseEdgeAPIRequest
canonicalG2SFGCTransverseEdgeAPIRequest =
  record
    { status =
        onlyRightEdgeNoIndependentTransverseEdge
    ; inspectedGaugeField =
        SFGC.GaugeField
    ; inspectedGaugeFieldIsSFGC =
        refl
    ; inspectedGaugeFieldShape =
        "SFGC.GaugeField = ShiftPressurePoint -> Phase4; one static right-link phase per point"
    ; inspectedRightEdge =
        G2.SFGCShiftRightEdge
    ; inspectedRightEdgeIsCurrentG2RightEdge =
        refl
    ; inspectedRightEdgeSource =
        G2.sfgcShiftRightEdgeSource
    ; inspectedRightEdgeTarget =
        G2.sfgcShiftRightEdgeTarget
    ; inspectedRightEdgeTargetLawName =
        "sfgcShiftRightEdgeTarget"
    ; inspectedRightEdgeTargetLawShape =
        "sfgcShiftRightEdgeTarget edge = SSL.rightNeighbor edge"
    ; inspectedRightEdge1Form =
        G2.SFGCShiftRightEdge1Form
    ; inspectedRightEdge1FormBridge =
        G2.canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; availableDegenerateReturnPlaquette =
        G2.canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface
    ; availableDegenerateTwoStepReturnPlaquette =
        G2.canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface
    ; missingAPIs =
        missingSFGCShiftTransverseEdge
        ∷ missingSFGCShiftTransverseEdgeSource
        ∷ missingSFGCShiftTransverseEdgeTarget
        ∷ missingSFGCShiftTransverseEndpointLaws
        ∷ missingSFGCTwoDirectionPlaquetteConstructor
        ∷ missingSFGCPlaquettePrimeBumpCommutationLaw
        ∷ missingSFGCNondegenerateSignedPlaquetteBoundary
        ∷ missingSFGCBoundaryOfBoundaryZeroLaw
        ∷ []
    ; exactMissingConstructor =
        "SFGCShiftTransverseEdge"
    ; exactMissingConstructorShape =
        "independent transverse edge carrier over ShiftPressurePoint, not definitionally the current right-edge anchor"
    ; exactMissingEndpointLaw =
        "sfgcShiftTransverseEdgeEndpointLaws"
    ; exactMissingEndpointLawShape =
        "source/target laws for transverse edges plus SW/SE/NE/NW plaquette endpoint equalities"
    ; exactMissingPrimeLaw =
        "sfgcPlaquettePrimeBumpCommutes"
    ; exactMissingPrimeLawShape =
        "bottom-then-transverse and transverse-then-bottom endpoint/transport laws identify the same NE vertex"
    ; blockedCarrierTarget =
        "DiscreteCurvatureCarrier SFGC.GaugeField"
    ; requestBoundary =
        "The inspected SFGC lane exposes Phase4 right-neighbor links through SFGC.GaugeField and SSL.rightNeighbor"
        ∷ "G2 exposes SFGCShiftRightEdge, source/target maps, a right-edge 1-form bridge, and degenerate return plaquette normalizers"
        ∷ "No prime-parameterized or independent transverse edge API exists in the inspected modules"
        ∷ "Degenerate return plaquettes are not promoted to two-direction curvature"
        ∷ "No Maxwell/G2 closure claim is made by this sidecar"
        ∷ []
    }

g2SFGCTransverseEdgeFirstMissing :
  G2SFGCTransverseEdgeAPIRequest.exactMissingConstructor
    canonicalG2SFGCTransverseEdgeAPIRequest
  ≡
  "SFGCShiftTransverseEdge"
g2SFGCTransverseEdgeFirstMissing =
  refl

g2SFGCRightEdgeTargetIsRightNeighbor :
  (edge : G2.SFGCShiftRightEdge) →
  G2SFGCTransverseEdgeAPIRequest.inspectedRightEdgeTarget
    canonicalG2SFGCTransverseEdgeAPIRequest
    edge
  ≡
  SSL.rightNeighbor edge
g2SFGCRightEdgeTargetIsRightNeighbor edge =
  refl

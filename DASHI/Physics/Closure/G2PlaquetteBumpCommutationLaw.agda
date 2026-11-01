module DASHI.Physics.Closure.G2PlaquetteBumpCommutationLaw where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2

------------------------------------------------------------------------
-- Conditional G2 plaquette bump-commutation law surface.
--
-- This module does not construct DiscreteCurvatureCarrier.  It packages the
-- narrow law that becomes available once Lane 3 supplies an independent
-- transverse-edge API and the associated nondegenerate square laws.

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record G2PlaquetteTransverseEdgeAPI : Set₁ where
  field
    BasePoint :
      Set

    PrimeDirection :
      Set

    Edge :
      Set

    Plaquette :
      Set

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Coefficient :
      Set

    coefficientLaws :
      G2.AbelianCoefficientLawSurface Coefficient

    p1 :
      PrimeDirection

    p2 :
      PrimeDirection

    p1≠p2 :
      p1 ≠ p2

    _+p_ :
      PrimeDirection →
      PrimeDirection →
      PrimeDirection

    p1+p2=p2+p1 :
      (p1 +p p2) ≡ (p2 +p p1)

    bump :
      BasePoint →
      PrimeDirection →
      BasePoint

    bump-commutes :
      (base : BasePoint) →
      bump (bump base p1) p2
        ≡
      bump (bump base p2) p1

    plaquetteAt :
      BasePoint →
      Plaquette

    squareSW :
      Plaquette →
      BasePoint

    squareSE :
      Plaquette →
      BasePoint

    squareNE :
      Plaquette →
      BasePoint

    squareNW :
      Plaquette →
      BasePoint

    bottomEdge :
      Plaquette →
      Edge

    rightEdge :
      Plaquette →
      Edge

    topEdge :
      Plaquette →
      Edge

    leftEdge :
      Plaquette →
      Edge

    edgeSource :
      Edge →
      BasePoint

    edgeTarget :
      Edge →
      BasePoint

    bottomSourceLaw :
      (base : BasePoint) →
      edgeSource (bottomEdge (plaquetteAt base)) ≡ squareSW (plaquetteAt base)

    bottomTargetLaw :
      (base : BasePoint) →
      edgeTarget (bottomEdge (plaquetteAt base)) ≡ squareSE (plaquetteAt base)

    rightSourceLaw :
      (base : BasePoint) →
      edgeSource (rightEdge (plaquetteAt base)) ≡ squareSE (plaquetteAt base)

    rightTargetLaw :
      (base : BasePoint) →
      edgeTarget (rightEdge (plaquetteAt base)) ≡ squareNE (plaquetteAt base)

    topSourceLaw :
      (base : BasePoint) →
      edgeSource (topEdge (plaquetteAt base)) ≡ squareNW (plaquetteAt base)

    topTargetLaw :
      (base : BasePoint) →
      edgeTarget (topEdge (plaquetteAt base)) ≡ squareNE (plaquetteAt base)

    leftSourceLaw :
      (base : BasePoint) →
      edgeSource (leftEdge (plaquetteAt base)) ≡ squareSW (plaquetteAt base)

    leftTargetLaw :
      (base : BasePoint) →
      edgeTarget (leftEdge (plaquetteAt base)) ≡ squareNW (plaquetteAt base)

    signedPlaquetteBoundary :
      Plaquette →
      List (G2.SignedBoundaryEdge Edge)

    signedPlaquetteBoundary-corrected :
      (base : BasePoint) →
      signedPlaquetteBoundary (plaquetteAt base)
        ≡
      G2.correctedSquareBoundary
        (bottomEdge (plaquetteAt base))
        (rightEdge (plaquetteAt base))
        (topEdge (plaquetteAt base))
        (leftEdge (plaquetteAt base))

    evaluate1 :
      Discrete1Form →
      Edge →
      Coefficient

    δ₀ :
      Discrete0Form →
      Discrete1Form

    vacuum1Form :
      Discrete1Form

    zeroCoeff :
      Coefficient

    zeroCoeff-isCoefficientZero :
      zeroCoeff ≡ G2.AbelianCoefficientLawSurface.zeroCoeff coefficientLaws

    ring-angle-cancellation :
      (a : Discrete1Form) →
      (base : BasePoint) →
      G2.signedBoundarySum
        coefficientLaws
        (evaluate1 a)
        (signedPlaquetteBoundary (plaquetteAt base))
        ≡
      zeroCoeff

    d²-zero-by-bump-commutation :
      (f : Discrete0Form) →
      (base : BasePoint) →
      G2.signedBoundarySum
        coefficientLaws
        (evaluate1 (δ₀ f))
        (signedPlaquetteBoundary (plaquetteAt base))
        ≡
      zeroCoeff

    apiBoundary :
      List String

δ₁Signed :
  (api : G2PlaquetteTransverseEdgeAPI) →
  G2PlaquetteTransverseEdgeAPI.Discrete1Form api →
  G2PlaquetteTransverseEdgeAPI.BasePoint api →
  G2PlaquetteTransverseEdgeAPI.Coefficient api
δ₁Signed api a base =
  G2.signedBoundarySum
    (G2PlaquetteTransverseEdgeAPI.coefficientLaws api)
    (G2PlaquetteTransverseEdgeAPI.evaluate1 api a)
    (G2PlaquetteTransverseEdgeAPI.signedPlaquetteBoundary api
      (G2PlaquetteTransverseEdgeAPI.plaquetteAt api base))

δ₁Signed-zero :
  (api : G2PlaquetteTransverseEdgeAPI) →
  (a : G2PlaquetteTransverseEdgeAPI.Discrete1Form api) →
  (base : G2PlaquetteTransverseEdgeAPI.BasePoint api) →
  δ₁Signed api a base
    ≡
  G2PlaquetteTransverseEdgeAPI.zeroCoeff api
δ₁Signed-zero api =
  G2PlaquetteTransverseEdgeAPI.ring-angle-cancellation api

record G2PlaquetteVacuumFlatnessSurface
  (api : G2PlaquetteTransverseEdgeAPI) : Set where
  field
    vacuumFlatness :
      (base : G2PlaquetteTransverseEdgeAPI.BasePoint api) →
      δ₁Signed api
        (G2PlaquetteTransverseEdgeAPI.vacuum1Form api)
        base
        ≡
      G2PlaquetteTransverseEdgeAPI.zeroCoeff api

    vacuumFlatnessBoundary :
      List String

vacuumFlatnessSurfaceFromδ₁SignedZero :
  (api : G2PlaquetteTransverseEdgeAPI) →
  G2PlaquetteVacuumFlatnessSurface api
vacuumFlatnessSurfaceFromδ₁SignedZero api =
  record
    { vacuumFlatness =
        δ₁Signed-zero api
          (G2PlaquetteTransverseEdgeAPI.vacuum1Form api)
    ; vacuumFlatnessBoundary =
        "Conditional vacuum flatness follows only after Lane 3 supplies the transverse plaquette API and ring/angle cancellation law"
        ∷ "This is flatness of δ₁Signed on the selected vacuum 1-form; it is not a DiscreteCurvatureCarrier inhabitant"
        ∷ []
    }

record G2PlaquetteD²BumpCommutationLaw
  (api : G2PlaquetteTransverseEdgeAPI) : Set where
  field
    p1NotP2 :
      G2PlaquetteTransverseEdgeAPI.p1 api
        ≠
      G2PlaquetteTransverseEdgeAPI.p2 api

    primeAdditionCommutes :
      (G2PlaquetteTransverseEdgeAPI._+p_ api
        (G2PlaquetteTransverseEdgeAPI.p1 api)
        (G2PlaquetteTransverseEdgeAPI.p2 api))
        ≡
      (G2PlaquetteTransverseEdgeAPI._+p_ api
        (G2PlaquetteTransverseEdgeAPI.p2 api)
        (G2PlaquetteTransverseEdgeAPI.p1 api))

    bumpCommutation :
      (base : G2PlaquetteTransverseEdgeAPI.BasePoint api) →
      G2PlaquetteTransverseEdgeAPI.bump api
        (G2PlaquetteTransverseEdgeAPI.bump api base
          (G2PlaquetteTransverseEdgeAPI.p1 api))
        (G2PlaquetteTransverseEdgeAPI.p2 api)
        ≡
      G2PlaquetteTransverseEdgeAPI.bump api
        (G2PlaquetteTransverseEdgeAPI.bump api base
          (G2PlaquetteTransverseEdgeAPI.p2 api))
        (G2PlaquetteTransverseEdgeAPI.p1 api)

    d²-zero :
      (f : G2PlaquetteTransverseEdgeAPI.Discrete0Form api) →
      (base : G2PlaquetteTransverseEdgeAPI.BasePoint api) →
      δ₁Signed api
        (G2PlaquetteTransverseEdgeAPI.δ₀ api f)
        base
        ≡
      G2PlaquetteTransverseEdgeAPI.zeroCoeff api

    lawBoundary :
      List String

d²BumpCommutationLawFromAPI :
  (api : G2PlaquetteTransverseEdgeAPI) →
  G2PlaquetteD²BumpCommutationLaw api
d²BumpCommutationLawFromAPI api =
  record
    { p1NotP2 =
        G2PlaquetteTransverseEdgeAPI.p1≠p2 api
    ; primeAdditionCommutes =
        G2PlaquetteTransverseEdgeAPI.p1+p2=p2+p1 api
    ; bumpCommutation =
        G2PlaquetteTransverseEdgeAPI.bump-commutes api
    ; d²-zero =
        G2PlaquetteTransverseEdgeAPI.d²-zero-by-bump-commutation api
    ; lawBoundary =
        "d²-zero is conditional on the supplied nondegenerate square and bump-commutation laws"
        ∷ "The square must expose base, p1, p2, p1≠p2, four oriented edges, p1+p2=p2+p1, and ring/angle cancellation"
        ∷ "No curvature carrier, Bianchi law, or Maxwell field-strength bridge is constructed by this law package"
        ∷ []
    }

data G2PlaquetteBumpCommutationSurfaceStatus : Set where
  conditionalOnLane3TransverseEdgeAPI :
    G2PlaquetteBumpCommutationSurfaceStatus

record G2PlaquetteBumpCommutationSurfaceReceipt : Set₁ where
  field
    status :
      G2PlaquetteBumpCommutationSurfaceStatus

    conditionalAPIName :
      String

    δ₁SignedName :
      String

    δ₁SignedZeroName :
      String

    vacuumFlatnessSurfaceName :
      String

    d²BumpCommutationLawName :
      String

    currentG2PlaquetteRequest :
      G2.SFGCNondegeneratePlaquetteCarrierRequest

    exactInputsRequired :
      List String

    blockedByLane3 :
      List G2.SFGCNondegeneratePlaquetteMissingAPI

    noPromotionBoundary :
      List String

canonicalG2PlaquetteBumpCommutationSurfaceReceipt :
  G2PlaquetteBumpCommutationSurfaceReceipt
canonicalG2PlaquetteBumpCommutationSurfaceReceipt =
  record
    { status =
        conditionalOnLane3TransverseEdgeAPI
    ; conditionalAPIName =
        "G2PlaquetteTransverseEdgeAPI"
    ; δ₁SignedName =
        "δ₁Signed"
    ; δ₁SignedZeroName =
        "δ₁Signed-zero"
    ; vacuumFlatnessSurfaceName =
        "G2PlaquetteVacuumFlatnessSurface"
    ; d²BumpCommutationLawName =
        "G2PlaquetteD²BumpCommutationLaw"
    ; currentG2PlaquetteRequest =
        G2.canonicalSFGCNondegeneratePlaquetteCarrierRequest
    ; exactInputsRequired =
        "base point carrier and plaquetteAt base"
        ∷ "independent p1 and p2 directions with p1≠p2"
        ∷ "four oriented edges: bottom, right, top, left"
        ∷ "endpoint laws for SW, SE, NE, NW"
        ∷ "prime addition law p1+p2=p2+p1"
        ∷ "bump-commutation law reaching the same NE corner in both orders"
        ∷ "signed plaquette boundary +bottom,+right,-top,-left"
        ∷ "Phase/ring coefficient cancellation for signed boundary sums"
        ∷ "d²-zero law for δ₁Signed after δ₀"
        ∷ []
    ; blockedByLane3 =
        G2.sfgcMissingIndependentTransverseEdgeAPI
        ∷ G2.sfgcMissingTransverseEdgeEndpointLaws
        ∷ G2.sfgcMissingNondegeneratePlaquetteVertexAPI
        ∷ G2.sfgcMissingNondegenerateSignedPlaquetteBoundary
        ∷ G2.sfgcMissingPlaquetteBumpCommutationAPI
        ∷ G2.sfgcMissingPlaquetteBumpCommutationLaws
        ∷ G2.sfgcMissingPlaquetteBoundaryOfBoundaryZero
        ∷ []
    ; noPromotionBoundary =
        "This receipt is conditional: it names the typed surface available once Lane 3 supplies the transverse-edge API"
        ∷ "The existing G2 lane still has only degenerate right-edge return normalizers, so no inhabited nondegenerate plaquette law is exported here"
        ∷ "This module does not construct DiscreteCurvatureCarrier SFGC.GaugeField"
        ∷ []
    }

module DASHI.Physics.Closure.G2NondegeneratePlaquetteSchema where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2SFGCAsUOnePrimeLattice as G2U1
import DASHI.Physics.Closure.G2TransverseEdgeAPI as G2TE
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- Exact schema required before the current SFGC right-edge surface can be
-- promoted to nondegenerate U(1) plaquette curvature.
--
-- This module is intentionally a receipt, not a carrier inhabitant.  The
-- inspected API exposes only right-neighbor links over a three-point process
-- chain, so any honest curvature carrier still needs a second independent
-- direction and square endpoint laws.

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record RequiredNondegenerateSFGCPlaquetteAPI
  (ConnectionCarrier : Set) : Set₁ where
  field
    Site :
      Set

    Direction :
      Set

    rightDirection :
      Direction

    transverseDirection :
      Direction

    independentDirections :
      rightDirection ≠ transverseDirection

    Edge :
      Set

    edgeAt :
      Direction →
      Site →
      Edge

    edgeSource :
      Edge →
      Site

    edgeTarget :
      Edge →
      Site

    edgeSourceLaw :
      (dir : Direction) →
      (site : Site) →
      edgeSource (edgeAt dir site) ≡ site

    shiftAction :
      Direction →
      Site →
      Site

    edgeTargetLaw :
      (dir : Direction) →
      (site : Site) →
      edgeTarget (edgeAt dir site) ≡ shiftAction dir site

    Plaquette :
      Set

    plaquetteAt :
      Site →
      Plaquette

    southwest :
      Plaquette →
      Site

    southeast :
      Plaquette →
      Site

    northeast :
      Plaquette →
      Site

    northwest :
      Plaquette →
      Site

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

    bottomSourceLaw :
      (base : Site) →
      edgeSource (bottomEdge (plaquetteAt base)) ≡ southwest (plaquetteAt base)

    bottomTargetLaw :
      (base : Site) →
      edgeTarget (bottomEdge (plaquetteAt base)) ≡ southeast (plaquetteAt base)

    rightSourceLaw :
      (base : Site) →
      edgeSource (rightEdge (plaquetteAt base)) ≡ southeast (plaquetteAt base)

    rightTargetLaw :
      (base : Site) →
      edgeTarget (rightEdge (plaquetteAt base)) ≡ northeast (plaquetteAt base)

    topSourceLaw :
      (base : Site) →
      edgeSource (topEdge (plaquetteAt base)) ≡ northwest (plaquetteAt base)

    topTargetLaw :
      (base : Site) →
      edgeTarget (topEdge (plaquetteAt base)) ≡ northeast (plaquetteAt base)

    leftSourceLaw :
      (base : Site) →
      edgeSource (leftEdge (plaquetteAt base)) ≡ southwest (plaquetteAt base)

    leftTargetLaw :
      (base : Site) →
      edgeTarget (leftEdge (plaquetteAt base)) ≡ northwest (plaquetteAt base)

    plaquetteCommutes :
      (base : Site) →
      shiftAction transverseDirection (shiftAction rightDirection base)
        ≡
      shiftAction rightDirection (shiftAction transverseDirection base)

    signedPlaquetteBoundary :
      Plaquette →
      List (G2DCC.SignedBoundaryEdge Edge)

    signedPlaquetteBoundaryIsCorrectedSquare :
      (base : Site) →
      signedPlaquetteBoundary (plaquetteAt base)
        ≡
      G2DCC.correctedSquareBoundary
        (bottomEdge (plaquetteAt base))
        (rightEdge (plaquetteAt base))
        (topEdge (plaquetteAt base))
        (leftEdge (plaquetteAt base))

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    connectionTo1Form :
      ConnectionCarrier →
      Discrete1Form

    evaluate1 :
      Discrete1Form →
      Edge →
      SPTI4.Phase4

    evaluate2 :
      Discrete2Form →
      Plaquette →
      SPTI4.Phase4

    δ₀ :
      Discrete0Form →
      Discrete1Form

    δ₁ :
      Discrete1Form →
      Discrete2Form

    boundaryOfBoundaryZero :
      (f : Discrete0Form) →
      (base : Site) →
      evaluate2 (δ₁ (δ₀ f)) (plaquetteAt base) ≡ SPTI4.φ0

    vacuumConnection :
      ConnectionCarrier

    vacuumFlatness :
      (base : Site) →
      evaluate2 (δ₁ (connectionTo1Form vacuumConnection)) (plaquetteAt base)
        ≡
      SPTI4.φ0

    FieldStrengthCarrier :
      Set

    fieldStrengthFromCurvature :
      Discrete2Form →
      FieldStrengthCarrier

    schemaBoundary :
      List String

discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI :
  {ConnectionCarrier : Set} →
  RequiredNondegenerateSFGCPlaquetteAPI ConnectionCarrier →
  G2DCC.DiscreteCurvatureCarrier ConnectionCarrier
discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI api =
  record
    { CurvatureCarrier =
        RequiredNondegenerateSFGCPlaquetteAPI.Discrete2Form api
    ; curvatureFromConnection =
        λ connection →
          RequiredNondegenerateSFGCPlaquetteAPI.δ₁ api
            (RequiredNondegenerateSFGCPlaquetteAPI.connectionTo1Form api
              connection)
    ; FieldStrengthCarrier =
        RequiredNondegenerateSFGCPlaquetteAPI.FieldStrengthCarrier api
    ; curvatureToFieldStrength =
        RequiredNondegenerateSFGCPlaquetteAPI.fieldStrengthFromCurvature api
    ; carrierBoundary =
        RequiredNondegenerateSFGCPlaquetteAPI.schemaBoundary api
    }

data G2NondegeneratePlaquetteSchemaStatus : Set where
  blockedBySingleRightEdgeOnly :
    G2NondegeneratePlaquetteSchemaStatus

data G2NondegeneratePlaquetteSchemaMissing : Set where
  missingSecondIndependentDirection :
    G2NondegeneratePlaquetteSchemaMissing

  missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge :
    G2NondegeneratePlaquetteSchemaMissing

  missingDirectionIndexedEdgeAction :
    G2NondegeneratePlaquetteSchemaMissing

  missingNondegenerateTwoCellBoundary :
    G2NondegeneratePlaquetteSchemaMissing

  missingPlaquetteCommutationLaw :
    G2NondegeneratePlaquetteSchemaMissing

  missingBoundaryOfBoundaryZeroForPlaquettes :
    G2NondegeneratePlaquetteSchemaMissing

  missingFieldStrengthFromCurvature :
    G2NondegeneratePlaquetteSchemaMissing

------------------------------------------------------------------------
-- Minimal direction-indexed schema extension.
--
-- This is the local typechecking schema requested by the G2 continuation
-- lane.  It does not mutate the current three-point SFGC process carrier.
-- Instead, it states the smallest interface a core SFGC adoption would have
-- to expose: a site carrier with a p2/right direction, a p3/up direction,
-- direction-indexed edges, commuting square endpoints, and an explicit
-- curvature-to-field-strength consumer.

data SFGCPrimeDirection : Set where
  p2RightDirection :
    SFGCPrimeDirection
  p3UpDirection :
    SFGCPrimeDirection

p2RightDirection≠p3UpDirection :
  p2RightDirection ≠ p3UpDirection
p2RightDirection≠p3UpDirection ()

record RequiredDirectionIndexedSFGCSchemaExtension
  (ConnectionCarrier : Set) : Set₁ where
  field
    SFGCSite :
      Set

    PrimeDirection :
      Set

    p2Right :
      PrimeDirection

    p3Up :
      PrimeDirection

    p2Right≠p3Up :
      p2Right ≠ p3Up

    primeDirectionBoundary :
      List String

    SFGCShiftEdge :
      PrimeDirection →
      SFGCSite →
      Set

    edgeSource :
      {dir : PrimeDirection} →
      {site : SFGCSite} →
      SFGCShiftEdge dir site →
      SFGCSite

    edgeSourceLaw :
      {dir : PrimeDirection} →
      (site : SFGCSite) →
      (edge : SFGCShiftEdge dir site) →
      edgeSource edge ≡ site

    shiftAction :
      PrimeDirection →
      SFGCSite →
      SFGCSite

    edgeTarget :
      {dir : PrimeDirection} →
      {site : SFGCSite} →
      SFGCShiftEdge dir site →
      SFGCSite

    edgeTargetLaw :
      {dir : PrimeDirection} →
      (site : SFGCSite) →
      (edge : SFGCShiftEdge dir site) →
      edgeTarget edge ≡ shiftAction dir site

    rightEdgeAt :
      (site : SFGCSite) →
      SFGCShiftEdge p2Right site

    upEdgeAt :
      (site : SFGCSite) →
      SFGCShiftEdge p3Up site

    rightInterpretsCurrentRightNeighbor :
      String

    upInterpretsTransverseP3Bump :
      String

    rightThenUp :
      SFGCSite →
      SFGCSite

    upThenRight :
      SFGCSite →
      SFGCSite

    rightThenUpLaw :
      (site : SFGCSite) →
      rightThenUp site ≡ shiftAction p3Up (shiftAction p2Right site)

    upThenRightLaw :
      (site : SFGCSite) →
      upThenRight site ≡ shiftAction p2Right (shiftAction p3Up site)

    p2p3ShiftCommutes :
      (site : SFGCSite) →
      rightThenUp site ≡ upThenRight site

    NondegeneratePlaquette :
      Set

    plaquetteAt :
      SFGCSite →
      NondegeneratePlaquette

    plaquetteAPI :
      RequiredNondegenerateSFGCPlaquetteAPI ConnectionCarrier

    plaquetteAPISiteIsDirectionIndexedSite :
      RequiredNondegenerateSFGCPlaquetteAPI.Site plaquetteAPI
        ≡
      SFGCSite

    plaquetteAPIDirectionIsPrimeDirection :
      RequiredNondegenerateSFGCPlaquetteAPI.Direction plaquetteAPI
        ≡
      PrimeDirection

    plaquetteAPIRightIsP2 :
      String

    plaquetteAPITransverseIsP3 :
      String

    fieldStrengthBoundary :
      List String

directionIndexedSchemaYieldsDiscreteCurvatureCarrier :
  {ConnectionCarrier : Set} →
  RequiredDirectionIndexedSFGCSchemaExtension ConnectionCarrier →
  G2DCC.DiscreteCurvatureCarrier ConnectionCarrier
directionIndexedSchemaYieldsDiscreteCurvatureCarrier extension =
  discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI
    (RequiredDirectionIndexedSFGCSchemaExtension.plaquetteAPI extension)

fieldStrengthFromDirectionIndexedCurvature :
  {ConnectionCarrier : Set} →
  (extension : RequiredDirectionIndexedSFGCSchemaExtension ConnectionCarrier) →
  G2DCC.DiscreteCurvatureCarrier.CurvatureCarrier
    (directionIndexedSchemaYieldsDiscreteCurvatureCarrier extension) →
  G2DCC.DiscreteCurvatureCarrier.FieldStrengthCarrier
    (directionIndexedSchemaYieldsDiscreteCurvatureCarrier extension)
fieldStrengthFromDirectionIndexedCurvature extension =
  G2DCC.DiscreteCurvatureCarrier.curvatureToFieldStrength
    (directionIndexedSchemaYieldsDiscreteCurvatureCarrier extension)

record DirectionIndexedSFGCAdoptionWrapper
  (ConnectionCarrier : Set) : Set₁ where
  field
    schemaExtension :
      RequiredDirectionIndexedSFGCSchemaExtension ConnectionCarrier

    adoptedDiscreteCurvatureCarrier :
      G2DCC.DiscreteCurvatureCarrier ConnectionCarrier

    adoptedDiscreteCurvatureCarrierIsFromSchema :
      adoptedDiscreteCurvatureCarrier
        ≡
      directionIndexedSchemaYieldsDiscreteCurvatureCarrier schemaExtension

    fieldStrengthFromAdoptedCurvature :
      G2DCC.DiscreteCurvatureCarrier.CurvatureCarrier
        adoptedDiscreteCurvatureCarrier →
      G2DCC.DiscreteCurvatureCarrier.FieldStrengthCarrier
        adoptedDiscreteCurvatureCarrier

    adoptionBoundary :
      List String

directionIndexedSchemaAdoptionWrapper :
  {ConnectionCarrier : Set} →
  (extension : RequiredDirectionIndexedSFGCSchemaExtension ConnectionCarrier) →
  DirectionIndexedSFGCAdoptionWrapper ConnectionCarrier
directionIndexedSchemaAdoptionWrapper extension =
  record
    { schemaExtension =
        extension
    ; adoptedDiscreteCurvatureCarrier =
        directionIndexedSchemaYieldsDiscreteCurvatureCarrier extension
    ; adoptedDiscreteCurvatureCarrierIsFromSchema =
        refl
    ; fieldStrengthFromAdoptedCurvature =
        fieldStrengthFromDirectionIndexedCurvature extension
    ; adoptionBoundary =
        "This is the local adoption wrapper: a supplied direction-indexed SFGC schema yields the G2 DiscreteCurvatureCarrier"
        ∷ "The wrapper does not invent core SFGCShiftEdge/shiftAction data; it only packages the already supplied schema"
        ∷ "Field strength is inhabited exactly through the schema plaquetteAPI fieldStrengthFromCurvature consumer"
        ∷ []
    }

data G2DirectionIndexedSchemaExtensionStatus : Set where
  directionIndexedSchemaSurfaceAvailableCoreAdoptionBlocked :
    G2DirectionIndexedSchemaExtensionStatus

record G2DirectionIndexedSchemaExtensionReceipt : Set₂ where
  field
    status :
      G2DirectionIndexedSchemaExtensionStatus

    canonicalPrimeDirectionCarrier :
      Set

    canonicalPrimeDirectionCarrierIsP2P3 :
      canonicalPrimeDirectionCarrier ≡ SFGCPrimeDirection

    canonicalRightDirection :
      SFGCPrimeDirection

    canonicalRightDirectionIsP2 :
      canonicalRightDirection ≡ p2RightDirection

    canonicalUpDirection :
      SFGCPrimeDirection

    canonicalUpDirectionIsP3 :
      canonicalUpDirection ≡ p3UpDirection

    canonicalDirectionsIndependent :
      canonicalRightDirection ≠ canonicalUpDirection

    sufficientSchema :
      Set₁

    sufficientSchemaIsDirectionIndexedExtension :
      sufficientSchema
        ≡
      RequiredDirectionIndexedSFGCSchemaExtension SFGC.GaugeField

    sufficientConstructorName :
      String

    sufficientConstructorTarget :
      String

    localAdoptionWrapperName :
      String

    localAdoptionWrapperTarget :
      String

    conditionalFieldStrengthWrapperName :
      String

    currentCoreAdoptionAvailable :
      Bool

    currentCoreAdoptionAvailableIsFalse :
      currentCoreAdoptionAvailable ≡ false

    nextBlocker :
      G2NondegeneratePlaquetteSchemaMissing

    nextFieldStrengthBlocker :
      G2NondegeneratePlaquetteSchemaMissing

    exactCoreFieldsRequired :
      List String

    schemaBoundary :
      List String

canonicalG2DirectionIndexedSchemaExtensionReceipt :
  G2DirectionIndexedSchemaExtensionReceipt
canonicalG2DirectionIndexedSchemaExtensionReceipt =
  record
    { status =
        directionIndexedSchemaSurfaceAvailableCoreAdoptionBlocked
    ; canonicalPrimeDirectionCarrier =
        SFGCPrimeDirection
    ; canonicalPrimeDirectionCarrierIsP2P3 =
        refl
    ; canonicalRightDirection =
        p2RightDirection
    ; canonicalRightDirectionIsP2 =
        refl
    ; canonicalUpDirection =
        p3UpDirection
    ; canonicalUpDirectionIsP3 =
        refl
    ; canonicalDirectionsIndependent =
        p2RightDirection≠p3UpDirection
    ; sufficientSchema =
        RequiredDirectionIndexedSFGCSchemaExtension SFGC.GaugeField
    ; sufficientSchemaIsDirectionIndexedExtension =
        refl
    ; sufficientConstructorName =
        "directionIndexedSchemaYieldsDiscreteCurvatureCarrier"
    ; sufficientConstructorTarget =
        "RequiredDirectionIndexedSFGCSchemaExtension SFGC.GaugeField -> DiscreteCurvatureCarrier SFGC.GaugeField"
    ; localAdoptionWrapperName =
        "directionIndexedSchemaAdoptionWrapper"
    ; localAdoptionWrapperTarget =
        "RequiredDirectionIndexedSFGCSchemaExtension SFGC.GaugeField -> DirectionIndexedSFGCAdoptionWrapper SFGC.GaugeField"
    ; conditionalFieldStrengthWrapperName =
        "fieldStrengthFromDirectionIndexedCurvature"
    ; currentCoreAdoptionAvailable =
        false
    ; currentCoreAdoptionAvailableIsFalse =
        refl
    ; nextBlocker =
        missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
    ; nextFieldStrengthBlocker =
        missingFieldStrengthFromCurvature
    ; exactCoreFieldsRequired =
        "SFGCSite, replacing or extending the current three-point ShiftPressurePoint process carrier"
        ∷ "SFGCPrimeDirection with p2/right and p3/up constructors, or an equivalent Prime-indexed direction carrier"
        ∷ "SFGCShiftEdge : PrimeDirection -> SFGCSite -> Set"
        ∷ "shiftAction : PrimeDirection -> SFGCSite -> SFGCSite"
        ∷ "rightEdgeAt : site -> SFGCShiftEdge p2Right site"
        ∷ "upEdgeAt : site -> SFGCShiftEdge p3Up site"
        ∷ "p2Right != p3Up and p2/p3 shift commutation laws"
        ∷ "connectionTo1Form/evaluate1 for direction-indexed links"
        ∷ "boundaryOfBoundaryZero on nondegenerate p2-p3 plaquettes"
        ∷ "fieldStrengthFromCurvature consumer accepted by the G2 gate"
        ∷ []
    ; schemaBoundary =
        "This file now contains the minimal direction-indexed p2/right and p3/up schema surface"
        ∷ "The surface is sufficient: supplying the schema yields DiscreteCurvatureCarrier through the existing constructor"
        ∷ "The local adoption wrapper packages that conditional carrier and exposes fieldStrengthFromCurvature when the schema is supplied"
        ∷ "No core SFGC module was changed, so no actual SFGC.GaugeField carrier is promoted here"
        ∷ "The next blocker is core adoption of SFGCShiftEdge/shiftAction plus the field-strength-from-curvature consumer"
        ∷ []
    }

record G2NondegeneratePlaquetteSchemaReceipt : Set₂ where
  field
    status :
      G2NondegeneratePlaquetteSchemaStatus

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierIsSFGC :
      inspectedConnectionCarrier ≡ SFGC.GaugeField

    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    inspectedRightEdge :
      Set

    inspectedRightEdgeIsCurrentG2RightEdge :
      inspectedRightEdge ≡ G2DCC.SFGCShiftRightEdge

    inspectedRightTarget :
      G2DCC.SFGCShiftRightEdge →
      SPTI.ShiftPressurePoint

    inspectedRightTargetLaw :
      (edge : G2DCC.SFGCShiftRightEdge) →
      inspectedRightTarget edge ≡ SSL.rightNeighbor edge

    availableRightEdgeBridge :
      G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge

    availableReturnPlaquetteSurface :
      G2DCC.SFGCShiftRightEdgePlaquetteNormalizerSurface

    availableTwoStepReturnSurface :
      G2DCC.SFGCShiftRightEdgeTwoStepPlaquetteSurface

    availableMinimalUOneSystem :
      G2U1.DiscreteUOneConnectionSystem SFGC.GaugeField

    existingTransverseEdgeRequest :
      G2TE.G2SFGCTransverseEdgeAPIRequest

    directionIndexedSchemaExtensionReceipt :
      G2DirectionIndexedSchemaExtensionReceipt

    firstMissing :
      G2NondegeneratePlaquetteSchemaMissing

    missingFields :
      List G2NondegeneratePlaquetteSchemaMissing

    requiredNewFieldNames :
      List String

    sufficientConstructorName :
      String

    sufficientConstructorTarget :
      String

    exactMissingConstructor :
      String

    exactMissingConstructorShape :
      String

    rejectedPromotion :
      String

    receiptBoundary :
      List String

canonicalG2NondegeneratePlaquetteSchemaReceipt :
  G2NondegeneratePlaquetteSchemaReceipt
canonicalG2NondegeneratePlaquetteSchemaReceipt =
  record
    { status =
        blockedBySingleRightEdgeOnly
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierIsSFGC =
        refl
    ; inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsShiftPressurePoint =
        refl
    ; inspectedRightEdge =
        G2DCC.SFGCShiftRightEdge
    ; inspectedRightEdgeIsCurrentG2RightEdge =
        refl
    ; inspectedRightTarget =
        G2DCC.sfgcShiftRightEdgeTarget
    ; inspectedRightTargetLaw =
        λ edge → refl
    ; availableRightEdgeBridge =
        G2DCC.canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; availableReturnPlaquetteSurface =
        G2DCC.canonicalSFGCShiftRightEdgePlaquetteNormalizerSurface
    ; availableTwoStepReturnSurface =
        G2DCC.canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface
    ; availableMinimalUOneSystem =
        G2U1.canonicalSFGCDiscreteUOneConnectionSystem
    ; existingTransverseEdgeRequest =
        G2TE.canonicalG2SFGCTransverseEdgeAPIRequest
    ; directionIndexedSchemaExtensionReceipt =
        canonicalG2DirectionIndexedSchemaExtensionReceipt
    ; firstMissing =
        missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
    ; missingFields =
        missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
        ∷ missingDirectionIndexedEdgeAction
        ∷ missingNondegenerateTwoCellBoundary
        ∷ missingPlaquetteCommutationLaw
        ∷ missingBoundaryOfBoundaryZeroForPlaquettes
        ∷ missingFieldStrengthFromCurvature
        ∷ []
    ; requiredNewFieldNames =
        "SFGCPrimeDirection with p2RightDirection and p3UpDirection plus independentDirections"
        ∷ "edgeAt : Direction -> ShiftPressurePoint -> Edge"
        ∷ "shiftAction : Direction -> ShiftPressurePoint -> ShiftPressurePoint"
        ∷ "four plaquette vertices SW/SE/NE/NW and bottom/right/top/left edges"
        ∷ "signedPlaquetteBoundary = +bottom,+right,-top,-left"
        ∷ "plaquetteCommutes : transverse(right base) == right(transverse base)"
        ∷ "boundaryOfBoundaryZero : δ1 (δ0 f) == φ0 on every plaquette"
        ∷ "fieldStrengthFromCurvature : Discrete2Form -> FieldStrengthCarrier"
        ∷ []
    ; sufficientConstructorName =
        "discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI"
    ; sufficientConstructorTarget =
        "RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField -> DiscreteCurvatureCarrier SFGC.GaugeField"
    ; exactMissingConstructor =
        "SFGCShiftTransverseEdge / direction-indexed SFGCShiftEdge"
    ; exactMissingConstructorShape =
        "a second oriented edge action over ShiftPressurePoint with source/target laws independent of SSL.rightNeighbor"
    ; rejectedPromotion =
        "DiscreteCurvatureCarrier SFGC.GaugeField"
    ; receiptBoundary =
        "The current SFGC API supports a Phase4-valued right-edge 1-form over ShiftPressurePoint"
        ∷ "The only concrete edge target is SSL.rightNeighbor; there is no independent transverse direction or direction-indexed edge action"
        ∷ "Return plaquettes are degenerate normalizers and cannot witness nonzero or nondegenerate curvature"
        ∷ "The sufficient constructor is now typed: any real RequiredNondegenerateSFGCPlaquetteAPI immediately yields DiscreteCurvatureCarrier"
        ∷ "The direction-indexed schema surface is now typed locally, with p2/right and p3/up named explicitly"
        ∷ "Core adoption is still required before the G2 carrier constructor can be used honestly"
        ∷ "No DiscreteCurvatureCarrier SFGC.GaugeField is constructed by this module"
        ∷ []
    }

g2NondegeneratePlaquetteFirstMissing :
  G2NondegeneratePlaquetteSchemaReceipt.firstMissing
    canonicalG2NondegeneratePlaquetteSchemaReceipt
  ≡
  missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
g2NondegeneratePlaquetteFirstMissing =
  refl

g2NondegeneratePlaquetteExactMissingConstructor :
  G2NondegeneratePlaquetteSchemaReceipt.exactMissingConstructor
    canonicalG2NondegeneratePlaquetteSchemaReceipt
  ≡
  "SFGCShiftTransverseEdge / direction-indexed SFGCShiftEdge"
g2NondegeneratePlaquetteExactMissingConstructor =
  refl

module DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2NondegeneratePlaquetteSchema as G2NPS
import DASHI.Physics.Closure.G2SFGCAsUOnePrimeLattice as G2U1
import DASHI.Physics.Closure.G2TransverseEdgeAPI as G2TE
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- Bounded G2/SFGC schema extension.
--
-- This module is a request/adoption sidecar.  It does not edit the core SFGC
-- carrier and it does not construct a DiscreteCurvatureCarrier for
-- SFGC.GaugeField.  A carrier is exposed only conditionally from a supplied
-- direction-indexed, nondegenerate p2/p3 plaquette schema.

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data G2SFGCPrimeDirection : Set where
  p2Right :
    G2SFGCPrimeDirection

  p3Transverse :
    G2SFGCPrimeDirection

p2Right≠p3Transverse :
  p2Right ≠ p3Transverse
p2Right≠p3Transverse ()

data CurrentSFGCRightEdgeAt
  (site : SPTI.ShiftPressurePoint) : Set where
  currentSFGCRightEdge :
    CurrentSFGCRightEdgeAt site

record CurrentSFGCRightEdgeAdapter : Set₁ where
  field
    Site :
      Set

    RightEdge :
      Site →
      Set

    rightShiftAction :
      Site →
      Site

    rightEdgeAt :
      (site : Site) →
      RightEdge site

    rightEdgeSource :
      {site : Site} →
      RightEdge site →
      Site

    rightEdgeTarget :
      {site : Site} →
      RightEdge site →
      Site

    rightEdgeSourceLaw :
      (site : Site) →
      (edge : RightEdge site) →
      rightEdgeSource edge ≡ site

    rightEdgeTargetLaw :
      (site : Site) →
      (edge : RightEdge site) →
      rightEdgeTarget edge ≡ rightShiftAction site

    connectionToRightEdge1Form :
      SFGC.GaugeField →
      (site : Site) →
      RightEdge site →
      SPTI4.Phase4

    vacuumRightEdgeZero :
      (site : Site) →
      (edge : RightEdge site) →
      connectionToRightEdge1Form SFGC.vacuumGaugeField site edge
        ≡
      SPTI4.φ0

    adapterBoundary :
      List String

canonicalCurrentSFGCRightEdgeAdapter :
  CurrentSFGCRightEdgeAdapter
canonicalCurrentSFGCRightEdgeAdapter =
  record
    { Site =
        SPTI.ShiftPressurePoint
    ; RightEdge =
        CurrentSFGCRightEdgeAt
    ; rightShiftAction =
        SSL.rightNeighbor
    ; rightEdgeAt =
        λ site → currentSFGCRightEdge
    ; rightEdgeSource =
        λ {site} edge → site
    ; rightEdgeTarget =
        λ {site} edge → SSL.rightNeighbor site
    ; rightEdgeSourceLaw =
        λ site edge → refl
    ; rightEdgeTargetLaw =
        λ site edge → refl
    ; connectionToRightEdge1Form =
        λ A site edge →
          G2DCC.connectionToShiftRightEdge1Form A site
    ; vacuumRightEdgeZero =
        λ site edge →
          G2DCC.vacuumShiftRightEdge1FormZero site
    ; adapterBoundary =
        "Backwards-compatible adapter only for the existing SFGC right edge"
        ∷ "Site is ShiftPressurePoint and rightShiftAction is SSL.rightNeighbor"
        ∷ "RightEdge is the current G2DCC.SFGCShiftRightEdge anchor, sampled by connectionToShiftRightEdge1Form"
        ∷ "No p3/transverse edge, nondegenerate plaquette, or DiscreteCurvatureCarrier is constructed by this adapter"
        ∷ []
    }

data G2SFGCGaugeFieldSchemaExtensionStatus : Set where
  requestSurfaceAvailableCoreSchemaStillBlocked :
    G2SFGCGaugeFieldSchemaExtensionStatus

  coreDirectionIndexedSchemaAdopted :
    G2SFGCGaugeFieldSchemaExtensionStatus

data G2SFGCGaugeFieldSchemaExtensionMissing : Set where
  noRemainingG2SFGCSchemaExtensionMissing :
    G2SFGCGaugeFieldSchemaExtensionMissing

  missingCoreDirectionIndexedSFGCShiftEdge :
    G2SFGCGaugeFieldSchemaExtensionMissing

  missingTransverseP3SFGCLink :
    G2SFGCGaugeFieldSchemaExtensionMissing

  missingP2P3PlaquetteEndpointLaws :
    G2SFGCGaugeFieldSchemaExtensionMissing

  missingP2P3BoundaryOfBoundaryZero :
    G2SFGCGaugeFieldSchemaExtensionMissing

  missingFieldStrengthFromCurvature :
    G2SFGCGaugeFieldSchemaExtensionMissing

record DirectionIndexedSFGCEdgeRequest : Set₁ where
  field
    Site :
      Set

    Direction :
      Set

    rightDirection :
      Direction

    transverseP3Direction :
      Direction

    right≠transverseP3 :
      rightDirection ≠ transverseP3Direction

    SFGCShiftEdge :
      Direction →
      Site →
      Set

    shiftAction :
      Direction →
      Site →
      Site

    edgeSource :
      {dir : Direction} →
      {site : Site} →
      SFGCShiftEdge dir site →
      Site

    edgeTarget :
      {dir : Direction} →
      {site : Site} →
      SFGCShiftEdge dir site →
      Site

    edgeSourceLaw :
      {dir : Direction} →
      (site : Site) →
      (edge : SFGCShiftEdge dir site) →
      edgeSource edge ≡ site

    edgeTargetLaw :
      {dir : Direction} →
      (site : Site) →
      (edge : SFGCShiftEdge dir site) →
      edgeTarget edge ≡ shiftAction dir site

    currentRightLinkAt :
      (site : Site) →
      SFGCShiftEdge rightDirection site

    transverseP3LinkAt :
      (site : Site) →
      SFGCShiftEdge transverseP3Direction site

    p2ThenP3 :
      Site →
      Site

    p3ThenP2 :
      Site →
      Site

    p2ThenP3Law :
      (site : Site) →
      p2ThenP3 site
        ≡
      shiftAction transverseP3Direction (shiftAction rightDirection site)

    p3ThenP2Law :
      (site : Site) →
      p3ThenP2 site
        ≡
      shiftAction rightDirection (shiftAction transverseP3Direction site)

    p2p3Commutes :
      (site : Site) →
      p2ThenP3 site ≡ p3ThenP2 site

    adoptionBoundary :
      List String

canonicalSFGCSite2DDirectionIndexedEdgeRequest :
  DirectionIndexedSFGCEdgeRequest
canonicalSFGCSite2DDirectionIndexedEdgeRequest =
  record
    { Site =
        SFGC.SFGCSite2D
    ; Direction =
        SFGC.SFGCPrimeDirection
    ; rightDirection =
        SFGC.p2Right
    ; transverseP3Direction =
        SFGC.p3Transverse
    ; right≠transverseP3 =
        SFGC.p2Right≠p3Transverse
    ; SFGCShiftEdge =
        SFGC.SFGCSite2DShiftEdge
    ; shiftAction =
        λ
          { SFGC.p2Right →
              SFGC.sfgcSite2DP2ShiftAction
          ; SFGC.p3Transverse →
              SFGC.sfgcSite2DP3ShiftAction
          }
    ; edgeSource =
        SFGC.sfgcSite2DEdgeSource
    ; edgeTarget =
        SFGC.sfgcSite2DEdgeTarget
    ; edgeSourceLaw =
        SFGC.sfgcSite2DEdgeSourceLaw
    ; edgeTargetLaw =
        λ site →
          λ
            { (SFGC.sfgcSite2DP2RightEdgeAt .site) →
                refl
            ; (SFGC.sfgcSite2DP3TransverseEdgeAt .site) →
                refl
            }
    ; currentRightLinkAt =
        SFGC.sfgcSite2DP2RightEdgeAt
    ; transverseP3LinkAt =
        SFGC.sfgcSite2DP3TransverseEdgeAt
    ; p2ThenP3 =
        SFGC.sfgcSite2DP2ThenP3
    ; p3ThenP2 =
        SFGC.sfgcSite2DP3ThenP2
    ; p2ThenP3Law =
        SFGC.sfgcSite2DP2ThenP3Law
    ; p3ThenP2Law =
        SFGC.sfgcSite2DP3ThenP2Law
    ; p2p3Commutes =
        SFGC.sfgcSite2DP2P3EndpointCommutation
    ; adoptionBoundary =
        "Consumes SFGC.canonicalSFGCSite2DMinimalP3SemanticExtension as a direction-indexed edge request"
        ∷ "Site is SFGC.SFGCSite2D, not the old three-point ShiftPressurePoint carrier"
        ∷ "p2/right and p3/transverse links are separate constructors over the 2D site carrier"
        ∷ "p2/p3 endpoint commutation is definitional because the actions advance independent axes"
        ∷ "This is not yet a RequiredNondegenerateSFGCPlaquetteAPI or DiscreteCurvatureCarrier"
        ∷ []
    }

canonicalCoreDirectionIndexedSFGCEdgeRequest :
  DirectionIndexedSFGCEdgeRequest
canonicalCoreDirectionIndexedSFGCEdgeRequest =
  record
    { Site =
        SFGC.CanonicalCoreDirectionIndexedSFGCSite
    ; Direction =
        SFGC.SFGCPrimeDirection
    ; rightDirection =
        SFGC.p2Right
    ; transverseP3Direction =
        SFGC.p3Transverse
    ; right≠transverseP3 =
        SFGC.p2Right≠p3Transverse
    ; SFGCShiftEdge =
        SFGC.CanonicalCoreDirectionIndexedSFGCShiftEdge
    ; shiftAction =
        SFGC.CoreDirectionIndexedSFGCSchema.coreShiftAction
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; edgeSource =
        SFGC.CoreDirectionIndexedSFGCSchema.coreEdgeSource
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; edgeTarget =
        SFGC.CoreDirectionIndexedSFGCSchema.coreEdgeTarget
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; edgeSourceLaw =
        SFGC.CoreDirectionIndexedSFGCSchema.coreEdgeSourceLaw
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; edgeTargetLaw =
        SFGC.CoreDirectionIndexedSFGCSchema.coreEdgeTargetLaw
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; currentRightLinkAt =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP2RightLinkAt
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; transverseP3LinkAt =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP3TransverseLinkAt
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; p2ThenP3 =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP2ThenP3
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; p3ThenP2 =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP3ThenP2
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; p2ThenP3Law =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP2ThenP3Law
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; p3ThenP2Law =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP3ThenP2Law
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; p2p3Commutes =
        SFGC.CoreDirectionIndexedSFGCSchema.coreP2P3EndpointCommutation
          SFGC.canonicalCoreDirectionIndexedSFGCSchema
    ; adoptionBoundary =
        "Consumes SFGC.canonicalCoreDirectionIndexedSFGCSchema as the core-facing direction-indexed edge request"
        ∷ "The adopted core site is SFGC.CanonicalCoreDirectionIndexedSFGCSite, definitionally SFGC.SFGCSite2D"
        ∷ "The adopted core edge family has inhabited p2/right and p3/transverse links"
        ∷ "The legacy SFGC.SFGCSite and SFGC.SFGCShiftEdge names remain right-only compatibility surfaces"
        ∷ []
    }

record DirectionIndexedSFGCGaugeFieldSchema
  (ConnectionCarrier : Set) : Set₁ where
  field
    edgeRequest :
      DirectionIndexedSFGCEdgeRequest

    plaquetteSchema :
      G2NPS.RequiredNondegenerateSFGCPlaquetteAPI ConnectionCarrier

    schemaSiteMatchesEdgeRequest :
      G2NPS.RequiredNondegenerateSFGCPlaquetteAPI.Site plaquetteSchema
        ≡
      DirectionIndexedSFGCEdgeRequest.Site edgeRequest

    schemaDirectionMatchesEdgeRequest :
      G2NPS.RequiredNondegenerateSFGCPlaquetteAPI.Direction plaquetteSchema
        ≡
      DirectionIndexedSFGCEdgeRequest.Direction edgeRequest

    schemaRightDirectionIsP2 :
      String

    schemaTransverseDirectionIsP3 :
      String

    schemaBoundary :
      List String

canonicalSFGCSite2DRequiredNondegeneratePlaquetteAPI :
  G2NPS.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField
canonicalSFGCSite2DRequiredNondegeneratePlaquetteAPI =
  record
    { Site =
        SFGC.SFGCSite2D
    ; Direction =
        SFGC.SFGCPrimeDirection
    ; rightDirection =
        SFGC.p2Right
    ; transverseDirection =
        SFGC.p3Transverse
    ; independentDirections =
        SFGC.p2Right≠p3Transverse
    ; Edge =
        SFGC.SFGCSite2DEdge
    ; edgeAt =
        SFGC.sfgcSite2DEdgeAt
    ; edgeSource =
        SFGC.sfgcSite2DEdgeSourceTotal
    ; edgeTarget =
        SFGC.sfgcSite2DEdgeTargetTotal
    ; edgeSourceLaw =
        SFGC.sfgcSite2DEdgeAtSourceLaw
    ; shiftAction =
        SFGC.sfgcSite2DShiftAction
    ; edgeTargetLaw =
        SFGC.sfgcSite2DEdgeAtTargetLaw
    ; Plaquette =
        SFGC.SFGCSite2DPlaquette
    ; plaquetteAt =
        SFGC.sfgcSite2DPlaquetteAt
    ; southwest =
        SFGC.sfgcSite2DPlaquetteSW
    ; southeast =
        SFGC.sfgcSite2DPlaquetteSE
    ; northeast =
        SFGC.sfgcSite2DPlaquetteNE
    ; northwest =
        SFGC.sfgcSite2DPlaquetteNW
    ; bottomEdge =
        SFGC.sfgcSite2DPlaquetteBottomEdge
    ; rightEdge =
        SFGC.sfgcSite2DPlaquetteRightEdge
    ; topEdge =
        SFGC.sfgcSite2DPlaquetteTopEdge
    ; leftEdge =
        SFGC.sfgcSite2DPlaquetteLeftEdge
    ; bottomSourceLaw =
        SFGC.sfgcSite2DPlaquetteBottomSourceLaw
    ; bottomTargetLaw =
        SFGC.sfgcSite2DPlaquetteBottomTargetLaw
    ; rightSourceLaw =
        SFGC.sfgcSite2DPlaquetteRightSourceLaw
    ; rightTargetLaw =
        SFGC.sfgcSite2DPlaquetteRightTargetLaw
    ; topSourceLaw =
        SFGC.sfgcSite2DPlaquetteTopSourceLaw
    ; topTargetLaw =
        SFGC.sfgcSite2DPlaquetteTopTargetLaw
    ; leftSourceLaw =
        SFGC.sfgcSite2DPlaquetteLeftSourceLaw
    ; leftTargetLaw =
        SFGC.sfgcSite2DPlaquetteLeftTargetLaw
    ; plaquetteCommutes =
        SFGC.sfgcSite2DP2P3EndpointCommutation
    ; signedPlaquetteBoundary =
        λ plaquette →
          G2DCC.correctedSquareBoundary
            (SFGC.sfgcSite2DPlaquetteBottomEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteRightEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteTopEdge plaquette)
            (SFGC.sfgcSite2DPlaquetteLeftEdge plaquette)
    ; signedPlaquetteBoundaryIsCorrectedSquare =
        λ base → refl
    ; Discrete0Form =
        SFGC.SFGCSite2DDiscrete0Form
    ; Discrete1Form =
        SFGC.SFGCSite2DDiscrete1Form
    ; Discrete2Form =
        SFGC.SFGCSite2DDiscrete2Form
    ; connectionTo1Form =
        SFGC.sfgcSite2DConnectionTo1Form
    ; evaluate1 =
        SFGC.sfgcSite2DEvaluate1
    ; evaluate2 =
        SFGC.sfgcSite2DEvaluate2
    ; δ₀ =
        SFGC.sfgcSite2Dδ₀
    ; δ₁ =
        SFGC.sfgcSite2Dδ₁
    ; boundaryOfBoundaryZero =
        SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero
    ; vacuumConnection =
        SFGC.vacuumGaugeField
    ; vacuumFlatness =
        SFGC.sfgcSite2DVacuumWilsonLoopFlatness
    ; FieldStrengthCarrier =
        SFGC.SFGCSite2DFieldStrengthBridge
    ; fieldStrengthFromCurvature =
        SFGC.sfgcSite2DFieldStrengthFromCurvature
    ; schemaBoundary =
        "Canonical sidecar schema over SFGC.SFGCSite2D, not over the old ShiftPressurePoint SFGCSite alias"
        ∷ "Plaquette boundary is +bottom,+right,-top,-left over separate p2/right and p3/transverse edges"
        ∷ "p2/p3 endpoint commutation is supplied by SFGC.sfgcSite2DP2P3EndpointCommutation"
        ∷ "boundaryOfBoundaryZero is SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero for exact 0-form boundaries"
        ∷ "Curvature of connection 1-forms is evaluated as the Wilson-loop phase around the p2/p3 plaquette"
        ∷ "Field strength is bridged by SFGC.sfgcSite2DFieldStrengthFromCurvature"
        ∷ []
    }

canonicalSFGCSite2DGaugeFieldSchema :
  DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField
canonicalSFGCSite2DGaugeFieldSchema =
  record
    { edgeRequest =
        canonicalCoreDirectionIndexedSFGCEdgeRequest
    ; plaquetteSchema =
        canonicalSFGCSite2DRequiredNondegeneratePlaquetteAPI
    ; schemaSiteMatchesEdgeRequest =
        refl
    ; schemaDirectionMatchesEdgeRequest =
        refl
    ; schemaRightDirectionIsP2 =
        "SFGC.p2Right is the p2/right direction in canonicalSFGCSite2DDirectionIndexedEdgeRequest"
    ; schemaTransverseDirectionIsP3 =
        "SFGC.p3Transverse is the p3/transverse direction in canonicalSFGCSite2DDirectionIndexedEdgeRequest"
    ; schemaBoundary =
        "This schema consumes the core-facing p2/p3 edge request adopted from SFGCSite2D"
        ∷ "It supplies the nondegenerate p2/p3 plaquette boundary, boundary-of-boundary-zero law, vacuum flatness, and Wilson-loop field-strength bridge"
        ∷ "Legacy SFGC.SFGCSite/SFGCShiftEdge names remain right-only compatibility surfaces; direction-indexed core consumers use SFGC.CoreDirectionIndexedSFGCSchema"
        ∷ []
    }

schemaYieldsDiscreteCurvatureCarrier :
  {ConnectionCarrier : Set} →
  DirectionIndexedSFGCGaugeFieldSchema ConnectionCarrier →
  G2DCC.DiscreteCurvatureCarrier ConnectionCarrier
schemaYieldsDiscreteCurvatureCarrier schema =
  G2NPS.discreteCurvatureCarrierFromRequiredNondegenerateSFGCPlaquetteAPI
    (DirectionIndexedSFGCGaugeFieldSchema.plaquetteSchema schema)

schemaYieldsFieldStrengthFromCurvature :
  {ConnectionCarrier : Set} →
  (schema : DirectionIndexedSFGCGaugeFieldSchema ConnectionCarrier) →
  G2DCC.DiscreteCurvatureCarrier.CurvatureCarrier
    (schemaYieldsDiscreteCurvatureCarrier schema) →
  G2DCC.DiscreteCurvatureCarrier.FieldStrengthCarrier
    (schemaYieldsDiscreteCurvatureCarrier schema)
schemaYieldsFieldStrengthFromCurvature schema =
  G2DCC.DiscreteCurvatureCarrier.curvatureToFieldStrength
    (schemaYieldsDiscreteCurvatureCarrier schema)

record ConditionalSFGCGaugeFieldCarrierAdoption : Set₁ where
  field
    suppliedSchema :
      DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField

    adoptedCarrier :
      G2DCC.DiscreteCurvatureCarrier SFGC.GaugeField

    adoptedCarrierIsSchemaCarrier :
      adoptedCarrier ≡ schemaYieldsDiscreteCurvatureCarrier suppliedSchema

    adoptedFieldStrengthFromCurvature :
      G2DCC.DiscreteCurvatureCarrier.CurvatureCarrier adoptedCarrier →
      G2DCC.DiscreteCurvatureCarrier.FieldStrengthCarrier adoptedCarrier

    carrierBoundary :
      List String

adoptSFGCGaugeFieldCarrierFromSchema :
  DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField →
  ConditionalSFGCGaugeFieldCarrierAdoption
adoptSFGCGaugeFieldCarrierFromSchema schema =
  record
    { suppliedSchema =
        schema
    ; adoptedCarrier =
        schemaYieldsDiscreteCurvatureCarrier schema
    ; adoptedCarrierIsSchemaCarrier =
        refl
    ; adoptedFieldStrengthFromCurvature =
        schemaYieldsFieldStrengthFromCurvature schema
    ; carrierBoundary =
        "Conditional only: adoption requires an inhabited direction-indexed p2/p3 SFGC schema"
        ∷ "No canonical SFGC.GaugeField DiscreteCurvatureCarrier is constructed in this module"
        ∷ []
    }

record CoreDirectionIndexedSFGCShiftEdgeBlocker : Set₁ where
  field
    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    inspectedShiftPressurePointConstructors :
      List String

    inspectedShiftPressurePointEndpointStructure :
      List String

    currentSiteCarrierHasPrimeCoordinates :
      Bool

    currentSiteCarrierHasPrimeCoordinatesIsFalse :
      currentSiteCarrierHasPrimeCoordinates ≡ false

    inspectedGaugeFieldShape :
      String

    inspectedCoreRightLinkShape :
      String

    inspectedCoreP3TransverseEdgeUninhabited :
      (site : SFGC.SFGCSite) →
      SFGC.SFGCShiftEdge SFGC.p3Transverse site →
      ⊥

    coreTransverseP3LinkUpstreamAPIRequest :
      SFGC.SFGCTransverseP3LinkUpstreamAPIRequest

    coreThreePointP3ActionObstruction :
      SFGC.SFGCThreePointP3ActionObstruction

    firstMissing :
      G2SFGCGaugeFieldSchemaExtensionMissing

    smallestCoreAPIName :
      String

    smallestCoreAPIShape :
      String

    minimalSemanticExtensionAPIName :
      String

    requiredFailClosedAdoption :
      List String

    forbiddenCoreAssumptions :
      List String

    blockerBoundary :
      List String

canonicalCoreDirectionIndexedSFGCShiftEdgeBlocker :
  CoreDirectionIndexedSFGCShiftEdgeBlocker
canonicalCoreDirectionIndexedSFGCShiftEdgeBlocker =
  record
    { inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsShiftPressurePoint =
        refl
    ; inspectedShiftPressurePointConstructors =
        "shiftStartPoint"
        ∷ "shiftNextPoint"
        ∷ "shiftHeldExitPoint"
        ∷ []
    ; inspectedShiftPressurePointEndpointStructure =
        "Definition site: DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance defines ShiftPressurePoint with constructors shiftStartPoint, shiftNextPoint, shiftHeldExitPoint"
        ∷ "ShiftPressurePoint is a data type, not a record"
        ∷ "No endpoint, source, target, p3 coordinate, or prime projection field is available"
        ∷ "Definition site: DASHI.Physics.ShiftSpatialLaplacian exports leftNeighbor/rightNeighbor only, with rightNeighbor shiftStartPoint = shiftNextPoint, shiftNextPoint = shiftHeldExitPoint, shiftHeldExitPoint = shiftHeldExitPoint"
        ∷ "The current endpoint structure comes only from SFGC.sfgcShiftEdgeTarget on inhabited edges"
        ∷ []
    ; currentSiteCarrierHasPrimeCoordinates =
        false
    ; currentSiteCarrierHasPrimeCoordinatesIsFalse =
        refl
    ; inspectedGaugeFieldShape =
        "GaugeField = ShiftPressurePoint -> Phase4"
    ; inspectedCoreRightLinkShape =
        "Definition site: SFGCShiftEdge has constructor sfgcP2RightEdgeAt : (site : SFGCSite) -> SFGCShiftEdge p2Right site; sfgcShiftEdgeTarget maps it to SSL.rightNeighbor site"
    ; inspectedCoreP3TransverseEdgeUninhabited =
        SFGC.sfgcP3TransverseShiftEdgeMissing
    ; coreTransverseP3LinkUpstreamAPIRequest =
        SFGC.canonicalSFGCTransverseP3LinkUpstreamAPIRequest
    ; coreThreePointP3ActionObstruction =
        SFGC.canonicalSFGCThreePointP3ActionObstruction
    ; firstMissing =
        missingTransverseP3SFGCLink
    ; smallestCoreAPIName =
        "legacyTransverseP3LinkAt"
    ; smallestCoreAPIShape =
        "(site : SFGC.SFGCSite) -> SFGC.SFGCShiftEdge SFGC.p3Transverse site, plus p3 shiftAction endpoint law, if the legacy ShiftPressurePoint surface itself is ever widened"
    ; minimalSemanticExtensionAPIName =
        SFGC.minimalP3SemanticExtensionAPIName
    ; requiredFailClosedAdoption =
        "Core now exposes SFGCPrimeDirection and SFGCShiftEdge with the p2/right edge inhabited"
        ∷ "Definition-site evidence: ShiftPressurePoint currently has only shiftStartPoint, shiftNextPoint, and shiftHeldExitPoint; no independent p3 coordinate or transverse action is exported"
        ∷ "Definition-site evidence: SFGCShiftEdge currently has no constructor targeting SFGCShiftEdge p3Transverse site"
        ∷ "Definition-site evidence: SSL.leftNeighbor fails p2/p3 endpoint commutation at shiftStartPoint and cannot be p3Transverse"
        ∷ "Do not assume ShiftPressurePoint has record fields or endpoint projections; add an explicit p3 action/link API instead"
        ∷ "The exact upstream API request is SFGC.canonicalSFGCTransverseP3LinkUpstreamAPIRequest"
        ∷ "The narrowest typed semantic-extension request is SFGC.SFGCMinimalP3SemanticExtensionAPI"
        ∷ "Expose a real p3 transverse shiftAction that is not SSL.rightNeighbor reused under another name"
        ∷ "Expose transverseP3LinkAt : (site : SFGCSite) -> SFGCShiftEdge p3Transverse site"
        ∷ "Expose edgeTarget law for the p3 transverse edge"
        ∷ "Expose p2ThenP3/p3ThenP2 endpoint laws and their commutation before any plaquette carrier adoption"
        ∷ "The p3 action must not be identity or collapse-only on the current three-point carrier because both are degenerate"
        ∷ []
    ; forbiddenCoreAssumptions =
        "No field such as source, target, prime, coordinate, p3, or endpoint may be projected from ShiftPressurePoint"
        ∷ "No p3 transverse link may be synthesized by relabeling SSL.rightNeighbor, SSL.leftNeighbor, or the current p2 edge"
        ∷ "No p3 transverse action may be synthesized by identity or collapse-only endomaps on the current three-point carrier"
        ∷ "No DiscreteCurvatureCarrier adoption is valid from the legacy right-only SFGCShiftEdge surface alone"
        ∷ []
    ; blockerBoundary =
        "Legacy-only blocker: the old SFGCShiftEdge surface has an inhabited p2/right edge but no inhabited p3/transverse edge"
        ∷ "This blocker is witnessed by SFGC.sfgcP3TransverseShiftEdgeMissing for the legacy ShiftPressurePoint carrier"
        ∷ "The existing right-neighbor edge cannot be reused as p3 without collapsing the required nondegenerate plaquette"
        ∷ "Core direction-indexed consumers should use SFGC.canonicalCoreDirectionIndexedSFGCSchema instead of this legacy right-only surface"
        ∷ []
    }

record G2SFGCGaugeFieldSchemaExtensionReceipt : Set₂ where
  field
    status :
      G2SFGCGaugeFieldSchemaExtensionStatus

    inspectedGaugeField :
      Set

    inspectedGaugeFieldIsSFGC :
      inspectedGaugeField ≡ SFGC.GaugeField

    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsCurrentShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    coefficientCarrier :
      Set

    coefficientCarrierIsPhase4 :
      coefficientCarrier ≡ SPTI4.Phase4

    requestedDirectionCarrier :
      Set

    requestedDirectionCarrierIsP2P3 :
      requestedDirectionCarrier ≡ G2SFGCPrimeDirection

    requestedRightDirection :
      G2SFGCPrimeDirection

    requestedRightDirectionIsP2 :
      requestedRightDirection ≡ p2Right

    requestedTransverseDirection :
      G2SFGCPrimeDirection

    requestedTransverseDirectionIsP3 :
      requestedTransverseDirection ≡ p3Transverse

    requestedDirectionsIndependent :
      requestedRightDirection ≠ requestedTransverseDirection

    currentTransverseEdgeAudit :
      G2TE.G2SFGCTransverseEdgeAPIRequest

    currentUOneAudit :
      G2U1.G2SFGCAsUOnePrimeLatticeDiagnostic

    currentRightOnlyAdapter :
      CurrentSFGCRightEdgeAdapter

    legacyRightOnlyCoreEdgeBlocker :
      CoreDirectionIndexedSFGCShiftEdgeBlocker

    coreTransverseP3LinkUpstreamAPIRequest :
      SFGC.SFGCTransverseP3LinkUpstreamAPIRequest

    coreThreePointP3ActionObstruction :
      SFGC.SFGCThreePointP3ActionObstruction

    site2DSemanticExtension :
      SFGC.SFGCMinimalP3SemanticExtensionAPI

    site2DDirectionIndexedEdgeRequest :
      DirectionIndexedSFGCEdgeRequest

    coreDirectionIndexedAdoptionReceipt :
      SFGC.SFGCSite2DCoreDirectionIndexedAdoptionReceipt

    coreDirectionIndexedEdgeRequest :
      DirectionIndexedSFGCEdgeRequest

    sufficientSchemaSurface :
      Set₁

    sufficientSchemaSurfaceIsGaugeFieldSchema :
      sufficientSchemaSurface
        ≡
      DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField

    conditionalAdoptionConstructorName :
      String

    conditionalAdoptionConstructorTarget :
      String

    coreAdoptionAvailable :
      Bool

    coreAdoptionAvailableIsTrue :
      coreAdoptionAvailable ≡ true

    firstMissing :
      G2SFGCGaugeFieldSchemaExtensionMissing

    remainingMissing :
      List G2SFGCGaugeFieldSchemaExtensionMissing

    exactCoreSchemaBlocker :
      String

    exactRequiredCoreAPI :
      List String

    exactForbiddenAssumptions :
      List String

    rightOnlyAdapterCannotAdoptReason :
      String

    exactFieldStrengthBlocker :
      String

    receiptBoundary :
      List String

canonicalG2SFGCGaugeFieldSchemaExtensionReceipt :
  G2SFGCGaugeFieldSchemaExtensionReceipt
canonicalG2SFGCGaugeFieldSchemaExtensionReceipt =
  record
    { status =
        coreDirectionIndexedSchemaAdopted
    ; inspectedGaugeField =
        SFGC.GaugeField
    ; inspectedGaugeFieldIsSFGC =
        refl
    ; inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsCurrentShiftPressurePoint =
        refl
    ; coefficientCarrier =
        SPTI4.Phase4
    ; coefficientCarrierIsPhase4 =
        refl
    ; requestedDirectionCarrier =
        G2SFGCPrimeDirection
    ; requestedDirectionCarrierIsP2P3 =
        refl
    ; requestedRightDirection =
        p2Right
    ; requestedRightDirectionIsP2 =
        refl
    ; requestedTransverseDirection =
        p3Transverse
    ; requestedTransverseDirectionIsP3 =
        refl
    ; requestedDirectionsIndependent =
        p2Right≠p3Transverse
    ; currentTransverseEdgeAudit =
        G2TE.canonicalG2SFGCTransverseEdgeAPIRequest
    ; currentUOneAudit =
        G2U1.canonicalG2SFGCAsUOnePrimeLatticeDiagnostic
    ; currentRightOnlyAdapter =
        canonicalCurrentSFGCRightEdgeAdapter
    ; legacyRightOnlyCoreEdgeBlocker =
        canonicalCoreDirectionIndexedSFGCShiftEdgeBlocker
    ; coreTransverseP3LinkUpstreamAPIRequest =
        SFGC.canonicalSFGCTransverseP3LinkUpstreamAPIRequest
    ; coreThreePointP3ActionObstruction =
        SFGC.canonicalSFGCThreePointP3ActionObstruction
    ; site2DSemanticExtension =
        SFGC.canonicalSFGCSite2DMinimalP3SemanticExtension
    ; site2DDirectionIndexedEdgeRequest =
        canonicalSFGCSite2DDirectionIndexedEdgeRequest
    ; coreDirectionIndexedAdoptionReceipt =
        SFGC.canonicalSFGCSite2DCoreDirectionIndexedAdoptionReceipt
    ; coreDirectionIndexedEdgeRequest =
        canonicalCoreDirectionIndexedSFGCEdgeRequest
    ; sufficientSchemaSurface =
        DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField
    ; sufficientSchemaSurfaceIsGaugeFieldSchema =
        refl
    ; conditionalAdoptionConstructorName =
        "adoptSFGCGaugeFieldCarrierFromSchema"
    ; conditionalAdoptionConstructorTarget =
        "DirectionIndexedSFGCGaugeFieldSchema SFGC.GaugeField -> ConditionalSFGCGaugeFieldCarrierAdoption"
    ; coreAdoptionAvailable =
        true
    ; coreAdoptionAvailableIsTrue =
        refl
    ; firstMissing =
        noRemainingG2SFGCSchemaExtensionMissing
    ; remainingMissing =
        []
    ; exactCoreSchemaBlocker =
        "Cleared for direction-indexed core consumers: SFGC.canonicalCoreDirectionIndexedSFGCSchema adopts SFGCSite2D as the core-facing p2/p3 carrier while preserving the old right-only SFGCSite/SFGCShiftEdge compatibility names."
    ; exactRequiredCoreAPI =
        "Use SFGC.CoreDirectionIndexedSFGCSchema for p2/p3 core consumers"
        ∷ "Use canonicalCoreDirectionIndexedSFGCEdgeRequest when G2 needs the adopted core edge request"
        ∷ "Use canonicalSFGCSite2DGaugeFieldSchema for SFGC.GaugeField curvature and field-strength adoption"
        ∷ []
    ; exactForbiddenAssumptions =
        "Do not project source, target, p3, prime-coordinate, or endpoint fields from SPTI.ShiftPressurePoint"
        ∷ "Do not treat the three ShiftPressurePoint constructors as a hidden two-dimensional lattice"
        ∷ "Do not claim fieldStrengthFromCurvature from the right-only adapter"
        ∷ []
    ; rightOnlyAdapterCannotAdoptReason =
        "canonicalCurrentSFGCRightEdgeAdapter is right-edge-only; using it as p3 would identify the transverse link with SSL.rightNeighbor and would not satisfy the nondegenerate p2/p3 schema."
    ; exactFieldStrengthBlocker =
        "No field-strength blocker remains for the adopted core schema: canonicalSFGCSite2DGaugeFieldSchema supplies SFGC.sfgcSite2DFieldStrengthFromCurvature through the adopted direction-indexed carrier."
    ; receiptBoundary =
        "DirectionIndexedSFGCEdgeRequest names the p2/right plus p3/transverse edge API required for SFGC adoption"
        ∷ "canonicalSFGCSite2DDirectionIndexedEdgeRequest now supplies the p2/p3 action, link, target-law, commutation, and nondegenerate site semantics from SFGC.SFGCSite2D"
        ∷ "SFGC.canonicalCoreDirectionIndexedSFGCSchema accepts that SFGCSite2D surface as the core-facing direction-indexed schema"
        ∷ "canonicalCoreDirectionIndexedSFGCEdgeRequest consumes the adopted core schema"
        ∷ "canonicalSFGCSite2DRequiredNondegeneratePlaquetteAPI supplies the p2/p3 corrected square boundary and boundary-of-boundary-zero law"
        ∷ "canonicalSFGCSite2DGaugeFieldSchema ties that edge request to RequiredNondegenerateSFGCPlaquetteAPI"
        ∷ "schemaYieldsDiscreteCurvatureCarrier and adoptSFGCGaugeFieldCarrierFromSchema can consume the sidecar schema"
        ∷ "No constructor mutation is claimed: legacy SFGC.SFGCSite remains ShiftPressurePoint and legacy SFGCShiftEdge remains right-only"
        ∷ []
    }

g2SFGCGaugeFieldSchemaExtensionFirstMissingCleared :
  G2SFGCGaugeFieldSchemaExtensionReceipt.firstMissing
    canonicalG2SFGCGaugeFieldSchemaExtensionReceipt
    ≡
  noRemainingG2SFGCSchemaExtensionMissing
g2SFGCGaugeFieldSchemaExtensionFirstMissingCleared =
  refl

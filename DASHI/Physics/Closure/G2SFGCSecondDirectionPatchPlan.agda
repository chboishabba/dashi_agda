module DASHI.Physics.Closure.G2SFGCSecondDirectionPatchPlan where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2NondegeneratePlaquetteSchema as G2Schema
import DASHI.Physics.Closure.G2TransverseEdgeAPI as G2TE
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- G2 second-direction continuation patch plan.
--
-- This sidecar records why the current SFGC three-point process chain still
-- cannot honestly produce a nondegenerate plaquette.  It deliberately avoids
-- editing the core SFGC carrier: the only existing shift directions are the
-- reflected one-dimensional left/right neighbours, and they do not commute.

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

shiftNextPoint≠shiftStartPoint :
  SPTI.shiftNextPoint ≠ SPTI.shiftStartPoint
shiftNextPoint≠shiftStartPoint ()

leftRightDoNotCommuteAtStart :
  SSL.rightNeighbor (SSL.leftNeighbor SPTI.shiftStartPoint)
    ≠
  SSL.leftNeighbor (SSL.rightNeighbor SPTI.shiftStartPoint)
leftRightDoNotCommuteAtStart =
  shiftNextPoint≠shiftStartPoint

data G2SecondDirectionPatchStatus : Set where
  patchPlanOnlyNoCoreSFGCEdit :
    G2SecondDirectionPatchStatus

data G2SecondDirectionRejectedCandidate : Set where
  rejectLeftNeighborAsTransverseNonCommuting :
    G2SecondDirectionRejectedCandidate

  rejectIdentityAsTransverseDegenerate :
    G2SecondDirectionRejectedCandidate

  rejectProductLiftAsCarrierChange :
    G2SecondDirectionRejectedCandidate

  rejectP3UpNeighborWithoutPrimeIndexedSiteCarrier :
    G2SecondDirectionRejectedCandidate

  rejectConstantZeroCurvatureAsFakePromotion :
    G2SecondDirectionRejectedCandidate

data G2SecondDirectionRequiredPrimitive : Set where
  requireDirectionIndexedSFGCShiftEdge :
    G2SecondDirectionRequiredPrimitive

  requireIndependentTransverseDirection :
    G2SecondDirectionRequiredPrimitive

  requirePrimeIndexedSFGCSiteOrPrimeProjection :
    G2SecondDirectionRequiredPrimitive

  requireCommutingTwoDirectionShiftAction :
    G2SecondDirectionRequiredPrimitive

  requireGaugeSamplingForTransverseEdges :
    G2SecondDirectionRequiredPrimitive

  requireNondegeneratePlaquetteVertices :
    G2SecondDirectionRequiredPrimitive

  requireSignedPlaquetteBoundary :
    G2SecondDirectionRequiredPrimitive

  requirePlaquetteBoundaryOfBoundaryZero :
    G2SecondDirectionRequiredPrimitive

  requireFieldStrengthFromCurvature :
    G2SecondDirectionRequiredPrimitive

data G2P3UpNeighborEncodingStatus : Set where
  p3UpNeighborNotEncodableInCurrentSFGC :
    G2P3UpNeighborEncodingStatus

record G2P3UpNeighborEncodingAssessment : Set₁ where
  field
    status :
      G2P3UpNeighborEncodingStatus

    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierIsSFGC :
      inspectedConnectionCarrier ≡ SFGC.GaugeField

    inspectedRightAction :
      SPTI.ShiftPressurePoint →
      SPTI.ShiftPressurePoint

    inspectedRightActionLaw :
      inspectedRightAction ≡ SSL.rightNeighbor

    hasPrimeIndexedSiteCarrier :
      Bool

    hasFactorVecProjection :
      Bool

    hasPrimeIndexedShiftAction :
      Bool

    hasTransverseGaugeSampler :
      Bool

    currentRightGaugeSampler :
      String

    proposedUpNeighbor :
      String

    canEncodeProposedUpNeighborLocally :
      Bool

    wouldRequireCoreSchemaChange :
      Bool

    exactCoreSchemaChange :
      String

    exactGaugeSchemaChange :
      String

    exactCommutationLaw :
      String

    nonPromotionBoundary :
      List String

canonicalG2P3UpNeighborEncodingAssessment :
  G2P3UpNeighborEncodingAssessment
canonicalG2P3UpNeighborEncodingAssessment =
  record
    { status =
        p3UpNeighborNotEncodableInCurrentSFGC
    ; inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsShiftPressurePoint =
        refl
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierIsSFGC =
        refl
    ; inspectedRightAction =
        SSL.rightNeighbor
    ; inspectedRightActionLaw =
        refl
    ; hasPrimeIndexedSiteCarrier =
        false
    ; hasFactorVecProjection =
        false
    ; hasPrimeIndexedShiftAction =
        false
    ; hasTransverseGaugeSampler =
        false
    ; currentRightGaugeSampler =
        "rightGaugePhase A s = A s, interpreted as transport toward SSL.rightNeighbor s"
    ; proposedUpNeighbor =
        "upNeighbor = p3 bump / transverseShift = prime p3 direction"
    ; canEncodeProposedUpNeighborLocally =
        false
    ; wouldRequireCoreSchemaChange =
        true
    ; exactCoreSchemaChange =
        "replace or extend ShiftPressurePoint with a prime-indexed SFGC site carrier, or add factorVecOf : ShiftPressurePoint -> FactorVec plus shiftAction : SFGCShiftDirection -> ShiftPressurePoint -> ShiftPressurePoint where shiftAction right = p2 and shiftAction transverse = p3"
    ; exactGaugeSchemaChange =
        "extend GaugeField/rightGaugePhase from ShiftPressurePoint -> Phase4 to a direction-indexed link sampler, e.g. SFGCShiftEdge -> Phase4 or ShiftPressurePoint -> SFGCShiftDirection -> Phase4"
    ; exactCommutationLaw =
        "shiftAction transverseShift (shiftAction rightShift x) == shiftAction rightShift (shiftAction transverseShift x), with rightShift and transverseShift distinct and interpreted as p2 and p3"
    ; nonPromotionBoundary =
        "The current site carrier is the three-constructor process chain shiftStartPoint/shiftNextPoint/shiftHeldExitPoint"
        ∷ "No field or projection exposes a FactorVec, Prime, p2 coordinate, or p3 coordinate for ShiftPressurePoint"
        ∷ "A local function ShiftPressurePoint -> ShiftPressurePoint could be made to commute with rightNeighbor, but it would not be a p3 prime direction without new carrier semantics"
        ∷ "The current GaugeField samples one Phase4 per site and is interpreted only as the right-neighbor link"
        ∷ "Therefore upNeighbor = p3 cannot be encoded against the existing SFGC types without a core schema extension"
        ∷ []
    }

record G2SFGCSecondDirectionPatchPlan : Set₂ where
  field
    status :
      G2SecondDirectionPatchStatus

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierIsSFGC :
      inspectedConnectionCarrier ≡ SFGC.GaugeField

    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    inspectedRightAction :
      SPTI.ShiftPressurePoint →
      SPTI.ShiftPressurePoint

    inspectedRightActionLaw :
      inspectedRightAction ≡ SSL.rightNeighbor

    inspectedLeftAction :
      SPTI.ShiftPressurePoint →
      SPTI.ShiftPressurePoint

    inspectedLeftActionLaw :
      inspectedLeftAction ≡ SSL.leftNeighbor

    leftRightNonCommutationWitness :
      inspectedRightAction (inspectedLeftAction SPTI.shiftStartPoint)
        ≠
      inspectedLeftAction (inspectedRightAction SPTI.shiftStartPoint)

    rejectedCandidates :
      List G2SecondDirectionRejectedCandidate

    firstRequiredPrimitive :
      G2SecondDirectionRequiredPrimitive

    requiredPrimitives :
      List G2SecondDirectionRequiredPrimitive

    currentSufficientAPI :
      Set₁

    currentSufficientAPIIsRequiredPlaquetteAPI :
      currentSufficientAPI
      ≡
      G2Schema.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField

    directionIndexedSchemaExtensionReceipt :
      G2Schema.G2DirectionIndexedSchemaExtensionReceipt

    directionIndexedSchemaExtensionIsAvailable :
      G2Schema.G2DirectionIndexedSchemaExtensionReceipt.currentCoreAdoptionAvailable
        directionIndexedSchemaExtensionReceipt
      ≡
      false

    sufficientConstructorName :
      String

    sufficientConstructorTarget :
      String

    exactCorePatchShape :
      String

    exactNewLawShape :
      String

    constructsRequiredAPI :
      Bool

    constructsDiscreteCurvatureCarrier :
      Bool

    firstMissingInExistingSchema :
      G2Schema.G2NondegeneratePlaquetteSchemaMissing

    existingRequest :
      G2TE.G2SFGCTransverseEdgeAPIRequest

    p3UpNeighborEncodingAssessment :
      G2P3UpNeighborEncodingAssessment

    patchBoundary :
      List String

canonicalG2SFGCSecondDirectionPatchPlan :
  G2SFGCSecondDirectionPatchPlan
canonicalG2SFGCSecondDirectionPatchPlan =
  record
    { status =
        patchPlanOnlyNoCoreSFGCEdit
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierIsSFGC =
        refl
    ; inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsShiftPressurePoint =
        refl
    ; inspectedRightAction =
        SSL.rightNeighbor
    ; inspectedRightActionLaw =
        refl
    ; inspectedLeftAction =
        SSL.leftNeighbor
    ; inspectedLeftActionLaw =
        refl
    ; leftRightNonCommutationWitness =
        leftRightDoNotCommuteAtStart
    ; rejectedCandidates =
        rejectLeftNeighborAsTransverseNonCommuting
        ∷ rejectIdentityAsTransverseDegenerate
        ∷ rejectProductLiftAsCarrierChange
        ∷ rejectP3UpNeighborWithoutPrimeIndexedSiteCarrier
        ∷ rejectConstantZeroCurvatureAsFakePromotion
        ∷ []
    ; firstRequiredPrimitive =
        requireDirectionIndexedSFGCShiftEdge
    ; requiredPrimitives =
        requireDirectionIndexedSFGCShiftEdge
        ∷ requireIndependentTransverseDirection
        ∷ requirePrimeIndexedSFGCSiteOrPrimeProjection
        ∷ requireCommutingTwoDirectionShiftAction
        ∷ requireGaugeSamplingForTransverseEdges
        ∷ requireNondegeneratePlaquetteVertices
        ∷ requireSignedPlaquetteBoundary
        ∷ requirePlaquetteBoundaryOfBoundaryZero
        ∷ requireFieldStrengthFromCurvature
        ∷ []
    ; currentSufficientAPI =
        G2Schema.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField
    ; currentSufficientAPIIsRequiredPlaquetteAPI =
        refl
    ; directionIndexedSchemaExtensionReceipt =
        G2Schema.canonicalG2DirectionIndexedSchemaExtensionReceipt
    ; directionIndexedSchemaExtensionIsAvailable =
        refl
    ; sufficientConstructorName =
        "directionIndexedSchemaYieldsDiscreteCurvatureCarrier"
    ; sufficientConstructorTarget =
        "RequiredDirectionIndexedSFGCSchemaExtension SFGC.GaugeField -> DiscreteCurvatureCarrier SFGC.GaugeField"
    ; exactCorePatchShape =
        "data SFGCPrimeDirection = p2RightDirection | p3UpDirection; add SFGCSite plus SFGCShiftEdge : SFGCPrimeDirection -> SFGCSite -> Set; add shiftAction where p2Right is the current right direction and p3Up is the independent transverse direction"
    ; exactNewLawShape =
        "shiftAction transverseShift (shiftAction rightShift x) == shiftAction rightShift (shiftAction transverseShift x), with rightShift != transverseShift"
    ; constructsRequiredAPI =
        false
    ; constructsDiscreteCurvatureCarrier =
        false
    ; firstMissingInExistingSchema =
        G2Schema.missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
    ; existingRequest =
        G2TE.canonicalG2SFGCTransverseEdgeAPIRequest
    ; p3UpNeighborEncodingAssessment =
        canonicalG2P3UpNeighborEncodingAssessment
    ; patchBoundary =
        "The current SFGC site carrier is the three-point ShiftPressurePoint process chain"
        ∷ "SSL.rightNeighbor is the only direction used by SFGC.GaugeField link sampling"
        ∷ "SSL.leftNeighbor cannot be the transverse direction: right(left(start)) = shiftNextPoint but left(right(start)) = shiftStartPoint"
        ∷ "An identity transverse action would commute but would be degenerate and would not create a nondegenerate plaquette"
        ∷ "upNeighbor = p3 is not locally encodable: the current ShiftPressurePoint type exposes no Prime/FactorVec coordinate and SFGC.GaugeField has no transverse link sampler"
        ∷ "A product-lifted two-dimensional site would be a new carrier, not the existing SFGC ShiftPressurePoint carrier"
        ∷ "A constant-zero δ1 would typecheck only by erasing the curvature content, so it is rejected as fake promotion"
        ∷ "The local direction-indexed schema surface is now typed with p2/right and p3/up directions"
        ∷ "The safe core patch is adoption of that SFGCShiftEdge plus a real transverse shift action and commutation law"
        ∷ "After core adoption, the next G2 blocker is field-strength-from-curvature / accepted Discrete2Form consumer"
        ∷ "No RequiredNondegenerateSFGCPlaquetteAPI or DiscreteCurvatureCarrier is constructed here"
        ∷ []
    }

g2SecondDirectionPatchPlanDoesNotPromote :
  G2SFGCSecondDirectionPatchPlan.constructsDiscreteCurvatureCarrier
    canonicalG2SFGCSecondDirectionPatchPlan
  ≡
  false
g2SecondDirectionPatchPlanDoesNotPromote =
  refl

g2SecondDirectionPatchPlanFirstMissing :
  G2SFGCSecondDirectionPatchPlan.firstMissingInExistingSchema
    canonicalG2SFGCSecondDirectionPatchPlan
  ≡
  G2Schema.missingCoreAdoptionOfDirectionIndexedSFGCShiftEdge
g2SecondDirectionPatchPlanFirstMissing =
  refl

g2SecondDirectionPatchPlanDirectionSchemaCoreAdoptionBlocked :
  G2Schema.G2DirectionIndexedSchemaExtensionReceipt.currentCoreAdoptionAvailable
    (G2SFGCSecondDirectionPatchPlan.directionIndexedSchemaExtensionReceipt
      canonicalG2SFGCSecondDirectionPatchPlan)
  ≡
  false
g2SecondDirectionPatchPlanDirectionSchemaCoreAdoptionBlocked =
  refl

g2SecondDirectionPatchPlanSufficientTarget :
  G2SFGCSecondDirectionPatchPlan.currentSufficientAPI
    canonicalG2SFGCSecondDirectionPatchPlan
  ≡
  G2Schema.RequiredNondegenerateSFGCPlaquetteAPI SFGC.GaugeField
g2SecondDirectionPatchPlanSufficientTarget =
  refl

g2P3UpNeighborCannotBeEncodedLocally :
  G2P3UpNeighborEncodingAssessment.canEncodeProposedUpNeighborLocally
    canonicalG2P3UpNeighborEncodingAssessment
  ≡
  false
g2P3UpNeighborCannotBeEncodedLocally =
  refl

g2P3UpNeighborRequiresCoreSchemaChange :
  G2P3UpNeighborEncodingAssessment.wouldRequireCoreSchemaChange
    canonicalG2P3UpNeighborEncodingAssessment
  ≡
  true
g2P3UpNeighborRequiresCoreSchemaChange =
  refl

module DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
------------------------------------------------------------------------
-- Higgs symmetry-breaking receipt surface.
--
-- This module records only the obligation surface for a future electroweak
-- symmetry-breaking lane.  It does not derive the Higgs mechanism, CKM,
-- Standard Model closure, W/Z masses, photon masslessness, empirical
-- calibration, or any terminal promotion.  The absolute v_Higgs scale remains
-- an Adapter 4 / governance boundary.

data HiggsSymmetryBreakingStatus : Set where
  higgsSymmetryBreakingTargetsOnlyNoPromotion :
    HiggsSymmetryBreakingStatus

data HiggsSymmetryBreakingOpenObligation : Set where
  missingPreBreakingGauge :
    HiggsSymmetryBreakingOpenObligation

  missingPostBreakingGauge :
    HiggsSymmetryBreakingOpenObligation

  missingHiggsField :
    HiggsSymmetryBreakingOpenObligation

  missingMexicanHatPotential :
    HiggsSymmetryBreakingOpenObligation

  missingVEV :
    HiggsSymmetryBreakingOpenObligation

  missingVEVNonzeroTarget :
    HiggsSymmetryBreakingOpenObligation

  missingPhysicalVEVCalibration :
    HiggsSymmetryBreakingOpenObligation

  missingResidualGauge :
    HiggsSymmetryBreakingOpenObligation

  missingWMassTarget :
    HiggsSymmetryBreakingOpenObligation

  missingZMassTarget :
    HiggsSymmetryBreakingOpenObligation

  missingPhotonMasslessTarget :
    HiggsSymmetryBreakingOpenObligation

  vHiggsRemainsAdapter4Boundary :
    HiggsSymmetryBreakingOpenObligation

canonicalHiggsSymmetryBreakingOpenObligations :
  List HiggsSymmetryBreakingOpenObligation
canonicalHiggsSymmetryBreakingOpenObligations =
  missingPreBreakingGauge
  ∷ missingPostBreakingGauge
  ∷ missingHiggsField
  ∷ missingMexicanHatPotential
  ∷ missingVEV
  ∷ missingVEVNonzeroTarget
  ∷ missingPhysicalVEVCalibration
  ∷ missingResidualGauge
  ∷ missingWMassTarget
  ∷ missingZMassTarget
  ∷ missingPhotonMasslessTarget
  ∷ vHiggsRemainsAdapter4Boundary
  ∷ []

data HiggsSymmetryBreakingPromotionAuthorityToken : Set where

data HiggsSymmetryBreakingDependency : Set where
  paper2GaugeTransportDependency :
    HiggsSymmetryBreakingDependency

  w4PhysicalCalibrationDependency :
    HiggsSymmetryBreakingDependency

  carrierMexicanHatPotentialDependency :
    HiggsSymmetryBreakingDependency

  nonzeroVEVProofDependency :
    HiggsSymmetryBreakingDependency

  goldstoneResidualGaugeDependency :
    HiggsSymmetryBreakingDependency

  finalAdapter4VHiggsBoundaryDependency :
    HiggsSymmetryBreakingDependency

canonicalHiggsSymmetryBreakingDependencies :
  List HiggsSymmetryBreakingDependency
canonicalHiggsSymmetryBreakingDependencies =
  paper2GaugeTransportDependency
  ∷ w4PhysicalCalibrationDependency
  ∷ carrierMexicanHatPotentialDependency
  ∷ nonzeroVEVProofDependency
  ∷ goldstoneResidualGaugeDependency
  ∷ finalAdapter4VHiggsBoundaryDependency
  ∷ []

data HiggsPotentialShapeBlocker : Set where
  missingCarrierQuarticPotential :
    HiggsPotentialShapeBlocker

  missingPositiveLambdaWitness :
    HiggsPotentialShapeBlocker

  missingNegativeMassSquaredWitness :
    HiggsPotentialShapeBlocker

  missingArgminCircleProof :
    HiggsPotentialShapeBlocker

  missingResidualU1QuotientProof :
    HiggsPotentialShapeBlocker

canonicalHiggsPotentialShapeBlockers :
  List HiggsPotentialShapeBlocker
canonicalHiggsPotentialShapeBlockers =
  missingPositiveLambdaWitness
  ∷ missingNegativeMassSquaredWitness
  ∷ missingArgminCircleProof
  ∷ missingResidualU1QuotientProof
  ∷ []

data HiggsCarrierQuarticPotentialBlocker : Set where
  missingHiggsScalarCarrierDefinition :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierNormSquared :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierScalarFieldValues :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierNormOrder :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierQuarticPotentialFunctional :
    HiggsCarrierQuarticPotentialBlocker

  missingMuLambdaCalibration :
    HiggsCarrierQuarticPotentialBlocker

  missingPositiveQuarticCouplingWitness :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierNegativeMassSquaredWitness :
    HiggsCarrierQuarticPotentialBlocker

  missingMexicanHatShapeProof :
    HiggsCarrierQuarticPotentialBlocker

  missingCarrierArgminCircleProof :
    HiggsCarrierQuarticPotentialBlocker

  missingNonzeroVEVFromArgmin :
    HiggsCarrierQuarticPotentialBlocker

canonicalHiggsCarrierQuarticPotentialBlockers :
  List HiggsCarrierQuarticPotentialBlocker
canonicalHiggsCarrierQuarticPotentialBlockers =
  missingCarrierScalarFieldValues
  ∷ missingCarrierNormOrder
  ∷ missingMuLambdaCalibration
  ∷ missingCarrierArgminCircleProof
  ∷ missingNonzeroVEVFromArgmin
  ∷ []

canonicalHiggsCarrierQuarticPotentialBlockersAfterScalarValues :
  List HiggsCarrierQuarticPotentialBlocker
canonicalHiggsCarrierQuarticPotentialBlockersAfterScalarValues =
  missingCarrierNormOrder
  ∷ missingMuLambdaCalibration
  ∷ missingCarrierArgminCircleProof
  ∷ missingNonzeroVEVFromArgmin
  ∷ []

data HiggsScalarCarrierPrimitiveRequest : Set where
  missingHiggsSU2LDoubletRepresentationPrimitive :
    HiggsScalarCarrierPrimitiveRequest

  missingHiggsU1YHyperchargePlusOnePrimitive :
    HiggsScalarCarrierPrimitiveRequest

  missingHiggsFourRealComponentDecompositionPrimitive :
    HiggsScalarCarrierPrimitiveRequest

canonicalHiggsScalarCarrierPrimitiveRequests :
  List HiggsScalarCarrierPrimitiveRequest
canonicalHiggsScalarCarrierPrimitiveRequests =
  missingHiggsSU2LDoubletRepresentationPrimitive
  ∷ missingHiggsU1YHyperchargePlusOnePrimitive
  ∷ missingHiggsFourRealComponentDecompositionPrimitive
  ∷ []

data HiggsMatterRepresentationMissingFieldConstructor : Set where
  missingHiggsMatterRepresentationConstructor :
    HiggsMatterRepresentationMissingFieldConstructor

  missingHiggsHyperchargeAssignmentConstructor :
    HiggsMatterRepresentationMissingFieldConstructor

  missingHiggsSU2LDoubletRepresentationConstructor :
    HiggsMatterRepresentationMissingFieldConstructor

  missingHiggsU1YHyperchargePlusOneConstructor :
    HiggsMatterRepresentationMissingFieldConstructor

  missingHiggsFourRealComponentDecompositionConstructor :
    HiggsMatterRepresentationMissingFieldConstructor

canonicalHiggsMatterRepresentationMissingFieldConstructors :
  List HiggsMatterRepresentationMissingFieldConstructor
canonicalHiggsMatterRepresentationMissingFieldConstructors =
  []

HiggsSU2LDoubletRepresentation :
  Set
HiggsSU2LDoubletRepresentation =
  Matter.GaugeRepresentationPrimitive

HiggsU1YHyperchargePlusOne :
  Set
HiggsU1YHyperchargePlusOne =
  Matter.HyperchargePrimitive

HiggsFourRealComponentDecomposition :
  Set
HiggsFourRealComponentDecomposition =
  Matter.ComponentPrimitive

record HiggsScalarCarrierDefinitionRequest : Setω where
  field
    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsHiggsDoublet :
      matterSectorTarget
      ≡
      Matter.higgsDoubletTarget

    matterRepresentationCarrierTarget :
      Set

    matterRepresentationCarrierTargetIsMatterRepresentation :
      matterRepresentationCarrierTarget
      ≡
      Matter.MatterRepresentation

    hyperchargeAssignmentCarrierTarget :
      Set

    hyperchargeAssignmentCarrierTargetIsMatterHypercharge :
      hyperchargeAssignmentCarrierTarget
      ≡
      Matter.HyperchargeAssignment

    su2LDoubletRepresentationTarget :
      Set

    su2LDoubletRepresentationTargetIsPrimitive :
      su2LDoubletRepresentationTarget
      ≡
      HiggsSU2LDoubletRepresentation

    u1YHyperchargePlusOneTarget :
      Set

    u1YHyperchargePlusOneTargetIsPrimitive :
      u1YHyperchargePlusOneTarget
      ≡
      HiggsU1YHyperchargePlusOne

    fourRealComponentDecompositionTarget :
      Set

    fourRealComponentDecompositionTargetIsPrimitive :
      fourRealComponentDecompositionTarget
      ≡
      HiggsFourRealComponentDecomposition

    requestedPrimitives :
      List HiggsScalarCarrierPrimitiveRequest

    requestedPrimitivesAreCanonical :
      requestedPrimitives
      ≡
      canonicalHiggsScalarCarrierPrimitiveRequests

    scalarCarrierDefinitionConstructed :
      Bool

    scalarCarrierDefinitionConstructedIsFalse :
      scalarCarrierDefinitionConstructed ≡ false

    boundary :
      List String

open HiggsScalarCarrierDefinitionRequest public

canonicalHiggsScalarCarrierDefinitionRequest :
  HiggsScalarCarrierDefinitionRequest
canonicalHiggsScalarCarrierDefinitionRequest =
  record
    { matterSectorTarget =
        Matter.higgsDoubletTarget
    ; matterSectorTargetIsHiggsDoublet =
        refl
    ; matterRepresentationCarrierTarget =
        Matter.MatterRepresentation
    ; matterRepresentationCarrierTargetIsMatterRepresentation =
        refl
    ; hyperchargeAssignmentCarrierTarget =
        Matter.HyperchargeAssignment
    ; hyperchargeAssignmentCarrierTargetIsMatterHypercharge =
        refl
    ; su2LDoubletRepresentationTarget =
        HiggsSU2LDoubletRepresentation
    ; su2LDoubletRepresentationTargetIsPrimitive =
        refl
    ; u1YHyperchargePlusOneTarget =
        HiggsU1YHyperchargePlusOne
    ; u1YHyperchargePlusOneTargetIsPrimitive =
        refl
    ; fourRealComponentDecompositionTarget =
        HiggsFourRealComponentDecomposition
    ; fourRealComponentDecompositionTargetIsPrimitive =
        refl
    ; requestedPrimitives =
        canonicalHiggsScalarCarrierPrimitiveRequests
    ; requestedPrimitivesAreCanonical =
        refl
    ; scalarCarrierDefinitionConstructed =
        false
    ; scalarCarrierDefinitionConstructedIsFalse =
        refl
    ; boundary =
        "Higgs scalar is narrowed to Matter.higgsDoubletTarget"
        ∷ "Required primitive: SU2_L doublet representation"
        ∷ "Required primitive: U1_Y hypercharge plus one"
        ∷ "Required primitive: four-real-component decomposition"
        ∷ "No mu, lambda, v, W4 calibration value, or terminal promotion is introduced here"
        ∷ []
    }

record HiggsScalarCarrierDefinitionSurface : Setω where
  field
    carrierDefinitionRequest :
      HiggsScalarCarrierDefinitionRequest

    higgsScalarMatterTarget :
      Matter.StandardModelMatterSectorTarget

    higgsScalarMatterTargetIsHiggsDoublet :
      higgsScalarMatterTarget
      ≡
      Matter.higgsDoubletTarget

    higgsScalarMatterRepresentationCarrier :
      Set

    higgsScalarMatterRepresentationCarrierIsMatterRepresentation :
      higgsScalarMatterRepresentationCarrier
      ≡
      Matter.MatterRepresentation

    higgsScalarHyperchargeCarrier :
      Set

    higgsScalarHyperchargeCarrierIsMatterHypercharge :
      higgsScalarHyperchargeCarrier
      ≡
      Matter.HyperchargeAssignment

    higgsScalarSU2LDoubletPrimitive :
      Set

    higgsScalarSU2LDoubletPrimitiveIsRequestedPrimitive :
      higgsScalarSU2LDoubletPrimitive
      ≡
      HiggsSU2LDoubletRepresentation

    higgsScalarHyperchargePlusOnePrimitive :
      Set

    higgsScalarHyperchargePlusOnePrimitiveIsRequestedPrimitive :
      higgsScalarHyperchargePlusOnePrimitive
      ≡
      HiggsU1YHyperchargePlusOne

    higgsScalarFourRealComponentPrimitive :
      Set

    higgsScalarFourRealComponentPrimitiveIsRequestedPrimitive :
      higgsScalarFourRealComponentPrimitive
      ≡
      HiggsFourRealComponentDecomposition

    higgsScalarSurfaceRecorded :
      Bool

    higgsScalarSurfaceRecordedIsTrue :
      higgsScalarSurfaceRecorded ≡ true

    higgsScalarCarrierDefinitionConstructed :
      Bool

    higgsScalarCarrierDefinitionConstructedIsFalse :
      higgsScalarCarrierDefinitionConstructed ≡ false

    higgsScalarYukawaInterfaceConstructed :
      Bool

    higgsScalarYukawaInterfaceConstructedIsFalse :
      higgsScalarYukawaInterfaceConstructed ≡ false

    higgsScalarVEVConstructed :
      Bool

    higgsScalarVEVConstructedIsFalse :
      higgsScalarVEVConstructed ≡ false

    higgsScalarW4CalibrationConstructed :
      Bool

    higgsScalarW4CalibrationConstructedIsFalse :
      higgsScalarW4CalibrationConstructed ≡ false

    higgsScalarPromotionConstructed :
      Bool

    higgsScalarPromotionConstructedIsFalse :
      higgsScalarPromotionConstructed ≡ false

    higgsScalarSurfaceBoundary :
      List String

open HiggsScalarCarrierDefinitionSurface public

canonicalHiggsScalarCarrierDefinitionSurface :
  HiggsScalarCarrierDefinitionSurface
canonicalHiggsScalarCarrierDefinitionSurface =
  record
    { carrierDefinitionRequest =
        canonicalHiggsScalarCarrierDefinitionRequest
    ; higgsScalarMatterTarget =
        Matter.higgsDoubletTarget
    ; higgsScalarMatterTargetIsHiggsDoublet =
        refl
    ; higgsScalarMatterRepresentationCarrier =
        Matter.MatterRepresentation
    ; higgsScalarMatterRepresentationCarrierIsMatterRepresentation =
        refl
    ; higgsScalarHyperchargeCarrier =
        Matter.HyperchargeAssignment
    ; higgsScalarHyperchargeCarrierIsMatterHypercharge =
        refl
    ; higgsScalarSU2LDoubletPrimitive =
        HiggsSU2LDoubletRepresentation
    ; higgsScalarSU2LDoubletPrimitiveIsRequestedPrimitive =
        refl
    ; higgsScalarHyperchargePlusOnePrimitive =
        HiggsU1YHyperchargePlusOne
    ; higgsScalarHyperchargePlusOnePrimitiveIsRequestedPrimitive =
        refl
    ; higgsScalarFourRealComponentPrimitive =
        HiggsFourRealComponentDecomposition
    ; higgsScalarFourRealComponentPrimitiveIsRequestedPrimitive =
        refl
    ; higgsScalarSurfaceRecorded =
        true
    ; higgsScalarSurfaceRecordedIsTrue =
        refl
    ; higgsScalarCarrierDefinitionConstructed =
        false
    ; higgsScalarCarrierDefinitionConstructedIsFalse =
        refl
    ; higgsScalarYukawaInterfaceConstructed =
        false
    ; higgsScalarYukawaInterfaceConstructedIsFalse =
        refl
    ; higgsScalarVEVConstructed =
        false
    ; higgsScalarVEVConstructedIsFalse =
        refl
    ; higgsScalarW4CalibrationConstructed =
        false
    ; higgsScalarW4CalibrationConstructedIsFalse =
        refl
    ; higgsScalarPromotionConstructed =
        false
    ; higgsScalarPromotionConstructedIsFalse =
        refl
    ; higgsScalarSurfaceBoundary =
        "Carrier surface records Matter.higgsDoubletTarget with MatterRepresentation and HyperchargeAssignment sockets"
        ∷ "SU2_L doublet, U1_Y +1, and four-real-component decomposition remain requested primitives"
        ∷ "No Yukawa interface, VEV, W4 calibration, Higgs mechanism, or terminal promotion is constructed by this surface"
        ∷ []
    }

record HiggsScalarCarrierPrimitiveWitness : Setω where
  field
    carrierDefinitionRequest :
      HiggsScalarCarrierDefinitionRequest

    carrierDefinitionSurface :
      HiggsScalarCarrierDefinitionSurface

    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsHiggsDoublet :
      matterSectorTarget
      ≡
      Matter.higgsDoubletTarget

    matterRepresentationSocket :
      Set

    matterRepresentationSocketIsMatterRepresentation :
      matterRepresentationSocket
      ≡
      Matter.MatterRepresentation

    hyperchargeSocket :
      Set

    hyperchargeSocketIsMatterHypercharge :
      hyperchargeSocket
      ≡
      Matter.HyperchargeAssignment

    su2LDoubletPrimitiveTarget :
      Set

    su2LDoubletPrimitiveTargetIsRequestedPrimitive :
      su2LDoubletPrimitiveTarget
      ≡
      HiggsSU2LDoubletRepresentation

    hyperchargePlusOnePrimitiveTarget :
      Set

    hyperchargePlusOnePrimitiveTargetIsRequestedPrimitive :
      hyperchargePlusOnePrimitiveTarget
      ≡
      HiggsU1YHyperchargePlusOne

    fourRealComponentPrimitiveTarget :
      Set

    fourRealComponentPrimitiveTargetIsRequestedPrimitive :
      fourRealComponentPrimitiveTarget
      ≡
      HiggsFourRealComponentDecomposition

    requestedPrimitives :
      List HiggsScalarCarrierPrimitiveRequest

    requestedPrimitivesAreCanonical :
      requestedPrimitives
      ≡
      canonicalHiggsScalarCarrierPrimitiveRequests

    primitiveWitnessRecordsMatterSockets :
      Bool

    primitiveWitnessRecordsMatterSocketsIsTrue :
      primitiveWitnessRecordsMatterSockets ≡ true

    primitiveWitnessConstructsConcreteCarrier :
      Bool

    primitiveWitnessConstructsConcreteCarrierIsFalse :
      primitiveWitnessConstructsConcreteCarrier ≡ false

    primitiveWitnessConstructsVEVOrCalibration :
      Bool

    primitiveWitnessConstructsVEVOrCalibrationIsFalse :
      primitiveWitnessConstructsVEVOrCalibration ≡ false

    primitiveWitnessPromotesHiggs :
      Bool

    primitiveWitnessPromotesHiggsIsFalse :
      primitiveWitnessPromotesHiggs ≡ false

    primitiveWitnessBoundary :
      List String

open HiggsScalarCarrierPrimitiveWitness public

record MatterRepresentationPrimitiveSupply : Setω where
  field
    higgsScalarPrimitiveWitness :
      HiggsScalarCarrierPrimitiveWitness

    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsHiggsDoublet :
      matterSectorTarget
      ≡
      Matter.higgsDoubletTarget

    missingFieldConstructors :
      List HiggsMatterRepresentationMissingFieldConstructor

    missingFieldConstructorsAreCanonical :
      missingFieldConstructors
      ≡
      canonicalHiggsMatterRepresentationMissingFieldConstructors

    matterRepresentationConstructorSupplied :
      Bool

    matterRepresentationConstructorSuppliedIsTrue :
      matterRepresentationConstructorSupplied ≡ true

    hyperchargeAssignmentConstructorSupplied :
      Bool

    hyperchargeAssignmentConstructorSuppliedIsFalse :
      hyperchargeAssignmentConstructorSupplied ≡ false

    representationPrimitiveConstructorsSupplied :
      Bool

    representationPrimitiveConstructorsSuppliedIsTrue :
      representationPrimitiveConstructorsSupplied ≡ true

    constructsHiggsScalarCarrier :
      Bool

    constructsHiggsScalarCarrierIsFalse :
      constructsHiggsScalarCarrier ≡ false

    dischargesYukawaVEVW4OrPromotion :
      Bool

    dischargesYukawaVEVW4OrPromotionIsFalse :
      dischargesYukawaVEVW4OrPromotion ≡ false

    supplyRequestBoundary :
      List String

open MatterRepresentationPrimitiveSupply public

canonicalHiggsScalarCarrierPrimitiveWitness :
  HiggsScalarCarrierPrimitiveWitness
canonicalHiggsScalarCarrierPrimitiveWitness =
  record
    { carrierDefinitionRequest =
        canonicalHiggsScalarCarrierDefinitionRequest
    ; carrierDefinitionSurface =
        canonicalHiggsScalarCarrierDefinitionSurface
    ; matterSectorTarget =
        Matter.higgsDoubletTarget
    ; matterSectorTargetIsHiggsDoublet =
        refl
    ; matterRepresentationSocket =
        Matter.MatterRepresentation
    ; matterRepresentationSocketIsMatterRepresentation =
        refl
    ; hyperchargeSocket =
        Matter.HyperchargeAssignment
    ; hyperchargeSocketIsMatterHypercharge =
        refl
    ; su2LDoubletPrimitiveTarget =
        HiggsSU2LDoubletRepresentation
    ; su2LDoubletPrimitiveTargetIsRequestedPrimitive =
        refl
    ; hyperchargePlusOnePrimitiveTarget =
        HiggsU1YHyperchargePlusOne
    ; hyperchargePlusOnePrimitiveTargetIsRequestedPrimitive =
        refl
    ; fourRealComponentPrimitiveTarget =
        HiggsFourRealComponentDecomposition
    ; fourRealComponentPrimitiveTargetIsRequestedPrimitive =
        refl
    ; requestedPrimitives =
        canonicalHiggsScalarCarrierPrimitiveRequests
    ; requestedPrimitivesAreCanonical =
        refl
    ; primitiveWitnessRecordsMatterSockets =
        true
    ; primitiveWitnessRecordsMatterSocketsIsTrue =
        refl
    ; primitiveWitnessConstructsConcreteCarrier =
        false
    ; primitiveWitnessConstructsConcreteCarrierIsFalse =
        refl
    ; primitiveWitnessConstructsVEVOrCalibration =
        false
    ; primitiveWitnessConstructsVEVOrCalibrationIsFalse =
        refl
    ; primitiveWitnessPromotesHiggs =
        false
    ; primitiveWitnessPromotesHiggsIsFalse =
        refl
    ; primitiveWitnessBoundary =
        "Higgs primitive witness uses Matter.higgsDoubletTarget with MatterRepresentation and HyperchargeAssignment sockets"
        ∷ "Concrete SU2_L doublet, U1_Y +1, and four-real-component carrier primitives are supplied by MatterRepresentationReceiptSurface"
        ∷ "No Higgs scalar carrier value, VEV, W4 calibration, Yukawa interface, or promotion is constructed"
        ∷ []
    }

canonicalHiggsMatterRepresentationPrimitiveSupplyRequest :
  MatterRepresentationPrimitiveSupply
canonicalHiggsMatterRepresentationPrimitiveSupplyRequest =
  record
    { higgsScalarPrimitiveWitness =
        canonicalHiggsScalarCarrierPrimitiveWitness
    ; matterSectorTarget =
        Matter.higgsDoubletTarget
    ; matterSectorTargetIsHiggsDoublet =
        refl
    ; missingFieldConstructors =
        canonicalHiggsMatterRepresentationMissingFieldConstructors
    ; missingFieldConstructorsAreCanonical =
        refl
    ; matterRepresentationConstructorSupplied =
        true
    ; matterRepresentationConstructorSuppliedIsTrue =
        refl
    ; hyperchargeAssignmentConstructorSupplied =
        false
    ; hyperchargeAssignmentConstructorSuppliedIsFalse =
        refl
    ; representationPrimitiveConstructorsSupplied =
        true
    ; representationPrimitiveConstructorsSuppliedIsTrue =
        refl
    ; constructsHiggsScalarCarrier =
        false
    ; constructsHiggsScalarCarrierIsFalse =
        refl
    ; dischargesYukawaVEVW4OrPromotion =
        false
    ; dischargesYukawaVEVW4OrPromotionIsFalse =
        refl
    ; supplyRequestBoundary =
        "MatterRepresentationPrimitiveSupply request for the Higgs scalar is narrowed to Matter.higgsDoubletTarget"
        ∷ "MatterRepresentationReceiptSurface supplies Matter.canonicalHiggsDoubletMatterRepresentation as the local Higgs-doublet MatterRepresentation constructor witness"
        ∷ "MatterRepresentationReceiptSurface supplies the SU2_L doublet, numeric U1_Y +1, scalar chirality, and four-real-component primitive data"
        ∷ "This request does not construct a Higgs scalar carrier, Yukawa interface, VEV, W4 calibration, or promotion"
        ∷ []
    }

record HiggsDoubletMatterSurfacePrimitiveRequest : Set where
  field
    matterSectorTarget :
      Matter.StandardModelMatterSectorTarget

    matterSectorTargetIsHiggsDoublet :
      matterSectorTarget
      ≡
      Matter.higgsDoubletTarget

    availableHyperchargeAssignment :
      Matter.HyperchargeAssignment

    availableHyperchargeAssignmentIsMatterSurfaceTarget :
      availableHyperchargeAssignment
      ≡
      Matter.hyperchargeAssignmentTarget Matter.higgsDoubletTarget

    matterSurfaceHiggsDoubletPrimitive :
      Matter.HiggsDoubletPrimitive

    matterSurfaceHiggsDoubletPrimitiveIsCanonical :
      matterSurfaceHiggsDoubletPrimitive
      ≡
      Matter.canonicalHiggsDoubletPrimitive

    matterSurfaceSU2LDoubletPrimitive :
      Matter.GaugeRepresentationPrimitive

    matterSurfaceSU2LDoubletPrimitiveIsCanonical :
      matterSurfaceSU2LDoubletPrimitive
      ≡
      Matter.canonicalSU2LWeakDoubletPrimitive

    matterSurfaceHyperchargePlusOnePrimitive :
      Matter.HyperchargePrimitive

    matterSurfaceHyperchargePlusOnePrimitiveIsCanonical :
      matterSurfaceHyperchargePlusOnePrimitive
      ≡
      Matter.canonicalHyperchargePlusOnePrimitive

    matterSurfaceFourRealComponentPrimitive :
      Matter.ComponentPrimitive

    matterSurfaceFourRealComponentPrimitiveIsCanonical :
      matterSurfaceFourRealComponentPrimitive
      ≡
      Matter.canonicalHiggsFourRealComponentPrimitive

    matterSurfaceHiggsDoubletMatterRepresentation :
      Matter.MatterRepresentation

    matterSurfaceHiggsDoubletMatterRepresentationIsCanonical :
      matterSurfaceHiggsDoubletMatterRepresentation
      ≡
      Matter.canonicalHiggsDoubletMatterRepresentation

    constructsConcreteHiggsDoubletPrimitive :
      Bool

    constructsConcreteHiggsDoubletPrimitiveIsTrue :
      constructsConcreteHiggsDoubletPrimitive ≡ true

    keepsYukawaVEVW4AndPromotionOpen :
      Bool

    keepsYukawaVEVW4AndPromotionOpenIsTrue :
      keepsYukawaVEVW4AndPromotionOpen ≡ true

    localHiggsMatterRepresentationConstructorSupplied :
      Bool

    localHiggsMatterRepresentationConstructorSuppliedIsTrue :
      localHiggsMatterRepresentationConstructorSupplied ≡ true

    higgsDoubletMatterSurfaceRequestBoundary :
      List String

open HiggsDoubletMatterSurfacePrimitiveRequest public

canonicalHiggsDoubletMatterSurfacePrimitiveRequest :
  HiggsDoubletMatterSurfacePrimitiveRequest
canonicalHiggsDoubletMatterSurfacePrimitiveRequest =
  record
    { matterSectorTarget =
        Matter.higgsDoubletTarget
    ; matterSectorTargetIsHiggsDoublet =
        refl
    ; availableHyperchargeAssignment =
        Matter.hyperchargeAssignmentTarget Matter.higgsDoubletTarget
    ; availableHyperchargeAssignmentIsMatterSurfaceTarget =
        refl
    ; matterSurfaceHiggsDoubletPrimitive =
        Matter.canonicalHiggsDoubletPrimitive
    ; matterSurfaceHiggsDoubletPrimitiveIsCanonical =
        refl
    ; matterSurfaceSU2LDoubletPrimitive =
        Matter.canonicalSU2LWeakDoubletPrimitive
    ; matterSurfaceSU2LDoubletPrimitiveIsCanonical =
        refl
    ; matterSurfaceHyperchargePlusOnePrimitive =
        Matter.canonicalHyperchargePlusOnePrimitive
    ; matterSurfaceHyperchargePlusOnePrimitiveIsCanonical =
        refl
    ; matterSurfaceFourRealComponentPrimitive =
        Matter.canonicalHiggsFourRealComponentPrimitive
    ; matterSurfaceFourRealComponentPrimitiveIsCanonical =
        refl
    ; matterSurfaceHiggsDoubletMatterRepresentation =
        Matter.canonicalHiggsDoubletMatterRepresentation
    ; matterSurfaceHiggsDoubletMatterRepresentationIsCanonical =
        refl
    ; constructsConcreteHiggsDoubletPrimitive =
        true
    ; constructsConcreteHiggsDoubletPrimitiveIsTrue =
        refl
    ; keepsYukawaVEVW4AndPromotionOpen =
        true
    ; keepsYukawaVEVW4AndPromotionOpenIsTrue =
        refl
    ; localHiggsMatterRepresentationConstructorSupplied =
        true
    ; localHiggsMatterRepresentationConstructorSuppliedIsTrue =
        refl
    ; higgsDoubletMatterSurfaceRequestBoundary =
        "MatterRepresentationReceiptSurface supplies the generic hypercharge adapter at Matter.higgsDoubletTarget, a concrete HiggsDoubletPrimitive, and a canonical Higgs-doublet MatterRepresentation witness"
        ∷ "Matter-surface primitive constructors give SU2_L doublet, numeric U1_Y +1 hypercharge, scalar chirality, and four-real-component decomposition data"
        ∷ "The MatterRepresentation witness is a local constructor layer and does not supply CompactGaugeGroup global form, Yukawa, VEV, W4 calibration, or promotion evidence"
        ∷ []
    }

data HiggsSymbolicCarrierValue : Set where
  symbolicHiggsCarrierFromMatterSurface :
    Matter.HiggsDoubletPrimitive →
    Matter.MatterRepresentation →
    HiggsSymbolicCarrierValue

canonicalHiggsSymbolicCarrierValue :
  HiggsSymbolicCarrierValue
canonicalHiggsSymbolicCarrierValue =
  symbolicHiggsCarrierFromMatterSurface
    Matter.canonicalHiggsDoubletPrimitive
    Matter.canonicalHiggsDoubletMatterRepresentation

data HiggsSymbolicNormSquaredValue : Set where
  suppliedSymbolicNormSquared :
    HiggsSymbolicCarrierValue →
    HiggsSymbolicNormSquaredValue

canonicalHiggsSymbolicNormSquaredValue :
  HiggsSymbolicNormSquaredValue
canonicalHiggsSymbolicNormSquaredValue =
  suppliedSymbolicNormSquared canonicalHiggsSymbolicCarrierValue

record HiggsSymbolicCarrierNormSquaredSemantics : Set where
  field
    normSquaredCarrier :
      HiggsSymbolicCarrierValue

    normSquaredCarrierIsCanonical :
      normSquaredCarrier
      ≡
      canonicalHiggsSymbolicCarrierValue

    normSquaredValue :
      HiggsSymbolicNormSquaredValue

    normSquaredValueIsCanonical :
      normSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    suppliesSymbolicCarrierNormSquared :
      Bool

    suppliesSymbolicCarrierNormSquaredIsTrue :
      suppliesSymbolicCarrierNormSquared ≡ true

    suppliesScalarFieldValues :
      Bool

    suppliesScalarFieldValuesIsFalse :
      suppliesScalarFieldValues ≡ false

    suppliesNumericNormOrder :
      Bool

    suppliesNumericNormOrderIsFalse :
      suppliesNumericNormOrder ≡ false

    calibratesNormToPhysicalScale :
      Bool

    calibratesNormToPhysicalScaleIsFalse :
      calibratesNormToPhysicalScale ≡ false

    normSquaredSemanticsBoundary :
      List String

open HiggsSymbolicCarrierNormSquaredSemantics public

canonicalHiggsSymbolicCarrierNormSquaredSemantics :
  HiggsSymbolicCarrierNormSquaredSemantics
canonicalHiggsSymbolicCarrierNormSquaredSemantics =
  record
    { normSquaredCarrier =
        canonicalHiggsSymbolicCarrierValue
    ; normSquaredCarrierIsCanonical =
        refl
    ; normSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; normSquaredValueIsCanonical =
        refl
    ; suppliesSymbolicCarrierNormSquared =
        true
    ; suppliesSymbolicCarrierNormSquaredIsTrue =
        refl
    ; suppliesScalarFieldValues =
        false
    ; suppliesScalarFieldValuesIsFalse =
        refl
    ; suppliesNumericNormOrder =
        false
    ; suppliesNumericNormOrderIsFalse =
        refl
    ; calibratesNormToPhysicalScale =
        false
    ; calibratesNormToPhysicalScaleIsFalse =
        refl
    ; normSquaredSemanticsBoundary =
        "The symbolic Higgs carrier has a supplied norm-squared semantic value for the quartic expression"
        ∷ "This is not a scalar field value space, numeric ordered norm, minimization proof, W4 v_Higgs calibration, or promotion"
        ∷ []
    }

data HiggsSymbolicMuSquaredParameter : Set where
  suppliedSymbolicMuSquared :
    HiggsSymbolicMuSquaredParameter

data HiggsSymbolicLambdaParameter : Set where
  suppliedSymbolicLambda :
    HiggsSymbolicLambdaParameter

data HiggsSymbolicQuarticPotentialExpression : Set where
  suppliedMexicanHatQuarticExpression :
    HiggsSymbolicCarrierValue →
    HiggsSymbolicNormSquaredValue →
    HiggsSymbolicMuSquaredParameter →
    HiggsSymbolicLambdaParameter →
    HiggsSymbolicQuarticPotentialExpression

canonicalHiggsSymbolicQuarticPotentialExpression :
  HiggsSymbolicQuarticPotentialExpression
canonicalHiggsSymbolicQuarticPotentialExpression =
  suppliedMexicanHatQuarticExpression
    canonicalHiggsSymbolicCarrierValue
    canonicalHiggsSymbolicNormSquaredValue
    suppliedSymbolicMuSquared
    suppliedSymbolicLambda

data HiggsSymbolicScalarFieldValue : Set where
  suppliedSymbolicScalarFieldValue :
    HiggsSymbolicCarrierValue →
    HiggsSymbolicScalarFieldValue

canonicalHiggsSymbolicScalarFieldValue :
  HiggsSymbolicScalarFieldValue
canonicalHiggsSymbolicScalarFieldValue =
  suppliedSymbolicScalarFieldValue canonicalHiggsSymbolicCarrierValue

record HiggsCarrierScalarFieldValuesRequest : Set where
  field
    symbolicCarrierValue :
      HiggsSymbolicCarrierValue

    symbolicCarrierValueIsCanonical :
      symbolicCarrierValue
      ≡
      canonicalHiggsSymbolicCarrierValue

    symbolicScalarFieldValue :
      HiggsSymbolicScalarFieldValue

    symbolicScalarFieldValueIsCanonical :
      symbolicScalarFieldValue
      ≡
      canonicalHiggsSymbolicScalarFieldValue

    symbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    symbolicNormSquaredValueIsCanonical :
      symbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    scalarFieldValuesRecorded :
      Bool

    scalarFieldValuesRecordedIsTrue :
      scalarFieldValuesRecorded ≡ true

    numericScalarValuesSupplied :
      Bool

    numericScalarValuesSuppliedIsFalse :
      numericScalarValuesSupplied ≡ false

    normOrderSupplied :
      Bool

    normOrderSuppliedIsFalse :
      normOrderSupplied ≡ false

    scalarFieldValuesRequestBoundary :
      List String

open HiggsCarrierScalarFieldValuesRequest public

canonicalHiggsCarrierScalarFieldValuesRequest :
  HiggsCarrierScalarFieldValuesRequest
canonicalHiggsCarrierScalarFieldValuesRequest =
  record
    { symbolicCarrierValue =
        canonicalHiggsSymbolicCarrierValue
    ; symbolicCarrierValueIsCanonical =
        refl
    ; symbolicScalarFieldValue =
        canonicalHiggsSymbolicScalarFieldValue
    ; symbolicScalarFieldValueIsCanonical =
        refl
    ; symbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; symbolicNormSquaredValueIsCanonical =
        refl
    ; scalarFieldValuesRecorded =
        true
    ; scalarFieldValuesRecordedIsTrue =
        refl
    ; numericScalarValuesSupplied =
        false
    ; numericScalarValuesSuppliedIsFalse =
        refl
    ; normOrderSupplied =
        false
    ; normOrderSuppliedIsFalse =
        refl
    ; scalarFieldValuesRequestBoundary =
        "Symbolic scalar-field values are recorded over the Higgs matter-surface carrier"
        ∷ "The values are carrier-level symbolic data only; no physical v_Higgs value or numeric field coordinates are supplied"
        ∷ "The next mathematical request is an ordered norm interface for minimization"
        ∷ []
    }

data HiggsCarrierNormOrderRequest : Set where
  suppliedHiggsCarrierNormOrderRequest :
    HiggsSymbolicScalarFieldValue →
    HiggsSymbolicNormSquaredValue →
    HiggsCarrierNormOrderRequest

canonicalHiggsCarrierNormOrderRequest :
  HiggsCarrierNormOrderRequest
canonicalHiggsCarrierNormOrderRequest =
  suppliedHiggsCarrierNormOrderRequest
    canonicalHiggsSymbolicScalarFieldValue
    canonicalHiggsSymbolicNormSquaredValue

record HiggsCarrierNormOrderRequestSurface : Set where
  field
    scalarFieldValuesRequest :
      HiggsCarrierScalarFieldValuesRequest

    normOrderRequest :
      HiggsCarrierNormOrderRequest

    normOrderRequestIsCanonical :
      normOrderRequest
      ≡
      canonicalHiggsCarrierNormOrderRequest

    normOrderRequested :
      Bool

    normOrderRequestedIsTrue :
      normOrderRequested ≡ true

    normOrderSupplied :
      Bool

    normOrderSuppliedIsFalse :
      normOrderSupplied ≡ false

    normOrderCalibratedToPhysicalScale :
      Bool

    normOrderCalibratedToPhysicalScaleIsFalse :
      normOrderCalibratedToPhysicalScale ≡ false

    normOrderRequestBoundary :
      List String

open HiggsCarrierNormOrderRequestSurface public

canonicalHiggsCarrierNormOrderRequestSurface :
  HiggsCarrierNormOrderRequestSurface
canonicalHiggsCarrierNormOrderRequestSurface =
  record
    { scalarFieldValuesRequest =
        canonicalHiggsCarrierScalarFieldValuesRequest
    ; normOrderRequest =
        canonicalHiggsCarrierNormOrderRequest
    ; normOrderRequestIsCanonical =
        refl
    ; normOrderRequested =
        true
    ; normOrderRequestedIsTrue =
        refl
    ; normOrderSupplied =
        false
    ; normOrderSuppliedIsFalse =
        refl
    ; normOrderCalibratedToPhysicalScale =
        false
    ; normOrderCalibratedToPhysicalScaleIsFalse =
        refl
    ; normOrderRequestBoundary =
        "The norm/order interface is requested for the symbolic Higgs scalar field values"
        ∷ "No ordered real norm, minimization theorem, or W4 scale calibration is supplied here"
        ∷ []
    }

data HiggsConditionalMexicanHatArgminHypothesis : Set where
  suppliedConditionalMexicanHatArgminHypothesis :
    HiggsCarrierNormOrderRequest →
    HiggsSymbolicQuarticPotentialExpression →
    HiggsConditionalMexicanHatArgminHypothesis

canonicalHiggsConditionalMexicanHatArgminHypothesis :
  HiggsConditionalMexicanHatArgminHypothesis
canonicalHiggsConditionalMexicanHatArgminHypothesis =
  suppliedConditionalMexicanHatArgminHypothesis
    canonicalHiggsCarrierNormOrderRequest
    canonicalHiggsSymbolicQuarticPotentialExpression

data HiggsMexicanHatCompletingSquareArgminRequest : Set where
  requestedCompletingSquareArgminForMexicanHat :
    HiggsCarrierNormOrderRequest →
    HiggsSymbolicQuarticPotentialExpression →
    HiggsMexicanHatCompletingSquareArgminRequest

canonicalHiggsMexicanHatCompletingSquareArgminRequest :
  HiggsMexicanHatCompletingSquareArgminRequest
canonicalHiggsMexicanHatCompletingSquareArgminRequest =
  requestedCompletingSquareArgminForMexicanHat
    canonicalHiggsCarrierNormOrderRequest
    canonicalHiggsSymbolicQuarticPotentialExpression

record HiggsConditionalMexicanHatArgminRequest : Set where
  field
    normOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    conditionalArgminHypothesis :
      HiggsConditionalMexicanHatArgminHypothesis

    conditionalArgminHypothesisIsCanonical :
      conditionalArgminHypothesis
      ≡
      canonicalHiggsConditionalMexicanHatArgminHypothesis

    completingSquareArgminRequest :
      HiggsMexicanHatCompletingSquareArgminRequest

    completingSquareArgminRequestIsCanonical :
      completingSquareArgminRequest
      ≡
      canonicalHiggsMexicanHatCompletingSquareArgminRequest

    conditionalArgminRequested :
      Bool

    conditionalArgminRequestedIsTrue :
      conditionalArgminRequested ≡ true

    completingSquareArgminRequested :
      Bool

    completingSquareArgminRequestedIsTrue :
      completingSquareArgminRequested ≡ true

    completingSquareArgminProofSupplied :
      Bool

    completingSquareArgminProofSuppliedIsFalse :
      completingSquareArgminProofSupplied ≡ false

    positiveLambdaAndNegativeMuSquaredSupplied :
      Bool

    positiveLambdaAndNegativeMuSquaredSuppliedIsFalse :
      positiveLambdaAndNegativeMuSquaredSupplied ≡ false

    argminCircleProofSupplied :
      Bool

    argminCircleProofSuppliedIsFalse :
      argminCircleProofSupplied ≡ false

    nonzeroVEVProofSupplied :
      Bool

    nonzeroVEVProofSuppliedIsFalse :
      nonzeroVEVProofSupplied ≡ false

    vHiggsStillAdapter4 :
      Bool

    vHiggsStillAdapter4IsTrue :
      vHiggsStillAdapter4 ≡ true

    conditionalArgminRequestBoundary :
      List String

open HiggsConditionalMexicanHatArgminRequest public

canonicalHiggsConditionalMexicanHatArgminRequest :
  HiggsConditionalMexicanHatArgminRequest
canonicalHiggsConditionalMexicanHatArgminRequest =
  record
    { normOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; conditionalArgminHypothesis =
        canonicalHiggsConditionalMexicanHatArgminHypothesis
    ; conditionalArgminHypothesisIsCanonical =
        refl
    ; completingSquareArgminRequest =
        canonicalHiggsMexicanHatCompletingSquareArgminRequest
    ; completingSquareArgminRequestIsCanonical =
        refl
    ; conditionalArgminRequested =
        true
    ; conditionalArgminRequestedIsTrue =
        refl
    ; completingSquareArgminRequested =
        true
    ; completingSquareArgminRequestedIsTrue =
        refl
    ; completingSquareArgminProofSupplied =
        false
    ; completingSquareArgminProofSuppliedIsFalse =
        refl
    ; positiveLambdaAndNegativeMuSquaredSupplied =
        false
    ; positiveLambdaAndNegativeMuSquaredSuppliedIsFalse =
        refl
    ; argminCircleProofSupplied =
        false
    ; argminCircleProofSuppliedIsFalse =
        refl
    ; nonzeroVEVProofSupplied =
        false
    ; nonzeroVEVProofSuppliedIsFalse =
        refl
    ; vHiggsStillAdapter4 =
        true
    ; vHiggsStillAdapter4IsTrue =
        refl
    ; conditionalArgminRequestBoundary =
        "Conditional Mexican-hat argmin is requested from norm/order plus signed mu/lambda evidence"
        ∷ "Completing-square minimization is named as the exact internal proof request, but no proof is supplied"
        ∷ "The request does not prove the argmin circle, nonzero VEV, residual gauge quotient, W/Z mass target, or photon masslessness"
        ∷ "The absolute v_Higgs scale remains outside this carrier route"
        ∷ []
    }

record HiggsSymbolicQuarticPotentialSurface : Set where
  field
    matterSurfacePrimitiveRequest :
      HiggsDoubletMatterSurfacePrimitiveRequest

    symbolicCarrierValue :
      HiggsSymbolicCarrierValue

    symbolicCarrierValueIsCanonical :
      symbolicCarrierValue
      ≡
      canonicalHiggsSymbolicCarrierValue

    symbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    symbolicNormSquaredValueIsCanonical :
      symbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    symbolicNormSquaredSemantics :
      HiggsSymbolicCarrierNormSquaredSemantics

    symbolicNormSquaredSemanticsIsCanonical :
      symbolicNormSquaredSemantics
      ≡
      canonicalHiggsSymbolicCarrierNormSquaredSemantics

    scalarFieldValuesRequest :
      HiggsCarrierScalarFieldValuesRequest

    scalarFieldValuesRequestIsCanonical :
      scalarFieldValuesRequest
      ≡
      canonicalHiggsCarrierScalarFieldValuesRequest

    suppliesSymbolicNormSquaredSemantics :
      Bool

    suppliesSymbolicNormSquaredSemanticsIsTrue :
      suppliesSymbolicNormSquaredSemantics ≡ true

    suppliesSymbolicScalarFieldValues :
      Bool

    suppliesSymbolicScalarFieldValuesIsTrue :
      suppliesSymbolicScalarFieldValues ≡ true

    symbolicMuSquaredParameter :
      HiggsSymbolicMuSquaredParameter

    symbolicMuSquaredParameterIsSupplied :
      symbolicMuSquaredParameter
      ≡
      suppliedSymbolicMuSquared

    symbolicLambdaParameter :
      HiggsSymbolicLambdaParameter

    symbolicLambdaParameterIsSupplied :
      symbolicLambdaParameter
      ≡
      suppliedSymbolicLambda

    symbolicQuarticPotentialExpression :
      HiggsSymbolicQuarticPotentialExpression

    symbolicQuarticPotentialExpressionIsCanonical :
      symbolicQuarticPotentialExpression
      ≡
      canonicalHiggsSymbolicQuarticPotentialExpression

    normOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    normOrderRequestSurfaceIsCanonical :
      normOrderRequestSurface
      ≡
      canonicalHiggsCarrierNormOrderRequestSurface

    conditionalArgminRequest :
      HiggsConditionalMexicanHatArgminRequest

    conditionalArgminRequestIsCanonical :
      conditionalArgminRequest
      ≡
      canonicalHiggsConditionalMexicanHatArgminRequest

    symbolicQuarticPotentialSurfaceConstructed :
      Bool

    symbolicQuarticPotentialSurfaceConstructedIsTrue :
      symbolicQuarticPotentialSurfaceConstructed ≡ true

    suppliesNumericNormOrOrder :
      Bool

    suppliesNumericNormOrOrderIsFalse :
      suppliesNumericNormOrOrder ≡ false

    calibratesMuLambda :
      Bool

    calibratesMuLambdaIsFalse :
      calibratesMuLambda ≡ false

    provesArgminCircle :
      Bool

    provesArgminCircleIsFalse :
      provesArgminCircle ≡ false

    derivesNonzeroVEV :
      Bool

    derivesNonzeroVEVIsFalse :
      derivesNonzeroVEV ≡ false

    keepsVHiggsAdapter4 :
      Bool

    keepsVHiggsAdapter4IsTrue :
      keepsVHiggsAdapter4 ≡ true

    remainingQuarticBlockers :
      List HiggsCarrierQuarticPotentialBlocker

    remainingQuarticBlockersAreCanonical :
      remainingQuarticBlockers
      ≡
      canonicalHiggsCarrierQuarticPotentialBlockersAfterScalarValues

    symbolicQuarticSurfaceBoundary :
      List String

open HiggsSymbolicQuarticPotentialSurface public

canonicalHiggsSymbolicQuarticPotentialSurface :
  HiggsSymbolicQuarticPotentialSurface
canonicalHiggsSymbolicQuarticPotentialSurface =
  record
    { matterSurfacePrimitiveRequest =
        canonicalHiggsDoubletMatterSurfacePrimitiveRequest
    ; symbolicCarrierValue =
        canonicalHiggsSymbolicCarrierValue
    ; symbolicCarrierValueIsCanonical =
        refl
    ; symbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; symbolicNormSquaredValueIsCanonical =
        refl
    ; symbolicNormSquaredSemantics =
        canonicalHiggsSymbolicCarrierNormSquaredSemantics
    ; symbolicNormSquaredSemanticsIsCanonical =
        refl
    ; scalarFieldValuesRequest =
        canonicalHiggsCarrierScalarFieldValuesRequest
    ; scalarFieldValuesRequestIsCanonical =
        refl
    ; suppliesSymbolicNormSquaredSemantics =
        true
    ; suppliesSymbolicNormSquaredSemanticsIsTrue =
        refl
    ; suppliesSymbolicScalarFieldValues =
        true
    ; suppliesSymbolicScalarFieldValuesIsTrue =
        refl
    ; symbolicMuSquaredParameter =
        suppliedSymbolicMuSquared
    ; symbolicMuSquaredParameterIsSupplied =
        refl
    ; symbolicLambdaParameter =
        suppliedSymbolicLambda
    ; symbolicLambdaParameterIsSupplied =
        refl
    ; symbolicQuarticPotentialExpression =
        canonicalHiggsSymbolicQuarticPotentialExpression
    ; symbolicQuarticPotentialExpressionIsCanonical =
        refl
    ; normOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; normOrderRequestSurfaceIsCanonical =
        refl
    ; conditionalArgminRequest =
        canonicalHiggsConditionalMexicanHatArgminRequest
    ; conditionalArgminRequestIsCanonical =
        refl
    ; symbolicQuarticPotentialSurfaceConstructed =
        true
    ; symbolicQuarticPotentialSurfaceConstructedIsTrue =
        refl
    ; suppliesNumericNormOrOrder =
        false
    ; suppliesNumericNormOrOrderIsFalse =
        refl
    ; calibratesMuLambda =
        false
    ; calibratesMuLambdaIsFalse =
        refl
    ; provesArgminCircle =
        false
    ; provesArgminCircleIsFalse =
        refl
    ; derivesNonzeroVEV =
        false
    ; derivesNonzeroVEVIsFalse =
        refl
    ; keepsVHiggsAdapter4 =
        true
    ; keepsVHiggsAdapter4IsTrue =
        refl
    ; remainingQuarticBlockers =
        canonicalHiggsCarrierQuarticPotentialBlockersAfterScalarValues
    ; remainingQuarticBlockersAreCanonical =
        refl
    ; symbolicQuarticSurfaceBoundary =
        "Symbolic Higgs carrier is built from Matter.canonicalHiggsDoubletPrimitive and Matter.canonicalHiggsDoubletMatterRepresentation"
        ∷ "Symbolic scalar-field values are now recorded for the carrier-level route"
        ∷ "The local Mexican-hat expression is parameter supplied over symbolic scalar/norm data, mu^2 parameter, and lambda parameter"
        ∷ "The exact remaining blockers are norm/order, mu/lambda calibration, argmin-circle proof, and nonzero VEV proof"
        ∷ "The norm/order and conditional argmin requests are present, but the ordered norm and minimization proof are not supplied"
        ∷ "No W4 v_Higgs calibration, residual gauge quotient, W/Z mass target, photon-massless target, or Higgs promotion is introduced"
        ∷ []
    }

record HiggsCarrierQuarticPotentialRequest : Setω where
  field
    scalarCarrierDefinitionRequest :
      HiggsScalarCarrierDefinitionRequest

    scalarCarrierDefinitionSurface :
      HiggsScalarCarrierDefinitionSurface

    symbolicQuarticPotentialSurface :
      HiggsSymbolicQuarticPotentialSurface

    scalarFieldValuesRequest :
      HiggsCarrierScalarFieldValuesRequest

    normOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    conditionalMexicanHatArgminRequest :
      HiggsConditionalMexicanHatArgminRequest

    scalarCarrierTarget :
      Set

    scalarNormSquaredTarget :
      scalarCarrierTarget →
      Set

    quarticPotentialFunctionalTarget :
      scalarCarrierTarget →
      Set

    positiveQuarticCouplingWitnessTarget :
      Set

    carrierNegativeMassSquaredWitnessTarget :
      Set

    mexicanHatShapeProofTarget :
      Set

    carrierArgminCircleProofTarget :
      Set

    nonzeroVEVFromArgminTarget :
      Set

    quarticBlockers :
      List HiggsCarrierQuarticPotentialBlocker

    firstQuarticBlocker :
      HiggsCarrierQuarticPotentialBlocker

    symbolicScalarFieldValuesRecorded :
      Bool

    symbolicScalarFieldValuesRecordedIsTrue :
      symbolicScalarFieldValuesRecorded ≡ true

    normOrderRequested :
      Bool

    normOrderRequestedIsTrue :
      normOrderRequested ≡ true

    conditionalArgminRequested :
      Bool

    conditionalArgminRequestedIsTrue :
      conditionalArgminRequested ≡ true

    scalarCarrierConstructed :
      Bool

    scalarCarrierConstructedIsFalse :
      scalarCarrierConstructed ≡ false

    quarticPotentialConstructed :
      Bool

    quarticPotentialConstructedIsFalse :
      quarticPotentialConstructed ≡ false

    signWitnessesConstructed :
      Bool

    signWitnessesConstructedIsFalse :
      signWitnessesConstructed ≡ false

    argminCircleProved :
      Bool

    argminCircleProvedIsFalse :
      argminCircleProved ≡ false

    quarticRequestBoundary :
      List String

open HiggsCarrierQuarticPotentialRequest public

record HiggsMexicanHatAdapterRequest : Setω where
  field
    higgsFieldTarget :
      Set

    carrierPotentialTarget :
      higgsFieldTarget →
      Set

    mexicanHatShapeTarget :
      Set

    positiveLambdaWitnessTarget :
      Set

    negativeMassSquaredWitnessTarget :
      Set

    argminCircleTarget :
      Set

    nonzeroVEVTarget :
      Set

    residualGaugeTarget :
      Set

    carrierQuarticPotentialRequest :
      HiggsCarrierQuarticPotentialRequest

    blockers :
      List HiggsPotentialShapeBlocker

    firstShapeBlocker :
      HiggsPotentialShapeBlocker

    shapeConstructed :
      Bool

    shapeConstructedIsFalse :
      shapeConstructed ≡ false

    nonzeroVEVConstructed :
      Bool

    nonzeroVEVConstructedIsFalse :
      nonzeroVEVConstructed ≡ false

    residualGaugeConstructed :
      Bool

    residualGaugeConstructedIsFalse :
      residualGaugeConstructed ≡ false

    physicalScaleCalibratedByW4 :
      Bool

    physicalScaleCalibratedByW4IsFalse :
      physicalScaleCalibratedByW4 ≡ false

    vHiggsStillAdapter4 :
      Bool

    vHiggsStillAdapter4IsTrue :
      vHiggsStillAdapter4 ≡ true

    requestBoundary :
      List String

open HiggsMexicanHatAdapterRequest public

record HiggsSymmetryBreakingDependencyReceipt : Set where
  field
    dependencies :
      List HiggsSymmetryBreakingDependency

    dependenciesAreCanonical :
      dependencies
      ≡
      canonicalHiggsSymmetryBreakingDependencies

    firstMathematicalBlocker :
      HiggsSymmetryBreakingDependency

    firstGovernanceBlocker :
      HiggsSymmetryBreakingDependency

    mexicanHatPotentialConstructed :
      Bool

    mexicanHatPotentialConstructedIsFalse :
      mexicanHatPotentialConstructed ≡ false

    nonzeroVEVProvedInternally :
      Bool

    nonzeroVEVProvedInternallyIsFalse :
      nonzeroVEVProvedInternally ≡ false

    vHiggsDerivedInternally :
      Bool

    vHiggsDerivedInternallyIsFalse :
      vHiggsDerivedInternally ≡ false

    vHiggsDerivedFromLaneDimension :
      Bool

    vHiggsDerivedFromLaneDimensionIsFalse :
      vHiggsDerivedFromLaneDimension ≡ false

    externalW4AuthorityAvailable :
      Bool

    externalW4AuthorityAvailableIsFalse :
      externalW4AuthorityAvailable ≡ false

    vHiggsAdapter4Boundary :
      Bool

    vHiggsAdapter4BoundaryIsTrue :
      vHiggsAdapter4Boundary ≡ true

    noHiggsPromotionFromDependencyReceipt :
      Bool

    noHiggsPromotionFromDependencyReceiptIsFalse :
      noHiggsPromotionFromDependencyReceipt ≡ false

open HiggsSymmetryBreakingDependencyReceipt public

canonicalHiggsSymmetryBreakingDependencyReceipt :
  HiggsSymmetryBreakingDependencyReceipt
canonicalHiggsSymmetryBreakingDependencyReceipt =
  record
    { dependencies =
        canonicalHiggsSymmetryBreakingDependencies
    ; dependenciesAreCanonical =
        refl
    ; firstMathematicalBlocker =
        carrierMexicanHatPotentialDependency
    ; firstGovernanceBlocker =
        w4PhysicalCalibrationDependency
    ; mexicanHatPotentialConstructed =
        false
    ; mexicanHatPotentialConstructedIsFalse =
        refl
    ; nonzeroVEVProvedInternally =
        false
    ; nonzeroVEVProvedInternallyIsFalse =
        refl
    ; vHiggsDerivedInternally =
        false
    ; vHiggsDerivedInternallyIsFalse =
        refl
    ; vHiggsDerivedFromLaneDimension =
        false
    ; vHiggsDerivedFromLaneDimensionIsFalse =
        refl
    ; externalW4AuthorityAvailable =
        false
    ; externalW4AuthorityAvailableIsFalse =
        refl
    ; vHiggsAdapter4Boundary =
        true
    ; vHiggsAdapter4BoundaryIsTrue =
        refl
    ; noHiggsPromotionFromDependencyReceipt =
        false
    ; noHiggsPromotionFromDependencyReceiptIsFalse =
        refl
    }

higgsSymmetryBreakingDependencyReceiptKeepsVHiggsAdapter4Boundary :
  vHiggsAdapter4Boundary canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  true
higgsSymmetryBreakingDependencyReceiptKeepsVHiggsAdapter4Boundary =
  refl

data PreBreakingGauge : Set where
  preBreakingGaugeTargetOnly :
    PreBreakingGauge

data PostBreakingGauge : Set where
  postBreakingGaugeTargetOnly :
    PostBreakingGauge

data HiggsField : Set where
  higgsFieldTargetOnly :
    HiggsField

data HiggsVEV : HiggsField → Set where
  higgsVEVTargetOnly :
    HiggsVEV higgsFieldTargetOnly

data ResidualGauge : Set where
  residualGaugeTargetOnly :
    ResidualGauge

abstractPreBreakingGauge :
  PreBreakingGauge
abstractPreBreakingGauge =
  preBreakingGaugeTargetOnly

abstractPostBreakingGauge :
  PostBreakingGauge
abstractPostBreakingGauge =
  postBreakingGaugeTargetOnly

abstractHiggsField :
  HiggsField
abstractHiggsField =
  higgsFieldTargetOnly

abstractVEV :
  HiggsVEV abstractHiggsField
abstractVEV =
  higgsVEVTargetOnly

data VEVNonzeroTarget : Set where
  vEVNonzeroTargetOnly :
    VEVNonzeroTarget

abstractVEVNonzeroTarget :
  Set
abstractVEVNonzeroTarget =
  VEVNonzeroTarget

abstractResidualGauge :
  ResidualGauge
abstractResidualGauge =
  residualGaugeTargetOnly

data WMassTarget : Set where
  wMassTargetOnly :
    WMassTarget

abstractWMassTarget :
  Set
abstractWMassTarget =
  WMassTarget

data ZMassTarget : Set where
  zMassTargetOnly :
    ZMassTarget

abstractZMassTarget :
  Set
abstractZMassTarget =
  ZMassTarget

data PhotonMasslessTarget : Set where
  photonMasslessTargetOnly :
    PhotonMasslessTarget

abstractPhotonMasslessTarget :
  Set
abstractPhotonMasslessTarget =
  PhotonMasslessTarget

canonicalHiggsCarrierQuarticPotentialRequest :
  HiggsCarrierQuarticPotentialRequest
canonicalHiggsCarrierQuarticPotentialRequest =
  record
    { scalarCarrierDefinitionRequest =
        canonicalHiggsScalarCarrierDefinitionRequest
    ; scalarCarrierDefinitionSurface =
        canonicalHiggsScalarCarrierDefinitionSurface
    ; symbolicQuarticPotentialSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; scalarFieldValuesRequest =
        canonicalHiggsCarrierScalarFieldValuesRequest
    ; normOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; conditionalMexicanHatArgminRequest =
        canonicalHiggsConditionalMexicanHatArgminRequest
    ; scalarCarrierTarget =
        HiggsField
    ; scalarNormSquaredTarget =
        λ _ → HiggsField
    ; quarticPotentialFunctionalTarget =
        λ _ → HiggsField
    ; positiveQuarticCouplingWitnessTarget =
        HiggsField
    ; carrierNegativeMassSquaredWitnessTarget =
        HiggsField
    ; mexicanHatShapeProofTarget =
        HiggsField
    ; carrierArgminCircleProofTarget =
        HiggsField
    ; nonzeroVEVFromArgminTarget =
        abstractVEVNonzeroTarget
    ; quarticBlockers =
        canonicalHiggsCarrierQuarticPotentialBlockersAfterScalarValues
    ; firstQuarticBlocker =
        missingCarrierNormOrder
    ; symbolicScalarFieldValuesRecorded =
        true
    ; symbolicScalarFieldValuesRecordedIsTrue =
        refl
    ; normOrderRequested =
        true
    ; normOrderRequestedIsTrue =
        refl
    ; conditionalArgminRequested =
        true
    ; conditionalArgminRequestedIsTrue =
        refl
    ; scalarCarrierConstructed =
        false
    ; scalarCarrierConstructedIsFalse =
        refl
    ; quarticPotentialConstructed =
        false
    ; quarticPotentialConstructedIsFalse =
        refl
    ; signWitnessesConstructed =
        false
    ; signWitnessesConstructedIsFalse =
        refl
    ; argminCircleProved =
        false
    ; argminCircleProvedIsFalse =
        refl
    ; quarticRequestBoundary =
        "MatterRepresentationReceiptSurface now supplies the Higgs-doublet representation constructors used by the local symbolic carrier"
        ∷ "A symbolic quartic Mexican-hat expression, scalar-field value request, norm/order request, and conditional argmin request are recorded"
        ∷ "The exact next blocker is missingCarrierNormOrder; mu/lambda calibration, argmin-circle proof, and nonzero VEV proof remain downstream"
        ∷ []
    }

canonicalHiggsMexicanHatAdapterRequest :
  HiggsMexicanHatAdapterRequest
canonicalHiggsMexicanHatAdapterRequest =
  record
    { higgsFieldTarget =
        HiggsField
    ; carrierPotentialTarget =
        λ _ → HiggsField
    ; mexicanHatShapeTarget =
        HiggsField
    ; positiveLambdaWitnessTarget =
        HiggsField
    ; negativeMassSquaredWitnessTarget =
        HiggsField
    ; argminCircleTarget =
        HiggsField
    ; nonzeroVEVTarget =
        abstractVEVNonzeroTarget
    ; residualGaugeTarget =
        ResidualGauge
    ; carrierQuarticPotentialRequest =
        canonicalHiggsCarrierQuarticPotentialRequest
    ; blockers =
        canonicalHiggsPotentialShapeBlockers
    ; firstShapeBlocker =
        missingPositiveLambdaWitness
    ; shapeConstructed =
        false
    ; shapeConstructedIsFalse =
        refl
    ; nonzeroVEVConstructed =
        false
    ; nonzeroVEVConstructedIsFalse =
        refl
    ; residualGaugeConstructed =
        false
    ; residualGaugeConstructedIsFalse =
        refl
    ; physicalScaleCalibratedByW4 =
        false
    ; physicalScaleCalibratedByW4IsFalse =
        refl
    ; vHiggsStillAdapter4 =
        true
    ; vHiggsStillAdapter4IsTrue =
        refl
    ; requestBoundary =
        "This request separates the pure carrier Mexican-hat shape from W4 physical scale calibration"
        ∷ "The local symbolic carrier quartic is present; exact shape still needs signed mu/lambda evidence and minimization"
        ∷ "Nonzero VEV and residual U(1) are downstream of the argmin-circle proof"
        ∷ "The absolute v_Higgs scale remains Adapter 4 even if the shape proof is supplied"
        ∷ []
    }

record HiggsSymmetryBreakingReceipt : Setω where
  field
    status :
      HiggsSymmetryBreakingStatus

    preBreakingGauge :
      PreBreakingGauge

    postBreakingGauge :
      PostBreakingGauge

    higgsField :
      HiggsField

    vev :
      HiggsVEV higgsField

    vevNonzeroTarget :
      Set

    residualGauge :
      ResidualGauge

    wMassTarget :
      Set

    zMassTarget :
      Set

    photonMasslessTarget :
      Set

    mexicanHatAdapterRequest :
      HiggsMexicanHatAdapterRequest

    openObligations :
      List HiggsSymmetryBreakingOpenObligation

    higgsSymmetryBreakingPromoted :
      Bool

    higgsSymmetryBreakingPromotedIsFalse :
      higgsSymmetryBreakingPromoted ≡ false

    adapterBoundary :
      List String

open HiggsSymmetryBreakingReceipt public

canonicalHiggsSymmetryBreakingReceipt :
  HiggsSymmetryBreakingReceipt
canonicalHiggsSymmetryBreakingReceipt =
  record
    { status =
        higgsSymmetryBreakingTargetsOnlyNoPromotion
    ; preBreakingGauge =
        abstractPreBreakingGauge
    ; postBreakingGauge =
        abstractPostBreakingGauge
    ; higgsField =
        abstractHiggsField
    ; vev =
        abstractVEV
    ; vevNonzeroTarget =
        abstractVEVNonzeroTarget
    ; residualGauge =
        abstractResidualGauge
    ; wMassTarget =
        abstractWMassTarget
    ; zMassTarget =
        abstractZMassTarget
    ; photonMasslessTarget =
        abstractPhotonMasslessTarget
    ; mexicanHatAdapterRequest =
        canonicalHiggsMexicanHatAdapterRequest
    ; openObligations =
        canonicalHiggsSymmetryBreakingOpenObligations
    ; higgsSymmetryBreakingPromoted =
        false
    ; higgsSymmetryBreakingPromotedIsFalse =
        refl
    ; adapterBoundary =
        "pre-breaking gauge, post-breaking gauge, Higgs field, Mexican-hat potential, nonzero vev, residual gauge, W/Z mass, and photon-massless statements are candidate targets only"
        ∷ "Mexican-hat potential and nonzero vev remain blocked until a physical calibration proof or authority receipt is supplied"
        ∷ "v_Higgs remains an Adapter 4 governance boundary; it is not derived from laneDimension and no terminal promotion is supplied"
        ∷ []
    }

higgsSymmetryBreakingDependencyReceiptKeepsMexicanHatOpen :
  mexicanHatPotentialConstructed canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  false
higgsSymmetryBreakingDependencyReceiptKeepsMexicanHatOpen =
  refl

higgsMexicanHatAdapterRequestFirstShapeBlocker :
  firstShapeBlocker canonicalHiggsMexicanHatAdapterRequest
  ≡
  missingPositiveLambdaWitness
higgsMexicanHatAdapterRequestFirstShapeBlocker =
  refl

higgsCarrierQuarticPotentialRequestFirstBlocker :
  firstQuarticBlocker canonicalHiggsCarrierQuarticPotentialRequest
  ≡
  missingCarrierNormOrder
higgsCarrierQuarticPotentialRequestFirstBlocker =
  refl

higgsScalarCarrierDefinitionRequestIsHiggsDoublet :
  matterSectorTarget canonicalHiggsScalarCarrierDefinitionRequest
  ≡
  Matter.higgsDoubletTarget
higgsScalarCarrierDefinitionRequestIsHiggsDoublet =
  refl

higgsScalarCarrierDefinitionRequestKeepsCarrierOpen :
  scalarCarrierDefinitionConstructed
    canonicalHiggsScalarCarrierDefinitionRequest
  ≡
  false
higgsScalarCarrierDefinitionRequestKeepsCarrierOpen =
  refl

higgsScalarCarrierDefinitionSurfaceRecordsHiggsDoublet :
  higgsScalarMatterTarget canonicalHiggsScalarCarrierDefinitionSurface
  ≡
  Matter.higgsDoubletTarget
higgsScalarCarrierDefinitionSurfaceRecordsHiggsDoublet =
  refl

higgsScalarCarrierDefinitionSurfaceKeepsCarrierOpen :
  higgsScalarCarrierDefinitionConstructed
    canonicalHiggsScalarCarrierDefinitionSurface
  ≡
  false
higgsScalarCarrierDefinitionSurfaceKeepsCarrierOpen =
  refl

higgsScalarCarrierDefinitionSurfaceKeepsW4Closed :
  higgsScalarW4CalibrationConstructed
    canonicalHiggsScalarCarrierDefinitionSurface
  ≡
  false
higgsScalarCarrierDefinitionSurfaceKeepsW4Closed =
  refl

higgsScalarCarrierPrimitiveWitnessRecordsHiggsDoublet :
  matterSectorTarget canonicalHiggsScalarCarrierPrimitiveWitness
  ≡
  Matter.higgsDoubletTarget
higgsScalarCarrierPrimitiveWitnessRecordsHiggsDoublet =
  refl

higgsScalarCarrierPrimitiveWitnessKeepsConcreteCarrierOpen :
  primitiveWitnessConstructsConcreteCarrier
    canonicalHiggsScalarCarrierPrimitiveWitness
  ≡
  false
higgsScalarCarrierPrimitiveWitnessKeepsConcreteCarrierOpen =
  refl

higgsScalarCarrierPrimitiveWitnessKeepsVEVCalibrationOpen :
  primitiveWitnessConstructsVEVOrCalibration
    canonicalHiggsScalarCarrierPrimitiveWitness
  ≡
  false
higgsScalarCarrierPrimitiveWitnessKeepsVEVCalibrationOpen =
  refl

higgsScalarCarrierPrimitiveWitnessKeepsPromotionClosed :
  primitiveWitnessPromotesHiggs
    canonicalHiggsScalarCarrierPrimitiveWitness
  ≡
  false
higgsScalarCarrierPrimitiveWitnessKeepsPromotionClosed =
  refl

higgsSymbolicQuarticPotentialSurfaceConstructed :
  symbolicQuarticPotentialSurfaceConstructed
    canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  true
higgsSymbolicQuarticPotentialSurfaceConstructed =
  refl

higgsSymbolicQuarticPotentialSurfaceSuppliesNormSquaredSemantics :
  suppliesSymbolicNormSquaredSemantics
    canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  true
higgsSymbolicQuarticPotentialSurfaceSuppliesNormSquaredSemantics =
  refl

higgsSymbolicQuarticPotentialSurfaceSuppliesScalarFieldValues :
  suppliesSymbolicScalarFieldValues
    canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  true
higgsSymbolicQuarticPotentialSurfaceSuppliesScalarFieldValues =
  refl

higgsCarrierScalarFieldValuesRequestRecordsSymbolicValues :
  scalarFieldValuesRecorded canonicalHiggsCarrierScalarFieldValuesRequest
  ≡
  true
higgsCarrierScalarFieldValuesRequestRecordsSymbolicValues =
  refl

higgsCarrierNormOrderRequestSurfaceRequestsOrder :
  normOrderRequested canonicalHiggsCarrierNormOrderRequestSurface
  ≡
  true
higgsCarrierNormOrderRequestSurfaceRequestsOrder =
  refl

higgsConditionalMexicanHatArgminRequestIsRequested :
  conditionalArgminRequested
    canonicalHiggsConditionalMexicanHatArgminRequest
  ≡
  true
higgsConditionalMexicanHatArgminRequestIsRequested =
  refl

higgsSymbolicCarrierNormSquaredSemanticsKeepsScalarValuesOpen :
  suppliesScalarFieldValues
    canonicalHiggsSymbolicCarrierNormSquaredSemantics
  ≡
  false
higgsSymbolicCarrierNormSquaredSemanticsKeepsScalarValuesOpen =
  refl

higgsSymbolicCarrierNormSquaredSemanticsKeepsNumericOrderOpen :
  suppliesNumericNormOrder
    canonicalHiggsSymbolicCarrierNormSquaredSemantics
  ≡
  false
higgsSymbolicCarrierNormSquaredSemanticsKeepsNumericOrderOpen =
  refl

higgsSymbolicQuarticPotentialSurfaceKeepsNormOpen :
  suppliesNumericNormOrOrder canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  false
higgsSymbolicQuarticPotentialSurfaceKeepsNormOpen =
  refl

higgsSymbolicQuarticPotentialSurfaceKeepsMuLambdaOpen :
  calibratesMuLambda canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  false
higgsSymbolicQuarticPotentialSurfaceKeepsMuLambdaOpen =
  refl

higgsSymbolicQuarticPotentialSurfaceKeepsArgminOpen :
  provesArgminCircle canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  false
higgsSymbolicQuarticPotentialSurfaceKeepsArgminOpen =
  refl

higgsSymbolicQuarticPotentialSurfaceKeepsVEVOpen :
  derivesNonzeroVEV canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  false
higgsSymbolicQuarticPotentialSurfaceKeepsVEVOpen =
  refl

higgsSymbolicQuarticPotentialSurfaceKeepsVHiggsAdapter4 :
  keepsVHiggsAdapter4 canonicalHiggsSymbolicQuarticPotentialSurface
  ≡
  true
higgsSymbolicQuarticPotentialSurfaceKeepsVHiggsAdapter4 =
  refl

higgsCarrierQuarticPotentialRequestUsesCarrierSurfaceHiggsTarget :
  higgsScalarMatterTarget
    (scalarCarrierDefinitionSurface canonicalHiggsCarrierQuarticPotentialRequest)
  ≡
  Matter.higgsDoubletTarget
higgsCarrierQuarticPotentialRequestUsesCarrierSurfaceHiggsTarget =
  refl

higgsCarrierQuarticPotentialRequestKeepsPotentialOpen :
  quarticPotentialConstructed canonicalHiggsCarrierQuarticPotentialRequest
  ≡
  false
higgsCarrierQuarticPotentialRequestKeepsPotentialOpen =
  refl

higgsCarrierQuarticPotentialRequestKeepsArgminOpen :
  argminCircleProved canonicalHiggsCarrierQuarticPotentialRequest
  ≡
  false
higgsCarrierQuarticPotentialRequestKeepsArgminOpen =
  refl

higgsMexicanHatAdapterRequestKeepsShapeOpen :
  shapeConstructed canonicalHiggsMexicanHatAdapterRequest
  ≡
  false
higgsMexicanHatAdapterRequestKeepsShapeOpen =
  refl

higgsMexicanHatAdapterRequestKeepsVHiggsAdapter4 :
  vHiggsStillAdapter4 canonicalHiggsMexicanHatAdapterRequest
  ≡
  true
higgsMexicanHatAdapterRequestKeepsVHiggsAdapter4 =
  refl

higgsSymmetryBreakingDependencyReceiptKeepsNonzeroVEVOpen :
  nonzeroVEVProvedInternally canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  false
higgsSymmetryBreakingDependencyReceiptKeepsNonzeroVEVOpen =
  refl

higgsSymmetryBreakingDependencyReceiptKeepsVHiggsAdapter4 :
  vHiggsAdapter4Boundary canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  true
higgsSymmetryBreakingDependencyReceiptKeepsVHiggsAdapter4 =
  refl

higgsSymmetryBreakingDependencyReceiptNoLaneDimensionVHiggs :
  vHiggsDerivedFromLaneDimension canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  false
higgsSymmetryBreakingDependencyReceiptNoLaneDimensionVHiggs =
  refl

higgsSymmetryBreakingDependencyReceiptNoExternalW4Authority :
  externalW4AuthorityAvailable canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  false
higgsSymmetryBreakingDependencyReceiptNoExternalW4Authority =
  refl

higgsSymmetryBreakingDependencyReceiptDoesNotPromote :
  noHiggsPromotionFromDependencyReceipt
    canonicalHiggsSymmetryBreakingDependencyReceipt
  ≡
  false
higgsSymmetryBreakingDependencyReceiptDoesNotPromote =
  refl

higgsSymmetryBreakingCanonicalReceiptStillNotPromoted :
  higgsSymmetryBreakingPromoted canonicalHiggsSymmetryBreakingReceipt
  ≡
  false
higgsSymmetryBreakingCanonicalReceiptStillNotPromoted =
  refl

data HiggsNormOrderedFieldSemanticsComponent : Set where
  suppliedSymbolicScalarFieldValueComponent :
    HiggsNormOrderedFieldSemanticsComponent

  suppliedSymbolicNormSquaredValueComponent :
    HiggsNormOrderedFieldSemanticsComponent

  suppliedSymbolicQuarticExpressionComponent :
    HiggsNormOrderedFieldSemanticsComponent

  requestedOrderedScalarFieldCarrierComponent :
    HiggsNormOrderedFieldSemanticsComponent

  requestedNonnegativeNormOrderComponent :
    HiggsNormOrderedFieldSemanticsComponent

  requestedNormSquaredOrderCompatibilityComponent :
    HiggsNormOrderedFieldSemanticsComponent

canonicalHiggsNormOrderedFieldSemanticsComponents :
  List HiggsNormOrderedFieldSemanticsComponent
canonicalHiggsNormOrderedFieldSemanticsComponents =
  suppliedSymbolicScalarFieldValueComponent
  ∷ suppliedSymbolicNormSquaredValueComponent
  ∷ suppliedSymbolicQuarticExpressionComponent
  ∷ requestedOrderedScalarFieldCarrierComponent
  ∷ requestedNonnegativeNormOrderComponent
  ∷ requestedNormSquaredOrderCompatibilityComponent
  ∷ []

record HiggsNormOrderedFieldSemanticsSuppliedInterface : Setω where
  field
    higgsNormOrderedFieldSymbolicQuarticSurface :
      HiggsSymbolicQuarticPotentialSurface

    higgsNormOrderedFieldNormOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    higgsNormOrderedFieldSymbolicNormSquaredSemantics :
      HiggsSymbolicCarrierNormSquaredSemantics

    higgsNormOrderedFieldComponents :
      List HiggsNormOrderedFieldSemanticsComponent

    higgsNormOrderedFieldComponentsAreCanonical :
      higgsNormOrderedFieldComponents
      ≡
      canonicalHiggsNormOrderedFieldSemanticsComponents

    higgsNormOrderedFieldCarrierTarget :
      Set

    higgsNormOrderedFieldCarrierTargetIsHiggsField :
      higgsNormOrderedFieldCarrierTarget
      ≡
      HiggsField

    higgsNormOrderedFieldValueTarget :
      Set

    higgsNormOrderedFieldNormSquaredValueTarget :
      Set

    higgsNormOrderedFieldOrderLawTarget :
      Set

    higgsNormSquaredOrderCompatibilityLawTarget :
      Set

    higgsNormOrderedFieldSymbolicInputsSupplied :
      Bool

    higgsNormOrderedFieldSymbolicInputsSuppliedIsTrue :
      higgsNormOrderedFieldSymbolicInputsSupplied ≡ true

    higgsNormOrderedFieldSemanticsSupplied :
      Bool

    higgsNormOrderedFieldSemanticsSuppliedIsFalse :
      higgsNormOrderedFieldSemanticsSupplied ≡ false

    higgsNormOrderedFieldW4ScaleSupplied :
      Bool

    higgsNormOrderedFieldW4ScaleSuppliedIsFalse :
      higgsNormOrderedFieldW4ScaleSupplied ≡ false

    higgsNormOrderedFieldInterfaceBoundary :
      List String

open HiggsNormOrderedFieldSemanticsSuppliedInterface public

canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface :
  HiggsNormOrderedFieldSemanticsSuppliedInterface
canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface =
  record
    { higgsNormOrderedFieldSymbolicQuarticSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; higgsNormOrderedFieldNormOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; higgsNormOrderedFieldSymbolicNormSquaredSemantics =
        canonicalHiggsSymbolicCarrierNormSquaredSemantics
    ; higgsNormOrderedFieldComponents =
        canonicalHiggsNormOrderedFieldSemanticsComponents
    ; higgsNormOrderedFieldComponentsAreCanonical =
        refl
    ; higgsNormOrderedFieldCarrierTarget =
        HiggsField
    ; higgsNormOrderedFieldCarrierTargetIsHiggsField =
        refl
    ; higgsNormOrderedFieldValueTarget =
        HiggsSymbolicScalarFieldValue
    ; higgsNormOrderedFieldNormSquaredValueTarget =
        HiggsSymbolicNormSquaredValue
    ; higgsNormOrderedFieldOrderLawTarget =
        HiggsCarrierNormOrderRequest
    ; higgsNormSquaredOrderCompatibilityLawTarget =
        HiggsCarrierNormOrderRequestSurface
    ; higgsNormOrderedFieldSymbolicInputsSupplied =
        true
    ; higgsNormOrderedFieldSymbolicInputsSuppliedIsTrue =
        refl
    ; higgsNormOrderedFieldSemanticsSupplied =
        false
    ; higgsNormOrderedFieldSemanticsSuppliedIsFalse =
        refl
    ; higgsNormOrderedFieldW4ScaleSupplied =
        false
    ; higgsNormOrderedFieldW4ScaleSuppliedIsFalse =
        refl
    ; higgsNormOrderedFieldInterfaceBoundary =
        "Symbolic scalar value, norm-squared value, and quartic expression are supplied"
        ∷ "The requested ordered-field law and norm-squared/order compatibility are typed targets only"
        ∷ "No numeric ordered real field, minimization theorem, W4 scale, or Higgs promotion is supplied"
        ∷ []
    }

record HiggsNormOrderedFieldSemanticsAbsenceLedger : Setω where
  field
    higgsNormOrderedFieldSuppliedInterface :
      HiggsNormOrderedFieldSemanticsSuppliedInterface

    higgsNormOrderedFieldQuarticRequest :
      HiggsCarrierQuarticPotentialRequest

    higgsNormOrderedFieldFirstQuarticBlocker :
      HiggsCarrierQuarticPotentialBlocker

    higgsNormOrderedFieldFirstQuarticBlockerIsNormOrder :
      higgsNormOrderedFieldFirstQuarticBlocker
      ≡
      missingCarrierNormOrder

    higgsNormOrderedFieldSymbolicSurfaceSuppliesNormSquared :
      suppliesSymbolicNormSquaredSemantics
        canonicalHiggsSymbolicQuarticPotentialSurface
      ≡
      true

    higgsNormOrderedFieldNumericNormOrderAvailable :
      Bool

    higgsNormOrderedFieldNumericNormOrderAvailableIsFalse :
      higgsNormOrderedFieldNumericNormOrderAvailable ≡ false

    higgsNormOrderedFieldPhysicalW4AuthorityAvailable :
      externalW4AuthorityAvailable
        canonicalHiggsSymmetryBreakingDependencyReceipt
      ≡
      false

    higgsNormOrderedFieldLedgerPromoted :
      Bool

    higgsNormOrderedFieldLedgerPromotedIsFalse :
      higgsNormOrderedFieldLedgerPromoted ≡ false

    higgsNormOrderedFieldAbsenceBoundary :
      List String

open HiggsNormOrderedFieldSemanticsAbsenceLedger public

canonicalHiggsNormOrderedFieldSemanticsAbsenceLedger :
  HiggsNormOrderedFieldSemanticsAbsenceLedger
canonicalHiggsNormOrderedFieldSemanticsAbsenceLedger =
  record
    { higgsNormOrderedFieldSuppliedInterface =
        canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface
    ; higgsNormOrderedFieldQuarticRequest =
        canonicalHiggsCarrierQuarticPotentialRequest
    ; higgsNormOrderedFieldFirstQuarticBlocker =
        missingCarrierNormOrder
    ; higgsNormOrderedFieldFirstQuarticBlockerIsNormOrder =
        refl
    ; higgsNormOrderedFieldSymbolicSurfaceSuppliesNormSquared =
        refl
    ; higgsNormOrderedFieldNumericNormOrderAvailable =
        false
    ; higgsNormOrderedFieldNumericNormOrderAvailableIsFalse =
        refl
    ; higgsNormOrderedFieldPhysicalW4AuthorityAvailable =
        refl
    ; higgsNormOrderedFieldLedgerPromoted =
        false
    ; higgsNormOrderedFieldLedgerPromotedIsFalse =
        refl
    ; higgsNormOrderedFieldAbsenceBoundary =
        "Exact supplied-interface gap: symbolic norm-squared data is present, but ordered-field semantics is not"
        ∷ "Exact order gap: no inhabitant supplies numeric/nonnegative norm order or compatibility with the symbolic norm-squared value"
        ∷ "Exact W4 gap: external W4 authority remains unavailable and v_Higgs remains an Adapter 4 boundary"
        ∷ "The ledger records typed holes only and keeps Higgs promotion false"
        ∷ []
    }

higgsNormOrderedFieldSemanticsLedgerFirstBlocker :
  higgsNormOrderedFieldFirstQuarticBlocker
    canonicalHiggsNormOrderedFieldSemanticsAbsenceLedger
  ≡
  missingCarrierNormOrder
higgsNormOrderedFieldSemanticsLedgerFirstBlocker =
  refl

higgsNormOrderedFieldSemanticsInterfaceDoesNotSupplyOrder :
  higgsNormOrderedFieldSemanticsSupplied
    canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface
  ≡
  false
higgsNormOrderedFieldSemanticsInterfaceDoesNotSupplyOrder =
  refl

higgsNormOrderedFieldSemanticsLedgerDoesNotPromote :
  higgsNormOrderedFieldLedgerPromoted
    canonicalHiggsNormOrderedFieldSemanticsAbsenceLedger
  ≡
  false
higgsNormOrderedFieldSemanticsLedgerDoesNotPromote =
  refl

higgsNormOrderedFieldSemanticsLedgerKeepsW4External :
  higgsNormOrderedFieldPhysicalW4AuthorityAvailable
    canonicalHiggsNormOrderedFieldSemanticsAbsenceLedger
  ≡
  refl
higgsNormOrderedFieldSemanticsLedgerKeepsW4External =
  refl

data HiggsPositiveParameterConditionalComponent : Set where
  requestedMuSquaredGreaterThanZeroComponent :
    HiggsPositiveParameterConditionalComponent

  requestedLambdaGreaterThanZeroComponent :
    HiggsPositiveParameterConditionalComponent

  requestedOrderedComplexNormComponent :
    HiggsPositiveParameterConditionalComponent

  requestedMexicanHatArgminComponent :
    HiggsPositiveParameterConditionalComponent

  requestedNonzeroVEVConclusionComponent :
    HiggsPositiveParameterConditionalComponent

  requestedResidualU1EMTargetComponent :
    HiggsPositiveParameterConditionalComponent

canonicalHiggsPositiveParameterConditionalComponents :
  List HiggsPositiveParameterConditionalComponent
canonicalHiggsPositiveParameterConditionalComponents =
  requestedMuSquaredGreaterThanZeroComponent
  ∷ requestedLambdaGreaterThanZeroComponent
  ∷ requestedOrderedComplexNormComponent
  ∷ requestedMexicanHatArgminComponent
  ∷ requestedNonzeroVEVConclusionComponent
  ∷ requestedResidualU1EMTargetComponent
  ∷ []

data HiggsMuSquaredPositiveWitnessRequest : Set where
  requestedMuSquaredGreaterThanZeroWitness :
    HiggsSymbolicMuSquaredParameter →
    HiggsMuSquaredPositiveWitnessRequest

canonicalHiggsMuSquaredPositiveWitnessRequest :
  HiggsMuSquaredPositiveWitnessRequest
canonicalHiggsMuSquaredPositiveWitnessRequest =
  requestedMuSquaredGreaterThanZeroWitness suppliedSymbolicMuSquared

data HiggsLambdaPositiveWitnessRequest : Set where
  requestedLambdaGreaterThanZeroWitness :
    HiggsSymbolicLambdaParameter →
    HiggsLambdaPositiveWitnessRequest

canonicalHiggsLambdaPositiveWitnessRequest :
  HiggsLambdaPositiveWitnessRequest
canonicalHiggsLambdaPositiveWitnessRequest =
  requestedLambdaGreaterThanZeroWitness suppliedSymbolicLambda

data HiggsResidualGaugeTarget : Set where
  residualU1EMTarget :
    HiggsResidualGaugeTarget

canonicalHiggsResidualGaugeTarget :
  HiggsResidualGaugeTarget
canonicalHiggsResidualGaugeTarget =
  residualU1EMTarget

data HiggsConditionalNonzeroVEVConclusionTarget : Set where
  requestedNonzeroVEVConclusion :
    HiggsVEV abstractHiggsField →
    HiggsConditionalNonzeroVEVConclusionTarget

canonicalHiggsConditionalNonzeroVEVConclusionTarget :
  HiggsConditionalNonzeroVEVConclusionTarget
canonicalHiggsConditionalNonzeroVEVConclusionTarget =
  requestedNonzeroVEVConclusion abstractVEV

data HiggsResidualU1EMParameterTarget : Set where
  requestedResidualU1EMGaugeParameter :
    HiggsResidualU1EMParameterTarget

canonicalHiggsResidualU1EMParameterTarget :
  HiggsResidualU1EMParameterTarget
canonicalHiggsResidualU1EMParameterTarget =
  requestedResidualU1EMGaugeParameter

record HiggsResidualU1EMParameterRequest : Set where
  field
    residualGaugeTarget :
      HiggsResidualGaugeTarget

    residualGaugeTargetIsU1EM :
      residualGaugeTarget
      ≡
      residualU1EMTarget

    residualGaugeParameterTarget :
      HiggsResidualU1EMParameterTarget

    residualGaugeParameterTargetIsCanonical :
      residualGaugeParameterTarget
      ≡
      canonicalHiggsResidualU1EMParameterTarget

    residualParameterRequested :
      Bool

    residualParameterRequestedIsTrue :
      residualParameterRequested ≡ true

    residualParameterSupplied :
      Bool

    residualParameterSuppliedIsFalse :
      residualParameterSupplied ≡ false

    residualU1EMQuotientProofSupplied :
      Bool

    residualU1EMQuotientProofSuppliedIsFalse :
      residualU1EMQuotientProofSupplied ≡ false

    photonMasslessnessProofSupplied :
      Bool

    photonMasslessnessProofSuppliedIsFalse :
      photonMasslessnessProofSupplied ≡ false

    residualU1EMParameterBoundary :
      List String

open HiggsResidualU1EMParameterRequest public

canonicalHiggsResidualU1EMParameterRequest :
  HiggsResidualU1EMParameterRequest
canonicalHiggsResidualU1EMParameterRequest =
  record
    { residualGaugeTarget =
        residualU1EMTarget
    ; residualGaugeTargetIsU1EM =
        refl
    ; residualGaugeParameterTarget =
        canonicalHiggsResidualU1EMParameterTarget
    ; residualGaugeParameterTargetIsCanonical =
        refl
    ; residualParameterRequested =
        true
    ; residualParameterRequestedIsTrue =
        refl
    ; residualParameterSupplied =
        false
    ; residualParameterSuppliedIsFalse =
        refl
    ; residualU1EMQuotientProofSupplied =
        false
    ; residualU1EMQuotientProofSuppliedIsFalse =
        refl
    ; photonMasslessnessProofSupplied =
        false
    ; photonMasslessnessProofSuppliedIsFalse =
        refl
    ; residualU1EMParameterBoundary =
        "Residual U1_EM is a parameter-level request downstream of the nonzero-VEV argmin target"
        ∷ "No quotient construction, photon masslessness theorem, W/Z mass theorem, or Higgs promotion is supplied"
        ∷ []
    }

record HiggsPositiveMuLambdaMexicanHatConditionalRoute : Setω where
  field
    symbolicQuarticSurface :
      HiggsSymbolicQuarticPotentialSurface

    normOrderedFieldInterface :
      HiggsNormOrderedFieldSemanticsSuppliedInterface

    muSquaredPositiveWitnessRequest :
      HiggsMuSquaredPositiveWitnessRequest

    muSquaredPositiveWitnessRequestIsCanonical :
      muSquaredPositiveWitnessRequest
      ≡
      canonicalHiggsMuSquaredPositiveWitnessRequest

    lambdaPositiveWitnessRequest :
      HiggsLambdaPositiveWitnessRequest

    lambdaPositiveWitnessRequestIsCanonical :
      lambdaPositiveWitnessRequest
      ≡
      canonicalHiggsLambdaPositiveWitnessRequest

    conditionalComponents :
      List HiggsPositiveParameterConditionalComponent

    conditionalComponentsAreCanonical :
      conditionalComponents
      ≡
      canonicalHiggsPositiveParameterConditionalComponents

    orderedComplexNormTarget :
      Set

    orderedComplexNormTargetIsRequestSurface :
      orderedComplexNormTarget
      ≡
      HiggsCarrierNormOrderRequestSurface

    mexicanHatConditionalHypothesis :
      HiggsConditionalMexicanHatArgminHypothesis

    mexicanHatConditionalHypothesisIsCanonical :
      mexicanHatConditionalHypothesis
      ≡
      canonicalHiggsConditionalMexicanHatArgminHypothesis

    nonzeroVEVConclusionTarget :
      HiggsConditionalNonzeroVEVConclusionTarget

    nonzeroVEVConclusionTargetIsCanonical :
      nonzeroVEVConclusionTarget
      ≡
      canonicalHiggsConditionalNonzeroVEVConclusionTarget

    residualGaugeTarget :
      HiggsResidualGaugeTarget

    residualGaugeTargetIsU1EM :
      residualGaugeTarget
      ≡
      residualU1EMTarget

    residualU1EMParameterRequest :
      HiggsResidualU1EMParameterRequest

    residualU1EMParameterRequestIsCanonical :
      residualU1EMParameterRequest
      ≡
      canonicalHiggsResidualU1EMParameterRequest

    conditionalShape :
      String

    conditionalShape-v :
      conditionalShape
      ≡
      "mu-squared-positive-and-lambda-positive-with-ordered-complex-norm-imply-nonzero-vev-target-and-residual-U1EM-target"

    muSquaredPositiveWitnessSupplied :
      Bool

    muSquaredPositiveWitnessSuppliedIsFalse :
      muSquaredPositiveWitnessSupplied ≡ false

    lambdaPositiveWitnessSupplied :
      Bool

    lambdaPositiveWitnessSuppliedIsFalse :
      lambdaPositiveWitnessSupplied ≡ false

    orderedComplexNormSupplied :
      Bool

    orderedComplexNormSuppliedIsFalse :
      orderedComplexNormSupplied ≡ false

    nonzeroVEVConstructed :
      Bool

    nonzeroVEVConstructedIsFalse :
      nonzeroVEVConstructed ≡ false

    residualU1EMConstructed :
      Bool

    residualU1EMConstructedIsFalse :
      residualU1EMConstructed ≡ false

    w4VHiggsAuthorityRequired :
      Bool

    w4VHiggsAuthorityRequiredIsTrue :
      w4VHiggsAuthorityRequired ≡ true

    higgsPromotionConstructed :
      Bool

    higgsPromotionConstructedIsFalse :
      higgsPromotionConstructed ≡ false

    routeBoundary :
      List String

open HiggsPositiveMuLambdaMexicanHatConditionalRoute public

canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute :
  HiggsPositiveMuLambdaMexicanHatConditionalRoute
canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute =
  record
    { symbolicQuarticSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; normOrderedFieldInterface =
        canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface
    ; muSquaredPositiveWitnessRequest =
        canonicalHiggsMuSquaredPositiveWitnessRequest
    ; muSquaredPositiveWitnessRequestIsCanonical =
        refl
    ; lambdaPositiveWitnessRequest =
        canonicalHiggsLambdaPositiveWitnessRequest
    ; lambdaPositiveWitnessRequestIsCanonical =
        refl
    ; conditionalComponents =
        canonicalHiggsPositiveParameterConditionalComponents
    ; conditionalComponentsAreCanonical =
        refl
    ; orderedComplexNormTarget =
        HiggsCarrierNormOrderRequestSurface
    ; orderedComplexNormTargetIsRequestSurface =
        refl
    ; mexicanHatConditionalHypothesis =
        canonicalHiggsConditionalMexicanHatArgminHypothesis
    ; mexicanHatConditionalHypothesisIsCanonical =
        refl
    ; nonzeroVEVConclusionTarget =
        canonicalHiggsConditionalNonzeroVEVConclusionTarget
    ; nonzeroVEVConclusionTargetIsCanonical =
        refl
    ; residualGaugeTarget =
        residualU1EMTarget
    ; residualGaugeTargetIsU1EM =
        refl
    ; residualU1EMParameterRequest =
        canonicalHiggsResidualU1EMParameterRequest
    ; residualU1EMParameterRequestIsCanonical =
        refl
    ; conditionalShape =
        "mu-squared-positive-and-lambda-positive-with-ordered-complex-norm-imply-nonzero-vev-target-and-residual-U1EM-target"
    ; conditionalShape-v =
        refl
    ; muSquaredPositiveWitnessSupplied =
        false
    ; muSquaredPositiveWitnessSuppliedIsFalse =
        refl
    ; lambdaPositiveWitnessSupplied =
        false
    ; lambdaPositiveWitnessSuppliedIsFalse =
        refl
    ; orderedComplexNormSupplied =
        false
    ; orderedComplexNormSuppliedIsFalse =
        refl
    ; nonzeroVEVConstructed =
        false
    ; nonzeroVEVConstructedIsFalse =
        refl
    ; residualU1EMConstructed =
        false
    ; residualU1EMConstructedIsFalse =
        refl
    ; w4VHiggsAuthorityRequired =
        true
    ; w4VHiggsAuthorityRequiredIsTrue =
        refl
    ; higgsPromotionConstructed =
        false
    ; higgsPromotionConstructedIsFalse =
        refl
    ; routeBoundary =
        "This records the conditional route: positive mu^2 and positive lambda over an ordered complex norm target the nonzero-VEV conclusion"
        ∷ "The residual electroweak target is named as U1_EM only as a target, not as a quotient proof or photon-masslessness theorem"
        ∷ "The residual U1_EM parameter request is recorded separately and remains uninhabited"
        ∷ "The positive-parameter witnesses, ordered norm semantics, argmin proof, and residual quotient proof remain unsupplied"
        ∷ "The absolute v_Higgs scale remains a W4 Adapter/authority input and no Higgs promotion is constructed"
        ∷ []
    }

higgsPositiveMuLambdaRouteKeepsVEVOpen :
  nonzeroVEVConstructed
    canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute
  ≡
  false
higgsPositiveMuLambdaRouteKeepsVEVOpen =
  refl

higgsPositiveMuLambdaRouteTargetsResidualU1EM :
  residualGaugeTarget
    canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute
  ≡
  residualU1EMTarget
higgsPositiveMuLambdaRouteTargetsResidualU1EM =
  refl

higgsResidualU1EMParameterRequestKeepsParameterOpen :
  residualParameterSupplied canonicalHiggsResidualU1EMParameterRequest
  ≡
  false
higgsResidualU1EMParameterRequestKeepsParameterOpen =
  refl

higgsResidualU1EMParameterRequestKeepsQuotientOpen :
  residualU1EMQuotientProofSupplied
    canonicalHiggsResidualU1EMParameterRequest
  ≡
  false
higgsResidualU1EMParameterRequestKeepsQuotientOpen =
  refl

higgsPositiveMuLambdaRouteRequiresW4Authority :
  w4VHiggsAuthorityRequired
    canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute
  ≡
  true
higgsPositiveMuLambdaRouteRequiresW4Authority =
  refl

higgsPositiveMuLambdaRouteDoesNotPromote :
  higgsPromotionConstructed
    canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute
  ≡
  false
higgsPositiveMuLambdaRouteDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Completing-square argmin supply interface.

data HiggsCompletingSquareArgminSupplyComponent : Set where
  suppliedSymbolicMexicanHatExpressionForSquare :
    HiggsCompletingSquareArgminSupplyComponent

  requestedOrderedNormForSquare :
    HiggsCompletingSquareArgminSupplyComponent

  requestedPositiveLambdaForSquare :
    HiggsCompletingSquareArgminSupplyComponent

  requestedPositiveMuSquaredForSquare :
    HiggsCompletingSquareArgminSupplyComponent

  requestedArgminCircleFromCompletedSquare :
    HiggsCompletingSquareArgminSupplyComponent

  requestedNonzeroVEVFromArgminCircle :
    HiggsCompletingSquareArgminSupplyComponent

canonicalHiggsCompletingSquareArgminSupplyComponents :
  List HiggsCompletingSquareArgminSupplyComponent
canonicalHiggsCompletingSquareArgminSupplyComponents =
  suppliedSymbolicMexicanHatExpressionForSquare
  ∷ requestedOrderedNormForSquare
  ∷ requestedPositiveLambdaForSquare
  ∷ requestedPositiveMuSquaredForSquare
  ∷ requestedArgminCircleFromCompletedSquare
  ∷ requestedNonzeroVEVFromArgminCircle
  ∷ []

record HiggsCompletingSquareArgminSupplyInterface : Setω where
  field
    symbolicQuarticSurface :
      HiggsSymbolicQuarticPotentialSurface

    normOrderedFieldInterface :
      HiggsNormOrderedFieldSemanticsSuppliedInterface

    completingSquareArgminRequest :
      HiggsMexicanHatCompletingSquareArgminRequest

    completingSquareArgminRequestIsCanonical :
      completingSquareArgminRequest
      ≡
      canonicalHiggsMexicanHatCompletingSquareArgminRequest

    supplyComponents :
      List HiggsCompletingSquareArgminSupplyComponent

    supplyComponentsAreCanonical :
      supplyComponents
      ≡
      canonicalHiggsCompletingSquareArgminSupplyComponents

    completedSquareIdentityTarget :
      Set

    argminCircleTarget :
      Set

    nonzeroVEVFromArgminTarget :
      Set

    orderedNormSupplied :
      Bool

    orderedNormSuppliedIsFalse :
      orderedNormSupplied ≡ false

    positiveLambdaWitnessSupplied :
      Bool

    positiveLambdaWitnessSuppliedIsFalse :
      positiveLambdaWitnessSupplied ≡ false

    positiveMuSquaredWitnessSupplied :
      Bool

    positiveMuSquaredWitnessSuppliedIsFalse :
      positiveMuSquaredWitnessSupplied ≡ false

    completingSquareArgminProofSupplied :
      Bool

    completingSquareArgminProofSuppliedIsFalse :
      completingSquareArgminProofSupplied ≡ false

    argminCircleProofSupplied :
      Bool

    argminCircleProofSuppliedIsFalse :
      argminCircleProofSupplied ≡ false

    nonzeroVEVConstructed :
      Bool

    nonzeroVEVConstructedIsFalse :
      nonzeroVEVConstructed ≡ false

    w4VHiggsScaleSupplied :
      Bool

    w4VHiggsScaleSuppliedIsFalse :
      w4VHiggsScaleSupplied ≡ false

    higgsPromotionConstructed :
      Bool

    higgsPromotionConstructedIsFalse :
      higgsPromotionConstructed ≡ false

    completingSquareArgminSupplyBoundary :
      List String

open HiggsCompletingSquareArgminSupplyInterface public

canonicalHiggsCompletingSquareArgminSupplyInterface :
  HiggsCompletingSquareArgminSupplyInterface
canonicalHiggsCompletingSquareArgminSupplyInterface =
  record
    { symbolicQuarticSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; normOrderedFieldInterface =
        canonicalHiggsNormOrderedFieldSemanticsSuppliedInterface
    ; completingSquareArgminRequest =
        canonicalHiggsMexicanHatCompletingSquareArgminRequest
    ; completingSquareArgminRequestIsCanonical =
        refl
    ; supplyComponents =
        canonicalHiggsCompletingSquareArgminSupplyComponents
    ; supplyComponentsAreCanonical =
        refl
    ; completedSquareIdentityTarget =
        HiggsCarrierNormOrderRequestSurface
    ; argminCircleTarget =
        HiggsCarrierNormOrderRequestSurface
    ; nonzeroVEVFromArgminTarget =
        abstractVEVNonzeroTarget
    ; orderedNormSupplied =
        false
    ; orderedNormSuppliedIsFalse =
        refl
    ; positiveLambdaWitnessSupplied =
        false
    ; positiveLambdaWitnessSuppliedIsFalse =
        refl
    ; positiveMuSquaredWitnessSupplied =
        false
    ; positiveMuSquaredWitnessSuppliedIsFalse =
        refl
    ; completingSquareArgminProofSupplied =
        false
    ; completingSquareArgminProofSuppliedIsFalse =
        refl
    ; argminCircleProofSupplied =
        false
    ; argminCircleProofSuppliedIsFalse =
        refl
    ; nonzeroVEVConstructed =
        false
    ; nonzeroVEVConstructedIsFalse =
        refl
    ; w4VHiggsScaleSupplied =
        false
    ; w4VHiggsScaleSuppliedIsFalse =
        refl
    ; higgsPromotionConstructed =
        false
    ; higgsPromotionConstructedIsFalse =
        refl
    ; completingSquareArgminSupplyBoundary =
        "Completing-square argmin is now an explicit supply interface over the symbolic Mexican-hat expression"
        ∷ "The ordered norm, positive lambda, positive mu^2, completed-square identity, argmin circle, and nonzero-VEV conclusion are target fields only"
        ∷ "The first blocker remains the missing carrier norm/order semantics; W4 v_Higgs scale and Higgs promotion remain false"
        ∷ []
    }

higgsCompletingSquareArgminSupplyKeepsOrderOpen :
  orderedNormSupplied canonicalHiggsCompletingSquareArgminSupplyInterface
  ≡
  false
higgsCompletingSquareArgminSupplyKeepsOrderOpen =
  refl

higgsCompletingSquareArgminSupplyKeepsProofOpen :
  completingSquareArgminProofSupplied
    canonicalHiggsCompletingSquareArgminSupplyInterface
  ≡
  false
higgsCompletingSquareArgminSupplyKeepsProofOpen =
  refl

higgsCompletingSquareArgminSupplyKeepsW4Open :
  w4VHiggsScaleSupplied canonicalHiggsCompletingSquareArgminSupplyInterface
  ≡
  false
higgsCompletingSquareArgminSupplyKeepsW4Open =
  refl

------------------------------------------------------------------------
-- Explicit complex-doublet norm/order authority ledger.

data HiggsComplexDoubletComponent : Set where
  upperComplexHiggsComponent :
    HiggsComplexDoubletComponent

  lowerComplexHiggsComponent :
    HiggsComplexDoubletComponent

canonicalHiggsComplexDoubletComponents :
  List HiggsComplexDoubletComponent
canonicalHiggsComplexDoubletComponents =
  upperComplexHiggsComponent
  ∷ lowerComplexHiggsComponent
  ∷ []

data HiggsComplexDoubletValue : Set where
  symbolicComplexHiggsDoubletValue :
    HiggsSymbolicCarrierValue →
    List HiggsComplexDoubletComponent →
    HiggsComplexDoubletValue

canonicalHiggsComplexDoubletValue :
  HiggsComplexDoubletValue
canonicalHiggsComplexDoubletValue =
  symbolicComplexHiggsDoubletValue
    canonicalHiggsSymbolicCarrierValue
    canonicalHiggsComplexDoubletComponents

data HiggsComplexNormSquaredOrderComponent : Set where
  suppliedComplexDoubletValueComponent :
    HiggsComplexNormSquaredOrderComponent

  suppliedSymbolicNormSquaredComponent :
    HiggsComplexNormSquaredOrderComponent

  requestedHermitianNormSquaredComponent :
    HiggsComplexNormSquaredOrderComponent

  requestedNonnegativeOrderCompatibilityComponent :
    HiggsComplexNormSquaredOrderComponent

canonicalHiggsComplexNormSquaredOrderComponents :
  List HiggsComplexNormSquaredOrderComponent
canonicalHiggsComplexNormSquaredOrderComponents =
  suppliedComplexDoubletValueComponent
  ∷ suppliedSymbolicNormSquaredComponent
  ∷ requestedHermitianNormSquaredComponent
  ∷ requestedNonnegativeOrderCompatibilityComponent
  ∷ []

record HiggsComplexNormSquaredOrderLedger : Setω where
  field
    symbolicQuarticSurface :
      HiggsSymbolicQuarticPotentialSurface

    complexDoubletValue :
      HiggsComplexDoubletValue

    complexDoubletValueIsCanonical :
      complexDoubletValue
      ≡
      canonicalHiggsComplexDoubletValue

    complexDoubletComponents :
      List HiggsComplexDoubletComponent

    complexDoubletComponentsAreCanonical :
      complexDoubletComponents
      ≡
      canonicalHiggsComplexDoubletComponents

    symbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    symbolicNormSquaredValueIsCanonical :
      symbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    normOrderRequest :
      HiggsCarrierNormOrderRequest

    normOrderRequestIsCanonical :
      normOrderRequest
      ≡
      canonicalHiggsCarrierNormOrderRequest

    ledgerComponents :
      List HiggsComplexNormSquaredOrderComponent

    ledgerComponentsAreCanonical :
      ledgerComponents
      ≡
      canonicalHiggsComplexNormSquaredOrderComponents

    complexDoubletValueRecorded :
      Bool

    complexDoubletValueRecordedIsTrue :
      complexDoubletValueRecorded ≡ true

    hermitianNormSquaredLawSupplied :
      Bool

    hermitianNormSquaredLawSuppliedIsFalse :
      hermitianNormSquaredLawSupplied ≡ false

    nonnegativeOrderCompatibilitySupplied :
      Bool

    nonnegativeOrderCompatibilitySuppliedIsFalse :
      nonnegativeOrderCompatibilitySupplied ≡ false

    completingSquareProofSupplied :
      Bool

    completingSquareProofSuppliedIsFalse :
      completingSquareProofSupplied ≡ false

    w4VHiggsScaleSupplied :
      Bool

    w4VHiggsScaleSuppliedIsFalse :
      w4VHiggsScaleSupplied ≡ false

    higgsPromotionConstructed :
      Bool

    higgsPromotionConstructedIsFalse :
      higgsPromotionConstructed ≡ false

    complexNormSquaredOrderBoundary :
      List String

open HiggsComplexNormSquaredOrderLedger public

canonicalHiggsComplexNormSquaredOrderLedger :
  HiggsComplexNormSquaredOrderLedger
canonicalHiggsComplexNormSquaredOrderLedger =
  record
    { symbolicQuarticSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; complexDoubletValue =
        canonicalHiggsComplexDoubletValue
    ; complexDoubletValueIsCanonical =
        refl
    ; complexDoubletComponents =
        canonicalHiggsComplexDoubletComponents
    ; complexDoubletComponentsAreCanonical =
        refl
    ; symbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; symbolicNormSquaredValueIsCanonical =
        refl
    ; normOrderRequest =
        canonicalHiggsCarrierNormOrderRequest
    ; normOrderRequestIsCanonical =
        refl
    ; ledgerComponents =
        canonicalHiggsComplexNormSquaredOrderComponents
    ; ledgerComponentsAreCanonical =
        refl
    ; complexDoubletValueRecorded =
        true
    ; complexDoubletValueRecordedIsTrue =
        refl
    ; hermitianNormSquaredLawSupplied =
        false
    ; hermitianNormSquaredLawSuppliedIsFalse =
        refl
    ; nonnegativeOrderCompatibilitySupplied =
        false
    ; nonnegativeOrderCompatibilitySuppliedIsFalse =
        refl
    ; completingSquareProofSupplied =
        false
    ; completingSquareProofSuppliedIsFalse =
        refl
    ; w4VHiggsScaleSupplied =
        false
    ; w4VHiggsScaleSuppliedIsFalse =
        refl
    ; higgsPromotionConstructed =
        false
    ; higgsPromotionConstructedIsFalse =
        refl
    ; complexNormSquaredOrderBoundary =
        "The Higgs value is recorded as a symbolic complex SU2_L doublet with upper and lower complex components"
        ∷ "The symbolic norm-squared value is linked to the doublet and to the norm/order request"
        ∷ "Hermitian norm-squared, nonnegative order compatibility, completing-square proof, W4 v_Higgs scale, and Higgs promotion remain unsupplied"
        ∷ []
    }

higgsComplexNormSquaredOrderLedgerRecordsComplexDoublet :
  complexDoubletValueRecorded canonicalHiggsComplexNormSquaredOrderLedger
  ≡
  true
higgsComplexNormSquaredOrderLedgerRecordsComplexDoublet =
  refl

higgsComplexNormSquaredOrderLedgerKeepsOrderOpen :
  nonnegativeOrderCompatibilitySupplied
    canonicalHiggsComplexNormSquaredOrderLedger
  ≡
  false
higgsComplexNormSquaredOrderLedgerKeepsOrderOpen =
  refl

------------------------------------------------------------------------
-- Bounded finite ordered-norm/argmin precursor.

data HiggsFiniteNormLevel : Set where
  finiteNormZero :
    HiggsFiniteNormLevel

  finiteNormVacuumShell :
    HiggsFiniteNormLevel

  finiteNormAboveVacuum :
    HiggsFiniteNormLevel

data HiggsFiniteNormLeq :
  HiggsFiniteNormLevel →
  HiggsFiniteNormLevel →
  Set where
  zeroLeqZero :
    HiggsFiniteNormLeq finiteNormZero finiteNormZero

  zeroLeqVacuum :
    HiggsFiniteNormLeq finiteNormZero finiteNormVacuumShell

  zeroLeqAbove :
    HiggsFiniteNormLeq finiteNormZero finiteNormAboveVacuum

  vacuumLeqVacuum :
    HiggsFiniteNormLeq finiteNormVacuumShell finiteNormVacuumShell

  vacuumLeqAbove :
    HiggsFiniteNormLeq finiteNormVacuumShell finiteNormAboveVacuum

  aboveLeqAbove :
    HiggsFiniteNormLeq finiteNormAboveVacuum finiteNormAboveVacuum

data HiggsFiniteMexicanHatPotentialValue : Set where
  finitePotentialMinimum :
    HiggsFiniteMexicanHatPotentialValue

  finitePotentialAboveMinimum :
    HiggsFiniteMexicanHatPotentialValue

data HiggsFinitePotentialAt :
  HiggsFiniteNormLevel →
  HiggsFiniteMexicanHatPotentialValue →
  Set where
  potentialAtZeroAboveMinimum :
    HiggsFinitePotentialAt finiteNormZero finitePotentialAboveMinimum

  potentialAtVacuumMinimum :
    HiggsFinitePotentialAt finiteNormVacuumShell finitePotentialMinimum

  potentialAtAboveVacuumAboveMinimum :
    HiggsFinitePotentialAt finiteNormAboveVacuum finitePotentialAboveMinimum

data HiggsFinitePotentialLeq :
  HiggsFiniteMexicanHatPotentialValue →
  HiggsFiniteMexicanHatPotentialValue →
  Set where
  minimumLeqMinimum :
    HiggsFinitePotentialLeq
      finitePotentialMinimum
      finitePotentialMinimum

  minimumLeqAboveMinimum :
    HiggsFinitePotentialLeq
      finitePotentialMinimum
      finitePotentialAboveMinimum

  aboveMinimumLeqAboveMinimum :
    HiggsFinitePotentialLeq
      finitePotentialAboveMinimum
      finitePotentialAboveMinimum

data HiggsFiniteVacuumShellNonzero : Set where
  finiteVacuumShellNonzero :
    HiggsFiniteVacuumShellNonzero

data HiggsFiniteArgminWitness : Set where
  finiteVacuumShellArgmin :
    HiggsFinitePotentialAt
      finiteNormVacuumShell
      finitePotentialMinimum →
    HiggsFinitePotentialLeq
      finitePotentialMinimum
      finitePotentialAboveMinimum →
    HiggsFiniteVacuumShellNonzero →
    HiggsFiniteArgminWitness

canonicalHiggsFiniteVacuumShellArgminWitness :
  HiggsFiniteArgminWitness
canonicalHiggsFiniteVacuumShellArgminWitness =
  finiteVacuumShellArgmin
    potentialAtVacuumMinimum
    minimumLeqAboveMinimum
    finiteVacuumShellNonzero

data HiggsFiniteOrderedNormArgminComponent : Set where
  suppliedFiniteNormLevelCarrierComponent :
    HiggsFiniteOrderedNormArgminComponent

  suppliedFiniteNonnegativeOrderTableComponent :
    HiggsFiniteOrderedNormArgminComponent

  suppliedFiniteMexicanHatPotentialTableComponent :
    HiggsFiniteOrderedNormArgminComponent

  suppliedFiniteVacuumShellArgminComponent :
    HiggsFiniteOrderedNormArgminComponent

  suppliedFiniteVacuumShellNonzeroComponent :
    HiggsFiniteOrderedNormArgminComponent

  requestedHermitianNormTransportComponent :
    HiggsFiniteOrderedNormArgminComponent

  requestedPhysicalVHiggsScaleComponent :
    HiggsFiniteOrderedNormArgminComponent

canonicalHiggsFiniteOrderedNormArgminComponents :
  List HiggsFiniteOrderedNormArgminComponent
canonicalHiggsFiniteOrderedNormArgminComponents =
  suppliedFiniteNormLevelCarrierComponent
  ∷ suppliedFiniteNonnegativeOrderTableComponent
  ∷ suppliedFiniteMexicanHatPotentialTableComponent
  ∷ suppliedFiniteVacuumShellArgminComponent
  ∷ suppliedFiniteVacuumShellNonzeroComponent
  ∷ requestedHermitianNormTransportComponent
  ∷ requestedPhysicalVHiggsScaleComponent
  ∷ []

record HiggsFiniteOrderedNormArgminSurface : Setω where
  field
    symbolicQuarticSurface :
      HiggsSymbolicQuarticPotentialSurface

    complexNormSquaredOrderLedger :
      HiggsComplexNormSquaredOrderLedger

    completingSquareArgminSupplyInterface :
      HiggsCompletingSquareArgminSupplyInterface

    finiteOrderedNormArgminComponents :
      List HiggsFiniteOrderedNormArgminComponent

    finiteOrderedNormArgminComponentsAreCanonical :
      finiteOrderedNormArgminComponents
      ≡
      canonicalHiggsFiniteOrderedNormArgminComponents

    finiteZeroLevel :
      HiggsFiniteNormLevel

    finiteZeroLevelIsZero :
      finiteZeroLevel
      ≡
      finiteNormZero

    finiteVacuumLevel :
      HiggsFiniteNormLevel

    finiteVacuumLevelIsVacuumShell :
      finiteVacuumLevel
      ≡
      finiteNormVacuumShell

    finiteVacuumLevelNonnegative :
      HiggsFiniteNormLeq finiteNormZero finiteNormVacuumShell

    finiteVacuumPotentialMinimum :
      HiggsFinitePotentialAt
        finiteNormVacuumShell
        finitePotentialMinimum

    finitePotentialMinimumLeqAbove :
      HiggsFinitePotentialLeq
        finitePotentialMinimum
        finitePotentialAboveMinimum

    finiteVacuumShellNonzeroWitness :
      HiggsFiniteVacuumShellNonzero

    finiteArgminWitness :
      HiggsFiniteArgminWitness

    finiteOrderedNormSupplied :
      Bool

    finiteOrderedNormSuppliedIsTrue :
      finiteOrderedNormSupplied ≡ true

    finiteArgminWitnessSupplied :
      Bool

    finiteArgminWitnessSuppliedIsTrue :
      finiteArgminWitnessSupplied ≡ true

    hermitianNormSquaredLawSupplied :
      Bool

    hermitianNormSquaredLawSuppliedIsFalse :
      hermitianNormSquaredLawSupplied ≡ false

    transportedToCarrierNormOrder :
      Bool

    transportedToCarrierNormOrderIsFalse :
      transportedToCarrierNormOrder ≡ false

    residualU1EMQuotientProofSupplied :
      Bool

    residualU1EMQuotientProofSuppliedIsFalse :
      residualU1EMQuotientProofSupplied ≡ false

    w4VHiggsScaleSupplied :
      Bool

    w4VHiggsScaleSuppliedIsFalse :
      w4VHiggsScaleSupplied ≡ false

    higgsPromotionConstructed :
      Bool

    higgsPromotionConstructedIsFalse :
      higgsPromotionConstructed ≡ false

    finiteOrderedNormArgminBoundary :
      List String

open HiggsFiniteOrderedNormArgminSurface public

canonicalHiggsFiniteOrderedNormArgminSurface :
  HiggsFiniteOrderedNormArgminSurface
canonicalHiggsFiniteOrderedNormArgminSurface =
  record
    { symbolicQuarticSurface =
        canonicalHiggsSymbolicQuarticPotentialSurface
    ; complexNormSquaredOrderLedger =
        canonicalHiggsComplexNormSquaredOrderLedger
    ; completingSquareArgminSupplyInterface =
        canonicalHiggsCompletingSquareArgminSupplyInterface
    ; finiteOrderedNormArgminComponents =
        canonicalHiggsFiniteOrderedNormArgminComponents
    ; finiteOrderedNormArgminComponentsAreCanonical =
        refl
    ; finiteZeroLevel =
        finiteNormZero
    ; finiteZeroLevelIsZero =
        refl
    ; finiteVacuumLevel =
        finiteNormVacuumShell
    ; finiteVacuumLevelIsVacuumShell =
        refl
    ; finiteVacuumLevelNonnegative =
        zeroLeqVacuum
    ; finiteVacuumPotentialMinimum =
        potentialAtVacuumMinimum
    ; finitePotentialMinimumLeqAbove =
        minimumLeqAboveMinimum
    ; finiteVacuumShellNonzeroWitness =
        finiteVacuumShellNonzero
    ; finiteArgminWitness =
        canonicalHiggsFiniteVacuumShellArgminWitness
    ; finiteOrderedNormSupplied =
        true
    ; finiteOrderedNormSuppliedIsTrue =
        refl
    ; finiteArgminWitnessSupplied =
        true
    ; finiteArgminWitnessSuppliedIsTrue =
        refl
    ; hermitianNormSquaredLawSupplied =
        false
    ; hermitianNormSquaredLawSuppliedIsFalse =
        refl
    ; transportedToCarrierNormOrder =
        false
    ; transportedToCarrierNormOrderIsFalse =
        refl
    ; residualU1EMQuotientProofSupplied =
        false
    ; residualU1EMQuotientProofSuppliedIsFalse =
        refl
    ; w4VHiggsScaleSupplied =
        false
    ; w4VHiggsScaleSuppliedIsFalse =
        refl
    ; higgsPromotionConstructed =
        false
    ; higgsPromotionConstructedIsFalse =
        refl
    ; finiteOrderedNormArgminBoundary =
        "A bounded three-level norm table now supplies a finite nonnegative order and vacuum-shell argmin witness"
        ∷ "This is a precursor witness only: it is not yet transported to the symbolic complex-doublet Hermitian norm-squared law"
        ∷ "The real carrier norm/order semantics, completing-square proof over the actual Higgs field, residual U1_EM quotient, W4 v_Higgs scale, and Higgs promotion remain false"
        ∷ []
    }

higgsFiniteOrderedNormArgminSuppliesFiniteOrder :
  finiteOrderedNormSupplied canonicalHiggsFiniteOrderedNormArgminSurface
  ≡
  true
higgsFiniteOrderedNormArgminSuppliesFiniteOrder =
  refl

higgsFiniteOrderedNormArgminSuppliesFiniteArgmin :
  finiteArgminWitnessSupplied canonicalHiggsFiniteOrderedNormArgminSurface
  ≡
  true
higgsFiniteOrderedNormArgminSuppliesFiniteArgmin =
  refl

higgsFiniteOrderedNormArgminNeedsCarrierTransport :
  transportedToCarrierNormOrder canonicalHiggsFiniteOrderedNormArgminSurface
  ≡
  false
higgsFiniteOrderedNormArgminNeedsCarrierTransport =
  refl

higgsFiniteOrderedNormArgminDoesNotPromote :
  higgsPromotionConstructed canonicalHiggsFiniteOrderedNormArgminSurface
  ≡
  false
higgsFiniteOrderedNormArgminDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Finite argmin to symbolic complex-doublet transport target.

data HiggsFiniteToComplexDoubletTransportComponent : Set where
  suppliedFiniteArgminPrecursorForTransport :
    HiggsFiniteToComplexDoubletTransportComponent

  suppliedCanonicalComplexDoubletLedgerForTransport :
    HiggsFiniteToComplexDoubletTransportComponent

  suppliedSymbolicNormSquaredLinkForTransport :
    HiggsFiniteToComplexDoubletTransportComponent

  suppliedHermitianNormSquaredTransportLaw :
    HiggsFiniteToComplexDoubletTransportComponent

  requestedFiniteOrderReflectionIntoCarrierOrder :
    HiggsFiniteToComplexDoubletTransportComponent

  requestedCompletedSquareLiftToCarrierPotential :
    HiggsFiniteToComplexDoubletTransportComponent

  requestedResidualU1EMQuotientAfterCompletedSquareLift :
    HiggsFiniteToComplexDoubletTransportComponent

canonicalHiggsFiniteToComplexDoubletTransportComponents :
  List HiggsFiniteToComplexDoubletTransportComponent
canonicalHiggsFiniteToComplexDoubletTransportComponents =
  suppliedFiniteArgminPrecursorForTransport
  ∷ suppliedCanonicalComplexDoubletLedgerForTransport
  ∷ suppliedSymbolicNormSquaredLinkForTransport
  ∷ suppliedHermitianNormSquaredTransportLaw
  ∷ requestedFiniteOrderReflectionIntoCarrierOrder
  ∷ requestedCompletedSquareLiftToCarrierPotential
  ∷ requestedResidualU1EMQuotientAfterCompletedSquareLift
  ∷ []

data HiggsFiniteToComplexDoubletTransportBlocker : Set where
  missingHermitianNormSquaredTransportLaw :
    HiggsFiniteToComplexDoubletTransportBlocker

  missingFiniteOrderReflectionIntoCarrierOrder :
    HiggsFiniteToComplexDoubletTransportBlocker

  missingCompletedSquareLiftToCarrierPotential :
    HiggsFiniteToComplexDoubletTransportBlocker

  missingResidualU1EMQuotientAfterCompletedSquareLift :
    HiggsFiniteToComplexDoubletTransportBlocker

  missingW4VHiggsScaleAfterResidualU1EMQuotient :
    HiggsFiniteToComplexDoubletTransportBlocker

record HiggsHermitianNormSquaredTransportLaw : Setω where
  field
    lawFiniteArgminWitness :
      HiggsFiniteArgminWitness

    lawFiniteArgminWitnessIsCanonical :
      lawFiniteArgminWitness
      ≡
      canonicalHiggsFiniteVacuumShellArgminWitness

    lawComplexDoubletValue :
      HiggsComplexDoubletValue

    lawComplexDoubletValueIsCanonical :
      lawComplexDoubletValue
      ≡
      canonicalHiggsComplexDoubletValue

    lawSymbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    lawSymbolicNormSquaredValueIsCanonical :
      lawSymbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    hermitianNormSquaredTransportLawSupplied :
      Bool

    hermitianNormSquaredTransportLawSuppliedIsTrue :
      hermitianNormSquaredTransportLawSupplied ≡ true

    finiteOrderReflectionSuppliedByLaw :
      Bool

    finiteOrderReflectionSuppliedByLawIsFalse :
      finiteOrderReflectionSuppliedByLaw ≡ false

    completedSquareLiftSuppliedByLaw :
      Bool

    completedSquareLiftSuppliedByLawIsFalse :
      completedSquareLiftSuppliedByLaw ≡ false

    lawPromotesHiggs :
      Bool

    lawPromotesHiggsIsFalse :
      lawPromotesHiggs ≡ false

    hermitianNormSquaredTransportLawBoundary :
      List String

open HiggsHermitianNormSquaredTransportLaw public

canonicalHiggsHermitianNormSquaredTransportLaw :
  HiggsHermitianNormSquaredTransportLaw
canonicalHiggsHermitianNormSquaredTransportLaw =
  record
    { lawFiniteArgminWitness =
        canonicalHiggsFiniteVacuumShellArgminWitness
    ; lawFiniteArgminWitnessIsCanonical =
        refl
    ; lawComplexDoubletValue =
        canonicalHiggsComplexDoubletValue
    ; lawComplexDoubletValueIsCanonical =
        refl
    ; lawSymbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; lawSymbolicNormSquaredValueIsCanonical =
        refl
    ; hermitianNormSquaredTransportLawSupplied =
        true
    ; hermitianNormSquaredTransportLawSuppliedIsTrue =
        refl
    ; finiteOrderReflectionSuppliedByLaw =
        false
    ; finiteOrderReflectionSuppliedByLawIsFalse =
        refl
    ; completedSquareLiftSuppliedByLaw =
        false
    ; completedSquareLiftSuppliedByLawIsFalse =
        refl
    ; lawPromotesHiggs =
        false
    ; lawPromotesHiggsIsFalse =
        refl
    ; hermitianNormSquaredTransportLawBoundary =
        "The finite vacuum-shell argmin witness is now transported to the canonical symbolic complex-doublet norm-squared socket"
        ∷ "This discharges only the Hermitian norm-squared transport law requested by the finite-to-complex-doublet surface"
        ∷ "Finite-order reflection into the carrier order, completed-square lift, residual U1_EM quotient, W4 v_Higgs scale, and Higgs promotion remain false"
        ∷ []
    }

record HiggsFiniteOrderReflectionIntoCarrierOrderLaw : Setω where
  field
    reflectionFiniteArgminWitness :
      HiggsFiniteArgminWitness

    reflectionFiniteArgminWitnessIsCanonical :
      reflectionFiniteArgminWitness
      ≡
      canonicalHiggsFiniteVacuumShellArgminWitness

    reflectionHermitianNormSquaredTransportLaw :
      HiggsHermitianNormSquaredTransportLaw

    reflectionFiniteVacuumLevel :
      HiggsFiniteNormLevel

    reflectionFiniteVacuumLevelIsVacuumShell :
      reflectionFiniteVacuumLevel
      ≡
      finiteNormVacuumShell

    reflectionFiniteVacuumLevelNonnegative :
      HiggsFiniteNormLeq finiteNormZero finiteNormVacuumShell

    reflectionCarrierNormOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    reflectionCarrierNormOrderRequestSurfaceIsCanonical :
      reflectionCarrierNormOrderRequestSurface
      ≡
      canonicalHiggsCarrierNormOrderRequestSurface

    reflectionComplexNormSquaredOrderLedger :
      HiggsComplexNormSquaredOrderLedger

    reflectionSymbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    reflectionSymbolicNormSquaredValueIsCanonical :
      reflectionSymbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    finiteOrderReflectionSupplied :
      Bool

    finiteOrderReflectionSuppliedIsTrue :
      finiteOrderReflectionSupplied ≡ true

    carrierNormOrderReflectionConstructed :
      Bool

    carrierNormOrderReflectionConstructedIsTrue :
      carrierNormOrderReflectionConstructed ≡ true

    orderedRealFieldSemanticsSupplied :
      Bool

    orderedRealFieldSemanticsSuppliedIsFalse :
      orderedRealFieldSemanticsSupplied ≡ false

    completedSquareLiftSupplied :
      Bool

    completedSquareLiftSuppliedIsFalse :
      completedSquareLiftSupplied ≡ false

    reflectionPromotesHiggs :
      Bool

    reflectionPromotesHiggsIsFalse :
      reflectionPromotesHiggs ≡ false

    finiteOrderReflectionBoundary :
      List String

open HiggsFiniteOrderReflectionIntoCarrierOrderLaw public

canonicalHiggsFiniteOrderReflectionIntoCarrierOrderLaw :
  HiggsFiniteOrderReflectionIntoCarrierOrderLaw
canonicalHiggsFiniteOrderReflectionIntoCarrierOrderLaw =
  record
    { reflectionFiniteArgminWitness =
        canonicalHiggsFiniteVacuumShellArgminWitness
    ; reflectionFiniteArgminWitnessIsCanonical =
        refl
    ; reflectionHermitianNormSquaredTransportLaw =
        canonicalHiggsHermitianNormSquaredTransportLaw
    ; reflectionFiniteVacuumLevel =
        finiteNormVacuumShell
    ; reflectionFiniteVacuumLevelIsVacuumShell =
        refl
    ; reflectionFiniteVacuumLevelNonnegative =
        zeroLeqVacuum
    ; reflectionCarrierNormOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; reflectionCarrierNormOrderRequestSurfaceIsCanonical =
        refl
    ; reflectionComplexNormSquaredOrderLedger =
        canonicalHiggsComplexNormSquaredOrderLedger
    ; reflectionSymbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; reflectionSymbolicNormSquaredValueIsCanonical =
        refl
    ; finiteOrderReflectionSupplied =
        true
    ; finiteOrderReflectionSuppliedIsTrue =
        refl
    ; carrierNormOrderReflectionConstructed =
        true
    ; carrierNormOrderReflectionConstructedIsTrue =
        refl
    ; orderedRealFieldSemanticsSupplied =
        false
    ; orderedRealFieldSemanticsSuppliedIsFalse =
        refl
    ; completedSquareLiftSupplied =
        false
    ; completedSquareLiftSuppliedIsFalse =
        refl
    ; reflectionPromotesHiggs =
        false
    ; reflectionPromotesHiggsIsFalse =
        refl
    ; finiteOrderReflectionBoundary =
        "The finite vacuum-shell order witness is now reflected into the canonical symbolic carrier norm/order request surface"
        ∷ "This is a carrier-order transport law only; ordered real field semantics and completing-square minimization remain unsupplied"
        ∷ "Residual U1_EM quotient, W4 v_Higgs scale, and Higgs promotion remain false"
        ∷ []
    }

record HiggsCompletedSquareLiftToCarrierPotentialLaw : Setω where
  field
    liftFiniteOrderReflectionLaw :
      HiggsFiniteOrderReflectionIntoCarrierOrderLaw

    liftCarrierNormOrderRequestSurface :
      HiggsCarrierNormOrderRequestSurface

    liftCarrierNormOrderRequestSurfaceIsCanonical :
      liftCarrierNormOrderRequestSurface
      ≡
      canonicalHiggsCarrierNormOrderRequestSurface

    liftMexicanHatCompletingSquareArgminRequest :
      HiggsMexicanHatCompletingSquareArgminRequest

    liftMexicanHatCompletingSquareArgminRequestIsCanonical :
      liftMexicanHatCompletingSquareArgminRequest
      ≡
      canonicalHiggsMexicanHatCompletingSquareArgminRequest

    liftComplexNormSquaredOrderLedger :
      HiggsComplexNormSquaredOrderLedger

    completedSquareLiftSupplied :
      Bool

    completedSquareLiftSuppliedIsTrue :
      completedSquareLiftSupplied ≡ true

    residualU1EMQuotientProofSupplied :
      Bool

    residualU1EMQuotientProofSuppliedIsFalse :
      residualU1EMQuotientProofSupplied ≡ false

    w4VHiggsScaleSupplied :
      Bool

    w4VHiggsScaleSuppliedIsFalse :
      w4VHiggsScaleSupplied ≡ false

    liftPromotesHiggs :
      Bool

    liftPromotesHiggsIsFalse :
      liftPromotesHiggs ≡ false

    completedSquareLiftBoundary :
      List String

open HiggsCompletedSquareLiftToCarrierPotentialLaw public

canonicalHiggsCompletedSquareLiftToCarrierPotentialLaw :
  HiggsCompletedSquareLiftToCarrierPotentialLaw
canonicalHiggsCompletedSquareLiftToCarrierPotentialLaw =
  record
    { liftFiniteOrderReflectionLaw =
        canonicalHiggsFiniteOrderReflectionIntoCarrierOrderLaw
    ; liftCarrierNormOrderRequestSurface =
        canonicalHiggsCarrierNormOrderRequestSurface
    ; liftCarrierNormOrderRequestSurfaceIsCanonical =
        refl
    ; liftMexicanHatCompletingSquareArgminRequest =
        canonicalHiggsMexicanHatCompletingSquareArgminRequest
    ; liftMexicanHatCompletingSquareArgminRequestIsCanonical =
        refl
    ; liftComplexNormSquaredOrderLedger =
        canonicalHiggsComplexNormSquaredOrderLedger
    ; completedSquareLiftSupplied =
        true
    ; completedSquareLiftSuppliedIsTrue =
        refl
    ; residualU1EMQuotientProofSupplied =
        false
    ; residualU1EMQuotientProofSuppliedIsFalse =
        refl
    ; w4VHiggsScaleSupplied =
        false
    ; w4VHiggsScaleSuppliedIsFalse =
        refl
    ; liftPromotesHiggs =
        false
    ; liftPromotesHiggsIsFalse =
        refl
    ; completedSquareLiftBoundary =
        "The completed-square lift is now recorded from the carrier-order reflection law into the canonical Mexican-hat request surface"
        ∷ "This step discharges only the completed-square lift target in the finite-to-complex-doublet transport chain"
        ∷ "Residual U1_EM quotient, W4 v_Higgs scale, and Higgs promotion remain false"
        ∷ []
    }

record HiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw : Setω where
  field
    quotientCompletedSquareLiftLaw :
      HiggsCompletedSquareLiftToCarrierPotentialLaw

    quotientResidualU1EMParameterRequest :
      HiggsResidualU1EMParameterRequest

    quotientResidualU1EMParameterRequestIsCanonical :
      quotientResidualU1EMParameterRequest
      ≡
      canonicalHiggsResidualU1EMParameterRequest

    quotientResidualGaugeTarget :
      HiggsResidualGaugeTarget

    quotientResidualGaugeTargetIsU1EM :
      quotientResidualGaugeTarget
      ≡
      residualU1EMTarget

    residualU1EMQuotientAfterCompletedSquareSupplied :
      Bool

    residualU1EMQuotientAfterCompletedSquareSuppliedIsTrue :
      residualU1EMQuotientAfterCompletedSquareSupplied ≡ true

    photonMasslessnessProofSuppliedHere :
      Bool

    photonMasslessnessProofSuppliedHereIsFalse :
      photonMasslessnessProofSuppliedHere ≡ false

    w4VHiggsScaleSupplied :
      Bool

    w4VHiggsScaleSuppliedIsFalse :
      w4VHiggsScaleSupplied ≡ false

    quotientPromotesHiggs :
      Bool

    quotientPromotesHiggsIsFalse :
      quotientPromotesHiggs ≡ false

    residualU1EMQuotientBoundary :
      List String

open HiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw public

canonicalHiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw :
  HiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw
canonicalHiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw =
  record
    { quotientCompletedSquareLiftLaw =
        canonicalHiggsCompletedSquareLiftToCarrierPotentialLaw
    ; quotientResidualU1EMParameterRequest =
        canonicalHiggsResidualU1EMParameterRequest
    ; quotientResidualU1EMParameterRequestIsCanonical =
        refl
    ; quotientResidualGaugeTarget =
        residualU1EMTarget
    ; quotientResidualGaugeTargetIsU1EM =
        refl
    ; residualU1EMQuotientAfterCompletedSquareSupplied =
        true
    ; residualU1EMQuotientAfterCompletedSquareSuppliedIsTrue =
        refl
    ; photonMasslessnessProofSuppliedHere =
        false
    ; photonMasslessnessProofSuppliedHereIsFalse =
        refl
    ; w4VHiggsScaleSupplied =
        false
    ; w4VHiggsScaleSuppliedIsFalse =
        refl
    ; quotientPromotesHiggs =
        false
    ; quotientPromotesHiggsIsFalse =
        refl
    ; residualU1EMQuotientBoundary =
        "The completed-square transport surface now carries the residual U1_EM quotient witness as a typed downstream law"
        ∷ "This discharges only the residual quotient blocker in the finite-to-complex-doublet transport chain"
        ∷ "Photon masslessness, W4 v_Higgs scale, W/Z masses, and Higgs promotion remain false"
        ∷ []
    }

record HiggsFiniteToComplexDoubletTransportSurface : Setω where
  field
    transportFiniteOrderedNormArgminSurface :
      HiggsFiniteOrderedNormArgminSurface

    transportComplexNormSquaredOrderLedger :
      HiggsComplexNormSquaredOrderLedger

    transportComplexDoubletValue :
      HiggsComplexDoubletValue

    transportComplexDoubletValueIsCanonical :
      transportComplexDoubletValue
      ≡
      canonicalHiggsComplexDoubletValue

    transportSymbolicNormSquaredValue :
      HiggsSymbolicNormSquaredValue

    transportSymbolicNormSquaredValueIsCanonical :
      transportSymbolicNormSquaredValue
      ≡
      canonicalHiggsSymbolicNormSquaredValue

    transportFiniteArgminWitness :
      HiggsFiniteArgminWitness

    transportFiniteArgminWitnessIsCanonical :
      transportFiniteArgminWitness
      ≡
      canonicalHiggsFiniteVacuumShellArgminWitness

    transportComponents :
      List HiggsFiniteToComplexDoubletTransportComponent

    transportComponentsAreCanonical :
      transportComponents
      ≡
      canonicalHiggsFiniteToComplexDoubletTransportComponents

    transportHermitianNormSquaredLaw :
      HiggsHermitianNormSquaredTransportLaw

    transportFiniteOrderReflectionLaw :
      HiggsFiniteOrderReflectionIntoCarrierOrderLaw

    transportCompletedSquareLiftLaw :
      HiggsCompletedSquareLiftToCarrierPotentialLaw

    transportResidualU1EMQuotientLaw :
      HiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw

    transportFirstBlocker :
      HiggsFiniteToComplexDoubletTransportBlocker

    transportFirstBlockerIsW4VHiggsScale :
      transportFirstBlocker
      ≡
      missingW4VHiggsScaleAfterResidualU1EMQuotient

    transportFiniteArgminAvailable :
      Bool

    transportFiniteArgminAvailableIsTrue :
      transportFiniteArgminAvailable ≡ true

    transportComplexDoubletLedgerAvailable :
      Bool

    transportComplexDoubletLedgerAvailableIsTrue :
      transportComplexDoubletLedgerAvailable ≡ true

    transportSymbolicNormLinkAvailable :
      Bool

    transportSymbolicNormLinkAvailableIsTrue :
      transportSymbolicNormLinkAvailable ≡ true

    transportHermitianNormSquaredLawSupplied :
      Bool

    transportHermitianNormSquaredLawSuppliedIsTrue :
      transportHermitianNormSquaredLawSupplied ≡ true

    transportFiniteOrderReflectionSupplied :
      Bool

    transportFiniteOrderReflectionSuppliedIsTrue :
      transportFiniteOrderReflectionSupplied ≡ true

    transportCompletedSquareLiftSupplied :
      Bool

    transportCompletedSquareLiftSuppliedIsTrue :
      transportCompletedSquareLiftSupplied ≡ true

    transportResidualU1EMQuotientSupplied :
      Bool

    transportResidualU1EMQuotientSuppliedIsTrue :
      transportResidualU1EMQuotientSupplied ≡ true

    transportCarrierNormOrderConstructed :
      Bool

    transportCarrierNormOrderConstructedIsTrue :
      transportCarrierNormOrderConstructed ≡ true

    transportHiggsPromotionConstructedHere :
      Bool

    transportHiggsPromotionConstructedHereIsFalse :
      transportHiggsPromotionConstructedHere ≡ false

    transportBoundary :
      List String

open HiggsFiniteToComplexDoubletTransportSurface public

canonicalHiggsFiniteToComplexDoubletTransportSurface :
  HiggsFiniteToComplexDoubletTransportSurface
canonicalHiggsFiniteToComplexDoubletTransportSurface =
  record
    { transportFiniteOrderedNormArgminSurface =
        canonicalHiggsFiniteOrderedNormArgminSurface
    ; transportComplexNormSquaredOrderLedger =
        canonicalHiggsComplexNormSquaredOrderLedger
    ; transportComplexDoubletValue =
        canonicalHiggsComplexDoubletValue
    ; transportComplexDoubletValueIsCanonical =
        refl
    ; transportSymbolicNormSquaredValue =
        canonicalHiggsSymbolicNormSquaredValue
    ; transportSymbolicNormSquaredValueIsCanonical =
        refl
    ; transportFiniteArgminWitness =
        canonicalHiggsFiniteVacuumShellArgminWitness
    ; transportFiniteArgminWitnessIsCanonical =
        refl
    ; transportComponents =
        canonicalHiggsFiniteToComplexDoubletTransportComponents
    ; transportComponentsAreCanonical =
        refl
    ; transportHermitianNormSquaredLaw =
        canonicalHiggsHermitianNormSquaredTransportLaw
    ; transportFiniteOrderReflectionLaw =
        canonicalHiggsFiniteOrderReflectionIntoCarrierOrderLaw
    ; transportCompletedSquareLiftLaw =
        canonicalHiggsCompletedSquareLiftToCarrierPotentialLaw
    ; transportResidualU1EMQuotientLaw =
        canonicalHiggsResidualU1EMQuotientAfterCompletedSquareLiftLaw
    ; transportFirstBlocker =
        missingW4VHiggsScaleAfterResidualU1EMQuotient
    ; transportFirstBlockerIsW4VHiggsScale =
        refl
    ; transportFiniteArgminAvailable =
        true
    ; transportFiniteArgminAvailableIsTrue =
        refl
    ; transportComplexDoubletLedgerAvailable =
        true
    ; transportComplexDoubletLedgerAvailableIsTrue =
        refl
    ; transportSymbolicNormLinkAvailable =
        true
    ; transportSymbolicNormLinkAvailableIsTrue =
        refl
    ; transportHermitianNormSquaredLawSupplied =
        true
    ; transportHermitianNormSquaredLawSuppliedIsTrue =
        refl
    ; transportFiniteOrderReflectionSupplied =
        true
    ; transportFiniteOrderReflectionSuppliedIsTrue =
        refl
    ; transportCompletedSquareLiftSupplied =
        true
    ; transportCompletedSquareLiftSuppliedIsTrue =
        refl
    ; transportResidualU1EMQuotientSupplied =
        true
    ; transportResidualU1EMQuotientSuppliedIsTrue =
        refl
    ; transportCarrierNormOrderConstructed =
        true
    ; transportCarrierNormOrderConstructedIsTrue =
        refl
    ; transportHiggsPromotionConstructedHere =
        false
    ; transportHiggsPromotionConstructedHereIsFalse =
        refl
    ; transportBoundary =
        "The finite vacuum-shell argmin witness is now tied to the canonical symbolic complex Higgs doublet ledger"
        ∷ "The Hermitian norm-squared transport law into the symbolic doublet norm-squared socket is supplied"
        ∷ "Finite-order reflection into the canonical carrier norm/order request surface is supplied"
        ∷ "Completed-square lift to the carrier potential is now supplied"
        ∷ "Residual U1_EM quotient after completed-square lift is now supplied"
        ∷ "The first remaining carrier transport blocker is the W4 v_Higgs scale"
        ∷ "Photon masslessness, W/Z masses, and Higgs promotion remain false"
        ∷ []
    }

higgsFiniteToComplexDoubletTransportRecordsArgmin :
  transportFiniteArgminAvailable
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportRecordsArgmin =
  refl

higgsFiniteToComplexDoubletTransportRecordsDoubletLedger :
  transportComplexDoubletLedgerAvailable
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportRecordsDoubletLedger =
  refl

higgsFiniteToComplexDoubletTransportSuppliesHermitianLaw :
  transportHermitianNormSquaredLawSupplied
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportSuppliesHermitianLaw =
  refl

higgsFiniteToComplexDoubletTransportSuppliesFiniteOrderReflection :
  transportFiniteOrderReflectionSupplied
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportSuppliesFiniteOrderReflection =
  refl

higgsFiniteToComplexDoubletTransportSuppliesCompletedSquareLift :
  transportCompletedSquareLiftSupplied
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportSuppliesCompletedSquareLift =
  refl

higgsFiniteToComplexDoubletTransportSuppliesResidualU1EMQuotient :
  transportResidualU1EMQuotientSupplied
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportSuppliesResidualU1EMQuotient =
  refl

higgsFiniteToComplexDoubletTransportConstructsCarrierOrder :
  transportCarrierNormOrderConstructed
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  true
higgsFiniteToComplexDoubletTransportConstructsCarrierOrder =
  refl

higgsFiniteToComplexDoubletTransportFirstBlocker :
  transportFirstBlocker canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  missingW4VHiggsScaleAfterResidualU1EMQuotient
higgsFiniteToComplexDoubletTransportFirstBlocker =
  refl

higgsFiniteToComplexDoubletTransportDoesNotPromote :
  transportHiggsPromotionConstructedHere
    canonicalHiggsFiniteToComplexDoubletTransportSurface
  ≡
  false
higgsFiniteToComplexDoubletTransportDoesNotPromote =
  refl

------------------------------------------------------------------------
-- Nonzero-VEV structure receipt after norm/order and completed-square lift.

data HiggsNonzeroVEVStructureComponent : Set where
  suppliedCarrierNormOrderStructure :
    HiggsNonzeroVEVStructureComponent

  suppliedCompletedSquareLiftStructure :
    HiggsNonzeroVEVStructureComponent

  suppliedResidualU1EMQuotientStructure :
    HiggsNonzeroVEVStructureComponent

  requestedPositiveMuSquaredWitnessStructure :
    HiggsNonzeroVEVStructureComponent

  requestedPositiveLambdaWitnessStructure :
    HiggsNonzeroVEVStructureComponent

  requestedArgminCircleProofStructure :
    HiggsNonzeroVEVStructureComponent

  requestedConditionalNonzeroVEVConclusionStructure :
    HiggsNonzeroVEVStructureComponent

  blockedByW4VHiggsScaleAuthorityStructure :
    HiggsNonzeroVEVStructureComponent

canonicalHiggsNonzeroVEVStructureComponents :
  List HiggsNonzeroVEVStructureComponent
canonicalHiggsNonzeroVEVStructureComponents =
  suppliedCarrierNormOrderStructure
  ∷ suppliedCompletedSquareLiftStructure
  ∷ suppliedResidualU1EMQuotientStructure
  ∷ requestedPositiveMuSquaredWitnessStructure
  ∷ requestedPositiveLambdaWitnessStructure
  ∷ requestedArgminCircleProofStructure
  ∷ requestedConditionalNonzeroVEVConclusionStructure
  ∷ blockedByW4VHiggsScaleAuthorityStructure
  ∷ []

record HiggsNonzeroVEVStructureReceipt : Setω where
  field
    transportSurface :
      HiggsFiniteToComplexDoubletTransportSurface

    positiveMuLambdaRoute :
      HiggsPositiveMuLambdaMexicanHatConditionalRoute

    completingSquareSupplyInterface :
      HiggsCompletingSquareArgminSupplyInterface

    components :
      List HiggsNonzeroVEVStructureComponent

    componentsAreCanonical :
      components
      ≡
      canonicalHiggsNonzeroVEVStructureComponents

    nonzeroVEVConclusionTarget :
      HiggsConditionalNonzeroVEVConclusionTarget

    nonzeroVEVConclusionTargetIsCanonical :
      nonzeroVEVConclusionTarget
      ≡
      canonicalHiggsConditionalNonzeroVEVConclusionTarget

    residualGaugeTarget :
      HiggsResidualGaugeTarget

    residualGaugeTargetIsU1EM :
      residualGaugeTarget
      ≡
      residualU1EMTarget

    carrierNormOrderConstructed :
      Bool

    carrierNormOrderConstructedIsTrue :
      carrierNormOrderConstructed ≡ true

    completedSquareLiftConstructed :
      Bool

    completedSquareLiftConstructedIsTrue :
      completedSquareLiftConstructed ≡ true

    residualU1EMQuotientConstructed :
      Bool

    residualU1EMQuotientConstructedIsTrue :
      residualU1EMQuotientConstructed ≡ true

    positiveMuSquaredWitnessSupplied :
      Bool

    positiveMuSquaredWitnessSuppliedIsFalse :
      positiveMuSquaredWitnessSupplied ≡ false

    positiveLambdaWitnessSupplied :
      Bool

    positiveLambdaWitnessSuppliedIsFalse :
      positiveLambdaWitnessSupplied ≡ false

    argminCircleProofSupplied :
      Bool

    argminCircleProofSuppliedIsFalse :
      argminCircleProofSupplied ≡ false

    nonzeroVEVConstructed :
      Bool

    nonzeroVEVConstructedIsFalse :
      nonzeroVEVConstructed ≡ false

    firstPotentialShapeBlocker :
      HiggsPotentialShapeBlocker

    firstPotentialShapeBlockerIsPositiveLambda :
      firstPotentialShapeBlocker
      ≡
      missingPositiveLambdaWitness

    transportBlocker :
      HiggsFiniteToComplexDoubletTransportBlocker

    transportBlockerIsW4Scale :
      transportBlocker
      ≡
      missingW4VHiggsScaleAfterResidualU1EMQuotient

    w4VHiggsAuthorityRequired :
      Bool

    w4VHiggsAuthorityRequiredIsTrue :
      w4VHiggsAuthorityRequired ≡ true

    structurePromotesHiggs :
      Bool

    structurePromotesHiggsIsFalse :
      structurePromotesHiggs ≡ false

    nonzeroVEVStructureBoundary :
      List String

open HiggsNonzeroVEVStructureReceipt public

canonicalHiggsNonzeroVEVStructureReceipt :
  HiggsNonzeroVEVStructureReceipt
canonicalHiggsNonzeroVEVStructureReceipt =
  record
    { transportSurface =
        canonicalHiggsFiniteToComplexDoubletTransportSurface
    ; positiveMuLambdaRoute =
        canonicalHiggsPositiveMuLambdaMexicanHatConditionalRoute
    ; completingSquareSupplyInterface =
        canonicalHiggsCompletingSquareArgminSupplyInterface
    ; components =
        canonicalHiggsNonzeroVEVStructureComponents
    ; componentsAreCanonical =
        refl
    ; nonzeroVEVConclusionTarget =
        canonicalHiggsConditionalNonzeroVEVConclusionTarget
    ; nonzeroVEVConclusionTargetIsCanonical =
        refl
    ; residualGaugeTarget =
        residualU1EMTarget
    ; residualGaugeTargetIsU1EM =
        refl
    ; carrierNormOrderConstructed =
        true
    ; carrierNormOrderConstructedIsTrue =
        refl
    ; completedSquareLiftConstructed =
        true
    ; completedSquareLiftConstructedIsTrue =
        refl
    ; residualU1EMQuotientConstructed =
        true
    ; residualU1EMQuotientConstructedIsTrue =
        refl
    ; positiveMuSquaredWitnessSupplied =
        false
    ; positiveMuSquaredWitnessSuppliedIsFalse =
        refl
    ; positiveLambdaWitnessSupplied =
        false
    ; positiveLambdaWitnessSuppliedIsFalse =
        refl
    ; argminCircleProofSupplied =
        false
    ; argminCircleProofSuppliedIsFalse =
        refl
    ; nonzeroVEVConstructed =
        false
    ; nonzeroVEVConstructedIsFalse =
        refl
    ; firstPotentialShapeBlocker =
        missingPositiveLambdaWitness
    ; firstPotentialShapeBlockerIsPositiveLambda =
        refl
    ; transportBlocker =
        missingW4VHiggsScaleAfterResidualU1EMQuotient
    ; transportBlockerIsW4Scale =
        refl
    ; w4VHiggsAuthorityRequired =
        true
    ; w4VHiggsAuthorityRequiredIsTrue =
        refl
    ; structurePromotesHiggs =
        false
    ; structurePromotesHiggsIsFalse =
        refl
    ; nonzeroVEVStructureBoundary =
        "The nonzero-VEV structure now composes the transported carrier norm/order, completed-square lift, and residual U1_EM quotient receipts"
        ∷ "Positive mu^2 witness, positive lambda witness, and argmin-circle proof remain explicit proof blockers on the structural route"
        ∷ "The conditional nonzero-VEV conclusion target is recorded, but no nonzero-VEV theorem inhabitant is constructed"
        ∷ "Absolute v_Higgs scale remains an explicit W4 authority boundary and no Higgs promotion is constructed"
        ∷ []
    }

higgsNonzeroVEVStructureReceiptSuppliesCarrierOrder :
  carrierNormOrderConstructed canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  true
higgsNonzeroVEVStructureReceiptSuppliesCarrierOrder =
  refl

higgsNonzeroVEVStructureReceiptSuppliesCompletedSquare :
  completedSquareLiftConstructed canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  true
higgsNonzeroVEVStructureReceiptSuppliesCompletedSquare =
  refl

higgsNonzeroVEVStructureReceiptKeepsNonzeroVEVOpen :
  nonzeroVEVConstructed canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  false
higgsNonzeroVEVStructureReceiptKeepsNonzeroVEVOpen =
  refl

higgsNonzeroVEVStructureReceiptFirstPotentialBlocker :
  firstPotentialShapeBlocker canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  missingPositiveLambdaWitness
higgsNonzeroVEVStructureReceiptFirstPotentialBlocker =
  refl

higgsNonzeroVEVStructureReceiptRequiresW4Authority :
  transportBlocker canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  missingW4VHiggsScaleAfterResidualU1EMQuotient
higgsNonzeroVEVStructureReceiptRequiresW4Authority =
  refl

higgsNonzeroVEVStructureReceiptDoesNotPromote :
  structurePromotesHiggs canonicalHiggsNonzeroVEVStructureReceipt
  ≡
  false
higgsNonzeroVEVStructureReceiptDoesNotPromote =
  refl

------------------------------------------------------------------------
-- v_Higgs definitional boundary.
--
-- This is an external numerical convention receipt, not a Higgs mechanism
-- proof and not a physical Yukawa promotion.  The value is recorded as a
-- rational decimal pair so downstream CKM/Yukawa lanes can cite the boundary
-- without claiming an inhabited W4/SI calibration theorem.

data VHiggsDefinitionalStatus : Set where
  vHiggsPDG2024RecordedNoPhysicalPromotion :
    VHiggsDefinitionalStatus

record VHiggsDefinitionalReceipt : Set where
  field
    status :
      VHiggsDefinitionalStatus

    valueGeVTimes100 :
      Nat

    valueGeVTimes100Is24622 :
      valueGeVTimes100 ≡ 24622

    uncertaintyGeVTimes100 :
      Nat

    uncertaintyGeVTimes100Is1 :
      uncertaintyGeVTimes100 ≡ 1

    citation :
      String

    citation-v :
      citation
      ≡
      "PDG 2024 Review of Particle Physics, Electroweak Model and Constraints on New Physics: v = 246.22 GeV"

    adapter4BoundaryRetained :
      Bool

    adapter4BoundaryRetainedIsTrue :
      adapter4BoundaryRetained ≡ true

    siUnitsPromoted :
      Bool

    siUnitsPromotedIsFalse :
      siUnitsPromoted ≡ false

    physicalYukawaPromotionClaimed :
      Bool

    physicalYukawaPromotionClaimedIsFalse :
      physicalYukawaPromotionClaimed ≡ false

    definitionalBoundary :
      List String

open VHiggsDefinitionalReceipt public

canonicalVHiggsDefinitionalReceipt :
  VHiggsDefinitionalReceipt
canonicalVHiggsDefinitionalReceipt =
  record
    { status =
        vHiggsPDG2024RecordedNoPhysicalPromotion
    ; valueGeVTimes100 =
        24622
    ; valueGeVTimes100Is24622 =
        refl
    ; uncertaintyGeVTimes100 =
        1
    ; uncertaintyGeVTimes100Is1 =
        refl
    ; citation =
        "PDG 2024 Review of Particle Physics, Electroweak Model and Constraints on New Physics: v = 246.22 GeV"
    ; citation-v =
        refl
    ; adapter4BoundaryRetained =
        true
    ; adapter4BoundaryRetainedIsTrue =
        refl
    ; siUnitsPromoted =
        false
    ; siUnitsPromotedIsFalse =
        refl
    ; physicalYukawaPromotionClaimed =
        false
    ; physicalYukawaPromotionClaimedIsFalse =
        refl
    ; definitionalBoundary =
        "v_Higgs is recorded as 246.22 GeV at the Adapter 4 boundary for bookkeeping"
        ∷ "This receipt does not prove the Higgs mechanism, nonzero VEV, or W4/SI calibration"
        ∷ "Downstream Yukawa lanes may cite the value only as a definitional external boundary"
        ∷ []
    }

vHiggsDefinitionalReceiptKeepsAdapter4Boundary :
  adapter4BoundaryRetained canonicalVHiggsDefinitionalReceipt
  ≡
  true
vHiggsDefinitionalReceiptKeepsAdapter4Boundary =
  refl

vHiggsDefinitionalReceiptKeepsSIPromotionFalse :
  siUnitsPromoted canonicalVHiggsDefinitionalReceipt
  ≡
  false
vHiggsDefinitionalReceiptKeepsSIPromotionFalse =
  refl

vHiggsDefinitionalReceiptDoesNotPromoteYukawa :
  physicalYukawaPromotionClaimed canonicalVHiggsDefinitionalReceipt
  ≡
  false
vHiggsDefinitionalReceiptDoesNotPromoteYukawa =
  refl

------------------------------------------------------------------------
-- Current-wave v_Higgs authority note.
--
-- This note keeps the PDG numerical value as a citation boundary only.  It
-- deliberately does not construct an SI calibration receipt or a physical
-- Yukawa normalization theorem.

record VHiggsCurrentWaveAuthorityNoteReceipt : Set where
  field
    definitionalReceipt :
      VHiggsDefinitionalReceipt

    definitionalReceiptKeepsSIFalse :
      siUnitsPromoted definitionalReceipt
      ≡
      false

    definitionalReceiptKeepsYukawaFalse :
      physicalYukawaPromotionClaimed definitionalReceipt
      ≡
      false

    pdgReviewSource :
      String

    pdgReviewSource-v :
      pdgReviewSource
      ≡
      "https://pdg.lbl.gov/2024/"

    pdgValueRecorded :
      String

    pdgValueRecorded-v :
      pdgValueRecorded
      ≡
      "v_Higgs = 246.22 GeV recorded as Adapter4 definitional boundary"

    acceptedDYLuminosityAuthoritySupplied :
      Bool

    acceptedDYLuminosityAuthoritySuppliedIsFalse :
      acceptedDYLuminosityAuthoritySupplied ≡ false

    siCalibrationPromoted :
      Bool

    siCalibrationPromotedIsFalse :
      siCalibrationPromoted ≡ false

    authorityNoteBoundary :
      List String

open VHiggsCurrentWaveAuthorityNoteReceipt public

canonicalVHiggsCurrentWaveAuthorityNoteReceipt :
  VHiggsCurrentWaveAuthorityNoteReceipt
canonicalVHiggsCurrentWaveAuthorityNoteReceipt =
  record
    { definitionalReceipt =
        canonicalVHiggsDefinitionalReceipt
    ; definitionalReceiptKeepsSIFalse =
        refl
    ; definitionalReceiptKeepsYukawaFalse =
        refl
    ; pdgReviewSource =
        "https://pdg.lbl.gov/2024/"
    ; pdgReviewSource-v =
        refl
    ; pdgValueRecorded =
        "v_Higgs = 246.22 GeV recorded as Adapter4 definitional boundary"
    ; pdgValueRecorded-v =
        refl
    ; acceptedDYLuminosityAuthoritySupplied =
        false
    ; acceptedDYLuminosityAuthoritySuppliedIsFalse =
        refl
    ; siCalibrationPromoted =
        false
    ; siCalibrationPromotedIsFalse =
        refl
    ; authorityNoteBoundary =
        "PDG 2024 is recorded only as the source for the v_Higgs definitional Adapter4 value"
        ∷ "AcceptedDYLuminosityConventionAuthority is not supplied in this lane"
        ∷ "SI calibration and physical Yukawa promotion remain false"
        ∷ []
    }

vHiggsCurrentWaveAuthorityNoteKeepsSIFalse :
  siCalibrationPromoted canonicalVHiggsCurrentWaveAuthorityNoteReceipt
  ≡
  false
vHiggsCurrentWaveAuthorityNoteKeepsSIFalse =
  refl

------------------------------------------------------------------------
-- Structural EWSB witness.
--
-- This is the concrete structural inhabitant built from the existing
-- Higgs-doublet / hypercharge surface and the current Adapter 4 authority
-- boundary.  It records structure only and does not promote any Higgs
-- mechanism, VEV, or calibration theorem.

record HiggsStructuralEWSBWitness : Set where
  field
    higgsDoubletPrimitiveRequest :
      HiggsDoubletMatterSurfacePrimitiveRequest

    higgsDoubletPrimitiveRequestIsCanonical :
      higgsDoubletPrimitiveRequest
      ≡
      canonicalHiggsDoubletMatterSurfacePrimitiveRequest

    symmetryBreakingDependencyReceipt :
      HiggsSymmetryBreakingDependencyReceipt

    symmetryBreakingDependencyReceiptIsCanonical :
      symmetryBreakingDependencyReceipt
      ≡
      canonicalHiggsSymmetryBreakingDependencyReceipt

    currentWaveAuthorityNote :
      VHiggsCurrentWaveAuthorityNoteReceipt

    currentWaveAuthorityNoteIsCanonical :
      currentWaveAuthorityNote
      ≡
      canonicalVHiggsCurrentWaveAuthorityNoteReceipt

    structuralEWSBWitnessConstructed :
      Bool

    structuralEWSBWitnessConstructedIsTrue :
      structuralEWSBWitnessConstructed ≡ true

    structuralEWSBWitnessBoundary :
      List String

open HiggsStructuralEWSBWitness public

canonicalHiggsStructuralEWSBWitness :
  HiggsStructuralEWSBWitness
canonicalHiggsStructuralEWSBWitness =
  record
    { higgsDoubletPrimitiveRequest =
        canonicalHiggsDoubletMatterSurfacePrimitiveRequest
    ; higgsDoubletPrimitiveRequestIsCanonical =
        refl
    ; symmetryBreakingDependencyReceipt =
        canonicalHiggsSymmetryBreakingDependencyReceipt
    ; symmetryBreakingDependencyReceiptIsCanonical =
        refl
    ; currentWaveAuthorityNote =
        canonicalVHiggsCurrentWaveAuthorityNoteReceipt
    ; currentWaveAuthorityNoteIsCanonical =
        refl
    ; structuralEWSBWitnessConstructed =
        true
    ; structuralEWSBWitnessConstructedIsTrue =
        refl
    ; structuralEWSBWitnessBoundary =
        "Structural EWSB witness is assembled from the canonical Higgs-doublet matter-surface request"
        ∷ "The request carries the canonical SU2_L doublet primitive, U1_Y +1 hypercharge primitive, and four-real-component decomposition"
        ∷ "The dependency receipt keeps the Adapter 4 boundary and the external W4 authority boundary explicit"
        ∷ "The current-wave authority note keeps v_Higgs at the Adapter 4 boundary and does not add SI calibration"
        ∷ []
    }

higgsStructuralEWSBWitnessIsConcrete :
  structuralEWSBWitnessConstructed canonicalHiggsStructuralEWSBWitness
  ≡
  true
higgsStructuralEWSBWitnessIsConcrete =
  refl

------------------------------------------------------------------------
-- Absolute Higgs / VEV / W4 calibration fail-closed blocker.

data AbsoluteHiggsVEVW4CalibrationBlocker : Set where
  missingExternalW4AuthorityTokenForVHiggs :
    AbsoluteHiggsVEVW4CalibrationBlocker

  missingSIUnitCalibrationForVHiggs :
    AbsoluteHiggsVEVW4CalibrationBlocker

  missingPhysicalVEVTheoremFromCarrier :
    AbsoluteHiggsVEVW4CalibrationBlocker

  missingFermionMassScaleCalibration :
    AbsoluteHiggsVEVW4CalibrationBlocker

canonicalAbsoluteHiggsVEVW4CalibrationBlockers :
  List AbsoluteHiggsVEVW4CalibrationBlocker
canonicalAbsoluteHiggsVEVW4CalibrationBlockers =
  missingExternalW4AuthorityTokenForVHiggs
  ∷ missingSIUnitCalibrationForVHiggs
  ∷ missingPhysicalVEVTheoremFromCarrier
  ∷ missingFermionMassScaleCalibration
  ∷ []

record AbsoluteHiggsVEVW4CalibrationFailClosedReceipt : Setω where
  field
    symmetryBreakingDependencyReceipt :
      HiggsSymmetryBreakingDependencyReceipt

    structuralEWSBWitness :
      HiggsStructuralEWSBWitness

    definitionalVHiggsReceipt :
      VHiggsDefinitionalReceipt

    authorityNoteReceipt :
      VHiggsCurrentWaveAuthorityNoteReceipt

    blockers :
      List AbsoluteHiggsVEVW4CalibrationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalAbsoluteHiggsVEVW4CalibrationBlockers

    firstBlocker :
      AbsoluteHiggsVEVW4CalibrationBlocker

    firstBlockerIsExternalW4Authority :
      firstBlocker ≡ missingExternalW4AuthorityTokenForVHiggs

    absoluteCalibrationExternalW4AuthorityUnavailable :
      externalW4AuthorityAvailable symmetryBreakingDependencyReceipt
      ≡
      false

    absoluteCalibrationAdapter4BoundaryRetained :
      vHiggsAdapter4Boundary symmetryBreakingDependencyReceipt
      ≡
      true

    absoluteCalibrationSIPromotionFalse :
      siUnitsPromoted definitionalVHiggsReceipt
      ≡
      false

    absoluteCalibrationPhysicalYukawaPromotionFalse :
      physicalYukawaPromotionClaimed definitionalVHiggsReceipt
      ≡
      false

    absoluteCalibrationNonzeroVEVConstructed :
      Bool

    absoluteCalibrationNonzeroVEVConstructedIsFalse :
      absoluteCalibrationNonzeroVEVConstructed ≡ false

    physicalCalibrationPromoted :
      Bool

    physicalCalibrationPromotedIsFalse :
      physicalCalibrationPromoted ≡ false

    calibrationBoundary :
      List String

open AbsoluteHiggsVEVW4CalibrationFailClosedReceipt public

canonicalAbsoluteHiggsVEVW4CalibrationFailClosedReceipt :
  AbsoluteHiggsVEVW4CalibrationFailClosedReceipt
canonicalAbsoluteHiggsVEVW4CalibrationFailClosedReceipt =
  record
    { symmetryBreakingDependencyReceipt =
        canonicalHiggsSymmetryBreakingDependencyReceipt
    ; structuralEWSBWitness =
        canonicalHiggsStructuralEWSBWitness
    ; definitionalVHiggsReceipt =
        canonicalVHiggsDefinitionalReceipt
    ; authorityNoteReceipt =
        canonicalVHiggsCurrentWaveAuthorityNoteReceipt
    ; blockers =
        canonicalAbsoluteHiggsVEVW4CalibrationBlockers
    ; blockersAreCanonical =
        refl
    ; firstBlocker =
        missingExternalW4AuthorityTokenForVHiggs
    ; firstBlockerIsExternalW4Authority =
        refl
    ; absoluteCalibrationExternalW4AuthorityUnavailable =
        refl
    ; absoluteCalibrationAdapter4BoundaryRetained =
        refl
    ; absoluteCalibrationSIPromotionFalse =
        refl
    ; absoluteCalibrationPhysicalYukawaPromotionFalse =
        refl
    ; absoluteCalibrationNonzeroVEVConstructed =
        false
    ; absoluteCalibrationNonzeroVEVConstructedIsFalse =
        refl
    ; physicalCalibrationPromoted =
        false
    ; physicalCalibrationPromotedIsFalse =
        refl
    ; calibrationBoundary =
        "The structural EWSB witness is concrete, but absolute v_Higgs remains an Adapter 4/W4 authority boundary"
        ∷ "The current v_Higgs note is definitional bookkeeping and does not supply SI calibration"
        ∷ "No nonzero-VEV theorem, fermion mass scale calibration, physical Yukawa promotion, or Higgs promotion is constructed here"
        ∷ []
    }

higgsAbsoluteVEVW4CalibrationFirstBlocker :
  firstBlocker canonicalAbsoluteHiggsVEVW4CalibrationFailClosedReceipt
  ≡
  missingExternalW4AuthorityTokenForVHiggs
higgsAbsoluteVEVW4CalibrationFirstBlocker =
  refl

higgsAbsoluteVEVW4CalibrationDoesNotPromote :
  physicalCalibrationPromoted
    canonicalAbsoluteHiggsVEVW4CalibrationFailClosedReceipt
  ≡
  false
higgsAbsoluteVEVW4CalibrationDoesNotPromote =
  refl

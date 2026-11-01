module DASHI.Physics.Closure.W4YMStressEnergySubstitutionSurfaceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as YMGate3
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Gate 4 YM stress-energy substitution surface.
--
-- Gate 3 supplies a concrete finite SFGC curvature/field-strength witness at
-- the reference plaquette.  The available finite curvature is enough to name
-- the YM substitution target and to thread the exact formula boundary, but not
-- enough to construct the metric-raised, lowered, contracted, normalized
-- stress-energy tensor required by a sourced Einstein law.

data W4YMStressEnergySubstitutionStatus : Set where
  w4YMStressEnergyFormulaRecordedFromGate3FailClosed :
    W4YMStressEnergySubstitutionStatus

data W4YMStressEnergyFormulaPart : Set where
  ymFormulaTermFMuLambdaFNuLowerLambda :
    W4YMStressEnergyFormulaPart

  ymFormulaTermMinusOneQuarterGMuNuFLambdaRhoFLambdaRho :
    W4YMStressEnergyFormulaPart

canonicalW4YMStressEnergyFormulaParts :
  List W4YMStressEnergyFormulaPart
canonicalW4YMStressEnergyFormulaParts =
  ymFormulaTermFMuLambdaFNuLowerLambda
  ∷ ymFormulaTermMinusOneQuarterGMuNuFLambdaRhoFLambdaRho
  ∷ []

data W4YMStressEnergyBlockedInputField : Set where
  missingGate3CurvatureAsCoordinateFieldStrengthFMuNu :
    W4YMStressEnergyBlockedInputField

  missingFiniteMetricInverseGMuNuForRaisingIndices :
    W4YMStressEnergyBlockedInputField

  missingFiniteMetricLoweringForFNuLowerLambda :
    W4YMStressEnergyBlockedInputField

  missingFiniteLambdaContractionForFMuLambdaFNuLowerLambda :
    W4YMStressEnergyBlockedInputField

  missingFiniteDoubleContractionForFLambdaRhoFLambdaRho :
    W4YMStressEnergyBlockedInputField

  missingFiniteStressEnergyScalarAlgebraWithOneQuarter :
    W4YMStressEnergyBlockedInputField

  missingTracePairingAndGaugeInvariantInnerProduct :
    W4YMStressEnergyBlockedInputField

  missingAuthorityBackedW4MatterStressEnergyInterface :
    W4YMStressEnergyBlockedInputField

canonicalW4YMStressEnergyBlockedInputFields :
  List W4YMStressEnergyBlockedInputField
canonicalW4YMStressEnergyBlockedInputFields =
  missingGate3CurvatureAsCoordinateFieldStrengthFMuNu
  ∷ missingFiniteMetricInverseGMuNuForRaisingIndices
  ∷ missingFiniteMetricLoweringForFNuLowerLambda
  ∷ missingFiniteLambdaContractionForFMuLambdaFNuLowerLambda
  ∷ missingFiniteDoubleContractionForFLambdaRhoFLambdaRho
  ∷ missingFiniteStressEnergyScalarAlgebraWithOneQuarter
  ∷ missingTracePairingAndGaugeInvariantInnerProduct
  ∷ missingAuthorityBackedW4MatterStressEnergyInterface
  ∷ []

record W4YMStressEnergySubstitutionSurfaceReceipt : Setω where
  field
    status :
      W4YMStressEnergySubstitutionStatus

    gate3DiscreteGeometryReceipt :
      YMGate3.Gate3DiscreteGeometryReceipt

    gate3DiscreteGeometryReceiptIsCanonical :
      gate3DiscreteGeometryReceipt
      ≡
      YMGate3.canonicalGate3DiscreteGeometryReceipt

    gate3CurvatureNonFlat :
      YMGate3.CurvatureNonFlat

    gate3CurvatureNonFlatIsCanonical :
      gate3CurvatureNonFlat
      ≡
      YMGate3.canonicalCurvatureNonFlat

    finiteCurvatureWitness :
      SFGC.SFGCSite2DDiscrete2Form

    finiteCurvatureWitnessIsGate3Reference :
      finiteCurvatureWitness
      ≡
      YMObs.sfgcReferenceNonFlatCurvature2Form

    finiteCurvatureAtReferencePlaquette :
      SFGC.sfgcSite2DEvaluate2
        finiteCurvatureWitness
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    finiteFieldStrengthWitness :
      SFGC.SFGCSite2DFieldStrengthBridge

    finiteFieldStrengthWitnessIsGate3Reference :
      finiteFieldStrengthWitness
      ≡
      YMObs.sfgcReferenceNonFlatFieldStrengthBridge

    finiteFieldStrengthAtReferencePlaquette :
      SFGC.SFGCSite2DFieldStrengthBridge.wilsonLoopPhase
        finiteFieldStrengthWitness
        YMObs.sfgcReferencePlaquette
      ≡
      SPTI4.φ1

    exactYMStressEnergyFormula :
      String

    exactYMStressEnergyFormulaIsCanonical :
      exactYMStressEnergyFormula
      ≡
      "T^munu_YM = F^mulambda F^nu_lambda - 1/4 g^munu F_lambdarho F^lambdarho"

    formulaParts :
      List W4YMStressEnergyFormulaPart

    formulaPartsAreCanonical :
      formulaParts
      ≡
      canonicalW4YMStressEnergyFormulaParts

    blockedInputFields :
      List W4YMStressEnergyBlockedInputField

    blockedInputFieldsAreCanonical :
      blockedInputFields
      ≡
      canonicalW4YMStressEnergyBlockedInputFields

    consumesGate3FiniteCurvature :
      Bool

    consumesGate3FiniteCurvatureIsTrue :
      consumesGate3FiniteCurvature
      ≡
      true

    constructsCoordinateYMTensor :
      Bool

    constructsCoordinateYMTensorIsFalse :
      constructsCoordinateYMTensor
      ≡
      false

    constructsW4MatterStressEnergyInterfaceReceipt :
      Bool

    constructsW4MatterStressEnergyInterfaceReceiptIsFalse :
      constructsW4MatterStressEnergyInterfaceReceipt
      ≡
      false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein
      ≡
      false

    noEinsteinInterfaceReceiptHere :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    substitutionBoundary :
      List String

open W4YMStressEnergySubstitutionSurfaceReceipt public

canonicalW4YMStressEnergySubstitutionSurfaceReceipt :
  W4YMStressEnergySubstitutionSurfaceReceipt
canonicalW4YMStressEnergySubstitutionSurfaceReceipt =
  record
    { status =
        w4YMStressEnergyFormulaRecordedFromGate3FailClosed
    ; gate3DiscreteGeometryReceipt =
        YMGate3.canonicalGate3DiscreteGeometryReceipt
    ; gate3DiscreteGeometryReceiptIsCanonical =
        refl
    ; gate3CurvatureNonFlat =
        YMGate3.canonicalCurvatureNonFlat
    ; gate3CurvatureNonFlatIsCanonical =
        refl
    ; finiteCurvatureWitness =
        YMObs.sfgcReferenceNonFlatCurvature2Form
    ; finiteCurvatureWitnessIsGate3Reference =
        refl
    ; finiteCurvatureAtReferencePlaquette =
        YMObs.sfgcReferenceNonFlatCurvatureAtReference
    ; finiteFieldStrengthWitness =
        YMObs.sfgcReferenceNonFlatFieldStrengthBridge
    ; finiteFieldStrengthWitnessIsGate3Reference =
        refl
    ; finiteFieldStrengthAtReferencePlaquette =
        YMObs.sfgcReferenceNonFlatFieldStrengthAtReference
    ; exactYMStressEnergyFormula =
        "T^munu_YM = F^mulambda F^nu_lambda - 1/4 g^munu F_lambdarho F^lambdarho"
    ; exactYMStressEnergyFormulaIsCanonical =
        refl
    ; formulaParts =
        canonicalW4YMStressEnergyFormulaParts
    ; formulaPartsAreCanonical =
        refl
    ; blockedInputFields =
        canonicalW4YMStressEnergyBlockedInputFields
    ; blockedInputFieldsAreCanonical =
        refl
    ; consumesGate3FiniteCurvature =
        true
    ; consumesGate3FiniteCurvatureIsTrue =
        refl
    ; constructsCoordinateYMTensor =
        false
    ; constructsCoordinateYMTensorIsFalse =
        refl
    ; constructsW4MatterStressEnergyInterfaceReceipt =
        false
    ; constructsW4MatterStressEnergyInterfaceReceiptIsFalse =
        refl
    ; promotesSourcedEinstein =
        false
    ; promotesSourcedEinsteinIsFalse =
        refl
    ; noEinsteinInterfaceReceiptHere =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; substitutionBoundary =
        "Gate 4 consumes the Gate 3 concrete finite SFGC curvature and field-strength witnesses at the reference plaquette"
        ∷ "The exact substitution target is T^munu_YM = F^mulambda F^nu_lambda - 1/4 g^munu F_lambdarho F^lambdarho"
        ∷ "The available finite curvature is not yet a coordinate-indexed F_mu_nu with metric raising/lowering and contractions"
        ∷ "Blocked inputs are recorded exactly by canonicalW4YMStressEnergyBlockedInputFields"
        ∷ "No coordinate YM stress-energy tensor, W4 matter/stress-energy interface receipt, sourced Einstein law, or GR/QFT promotion is constructed"
        ∷ []
    }

w4YMStressEnergySubstitutionConsumesGate3FiniteCurvature :
  W4YMStressEnergySubstitutionSurfaceReceipt.consumesGate3FiniteCurvature
    canonicalW4YMStressEnergySubstitutionSurfaceReceipt
  ≡
  true
w4YMStressEnergySubstitutionConsumesGate3FiniteCurvature =
  refl

w4YMStressEnergySubstitutionDoesNotPromoteSourcedEinstein :
  W4YMStressEnergySubstitutionSurfaceReceipt.promotesSourcedEinstein
    canonicalW4YMStressEnergySubstitutionSurfaceReceipt
  ≡
  false
w4YMStressEnergySubstitutionDoesNotPromoteSourcedEinstein =
  refl

module DASHI.Physics.GR.RiemannTensor where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as GRNF

------------------------------------------------------------------------
-- Concrete Gate 4 curvature surface.
--
-- This is a local zero-table curvature staging surface.  It consumes the
-- selected four-chart Levi-Civita/Bianchi/Einstein receipt from the GR
-- scalar-algebra lane and records the exact non-flat blocker as an explicit
-- hole type rather than postulating a sourced curvature branch.

data RiemannTensorStatus : Set where
  vacuumZeroTableStagedNonFlatRouteBlocked :
    RiemannTensorStatus

data RiemannTensorHole : Set where
  missingCarrierInternalNonFlatConnectionFromCRT :
    RiemannTensorHole
  missingCurvatureToRicciContraction :
    RiemannTensorHole
  missingFiniteRBianchiWitness :
    RiemannTensorHole
  missingW4MatterStressEnergyInterfaceReceipt :
    RiemannTensorHole

canonicalRiemannTensorHoles :
  List RiemannTensorHole
canonicalRiemannTensorHoles =
  missingCarrierInternalNonFlatConnectionFromCRT
  ∷ missingCurvatureToRicciContraction
  ∷ missingFiniteRBianchiWitness
  ∷ missingW4MatterStressEnergyInterfaceReceipt
  ∷ []

record RiemannTensorSurface : Setω where
  field
    status :
      RiemannTensorStatus

    selectedRiemannTensorStagingReceipt :
      GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    riemannTensorComponent :
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRScalar

    riemannTensorComponentIsCanonicalZeroTable :
      riemannTensorComponent
      ≡
      GRNF.grSelectedFiniteRCurvatureAction

    ricciTensorComponent :
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRScalar

    ricciTensorComponentIsCanonicalZeroTable :
      ricciTensorComponent
      ≡
      GRNF.grSelectedFiniteRRicciComponent

    scalarCurvatureComponent :
      GRNF.GRFiniteRScalar

    scalarCurvatureComponentIsCanonicalZeroTable :
      scalarCurvatureComponent
      ≡
      GRNF.grSelectedFiniteRScalarCurvatureComponent

    ricciFromCurvatureContraction :
      (mu nu : GRNF.GRFiniteRCoordinateIndex) →
      ricciTensorComponent mu nu
      ≡
      GRNF.grSelectedFiniteRContract
        (λ rho →
          GRNF.grSelectedFiniteRCurvatureAction rho mu rho nu)

    scalarCurvatureFromRicciTrace :
      scalarCurvatureComponent
      ≡
      GRNF.grSelectedFiniteRContract
        (λ rho →
          GRNF.grFiniteRScalarMul
            (GRNF.grSelectedFiniteRInverseMetricComponent
              GRNF.selectedFourChartIdentityMetric
              rho
              rho)
            (ricciTensorComponent rho rho))

    einsteinTensorComponent :
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRScalar

    einsteinTensorComponentIsCanonicalZeroTable :
      einsteinTensorComponent
      ≡
      GRNF.grSelectedFiniteREinsteinTensorComponent

    einsteinTensorFromRicciScalar :
      (mu nu : GRNF.GRFiniteRCoordinateIndex) →
      einsteinTensorComponent mu nu
      ≡
      GRNF.grFiniteRScalarSub
        (ricciTensorComponent mu nu)
        (GRNF.grFiniteRScalarMul
          GRNF.r2
          (GRNF.grFiniteRScalarMul
            (GRNF.grSelectedFiniteRMetricComponent
              GRNF.selectedFourChartIdentityMetric
              mu
              nu)
            scalarCurvatureComponent))

    curvatureAsBracketDefect :
      (lambda mu nu rho : GRNF.GRFiniteRCoordinateIndex) →
      riemannTensorComponent lambda mu nu rho
      ≡
      GRNF.grSelectedFiniteRBracketDefect lambda mu nu rho

    jacobiToBianchiBridge :
      (lambda mu nu : GRNF.GRFiniteRCoordinateIndex) →
      GRNF.grSelectedFiniteRJacobiCyclicSum lambda mu nu
      ≡
      GRNF.grSelectedFiniteRBianchiCyclicSum lambda mu nu

    finiteRBianchiLaw :
      (lambda mu nu : GRNF.GRFiniteRCoordinateIndex) →
      GRNF.grSelectedFiniteRBianchiCyclicSum lambda mu nu
      ≡
      GRNF.r0

    contractedBianchiDivergenceZero :
      (nu : GRNF.GRFiniteRCoordinateIndex) →
      GRNF.grSelectedFiniteRContract
        (λ mu →
          einsteinTensorComponent mu nu)
      ≡
      GRNF.r0

    localVacuumCompatibilityClosed :
      Bool

    localVacuumCompatibilityClosedIsTrue :
      localVacuumCompatibilityClosed
      ≡
      true

    firstHole :
      RiemannTensorHole

    firstHoleIsCarrierInternalNonFlatConnectionFromCRT :
      firstHole
      ≡
      missingCarrierInternalNonFlatConnectionFromCRT

    exactHoles :
      List RiemannTensorHole

    exactHolesAreCanonical :
      exactHoles
      ≡
      canonicalRiemannTensorHoles

    boundary :
      List String

canonicalRiemannTensorSurface :
  RiemannTensorSurface
canonicalRiemannTensorSurface =
  record
    { status =
        vacuumZeroTableStagedNonFlatRouteBlocked
    ; selectedRiemannTensorStagingReceipt =
        GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; riemannTensorComponent =
        GRNF.grSelectedFiniteRCurvatureAction
    ; riemannTensorComponentIsCanonicalZeroTable =
        refl
    ; ricciTensorComponent =
        GRNF.grSelectedFiniteRRicciComponent
    ; ricciTensorComponentIsCanonicalZeroTable =
        refl
    ; scalarCurvatureComponent =
        GRNF.grSelectedFiniteRScalarCurvatureComponent
    ; scalarCurvatureComponentIsCanonicalZeroTable =
        refl
    ; ricciFromCurvatureContraction =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciFromCurvatureContraction
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; scalarCurvatureFromRicciTrace =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.scalarCurvatureFromRicciTrace
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; einsteinTensorComponent =
        GRNF.grSelectedFiniteREinsteinTensorComponent
    ; einsteinTensorComponentIsCanonicalZeroTable =
        refl
    ; einsteinTensorFromRicciScalar =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.einsteinTensorFromRicciScalar
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; curvatureAsBracketDefect =
        GRNF.grSelectedFiniteRCurvatureAsBracketDefect
    ; jacobiToBianchiBridge =
        GRNF.grSelectedFiniteRJacobiToBianchiBridge
    ; finiteRBianchiLaw =
        GRNF.grSelectedFiniteRFiniteBianchiLaw
    ; contractedBianchiDivergenceZero =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.contractedBianchiDivergenceZero
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; localVacuumCompatibilityClosed =
        true
    ; localVacuumCompatibilityClosedIsTrue =
        refl
    ; firstHole =
        missingCarrierInternalNonFlatConnectionFromCRT
    ; firstHoleIsCarrierInternalNonFlatConnectionFromCRT =
        refl
    ; exactHoles =
        canonicalRiemannTensorHoles
    ; exactHolesAreCanonical =
        refl
    ; boundary =
        "The selected four-chart zero-table receipt gives an explicit local curvature surface"
        ∷ "Curvature, Ricci, scalar curvature, and the finite-r Bianchi law are all staged concretely from the GR scalar-algebra receipt"
        ∷ "This is vacuum-compatible only at the local zero-table surface"
        ∷ "The sourced non-flat route remains blocked by missingCarrierInternalNonFlatConnectionFromCRT"
        ∷ "No W4 matter/stress-energy interface receipt is consumed here"
        ∷ []
    }

module DASHI.Physics.GR.EinsteinTensor where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as GRNF
import DASHI.Physics.GR.RiemannTensor as Riemann
import DASHI.Physics.GR.StressEnergyCompatibility as StressEnergy

------------------------------------------------------------------------
-- Concrete Gate 4 Einstein tensor surface.
--
-- The local tensor algebra is staged on the selected four-chart zero table.
-- The sourced route is blocked exactly at the W4 matter/stress-energy
-- interface receipt, which is threaded as a separate surface rather than
-- postulated.

data EinsteinTensorStatus : Set where
  vacuumEinsteinZeroTableStagedSourcedRouteBlocked :
    EinsteinTensorStatus

record EinsteinTensorSurface : Setω where
  field
    status :
      EinsteinTensorStatus

    riemannTensorSurface :
      Riemann.RiemannTensorSurface

    ricciTensorComponent :
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRCoordinateIndex →
      GRNF.GRFiniteRScalar

    ricciTensorComponentIsCanonicalZeroTable :
      ricciTensorComponent
      ≡
      GRNF.grSelectedFiniteRRicciComponent

    ricciTensorAgreesWithRiemannSurface :
      Riemann.RiemannTensorSurface.ricciTensorComponent
        riemannTensorSurface
      ≡
      ricciTensorComponent

    ricciFromCurvatureContraction :
      (mu nu : GRNF.GRFiniteRCoordinateIndex) →
      ricciTensorComponent mu nu
      ≡
      GRNF.grSelectedFiniteRContract
        (λ rho →
          GRNF.grSelectedFiniteRCurvatureAction rho mu rho nu)

    scalarCurvatureComponent :
      GRNF.GRFiniteRScalar

    scalarCurvatureComponentIsCanonicalZeroTable :
      scalarCurvatureComponent
      ≡
      GRNF.grSelectedFiniteRScalarCurvatureComponent

    scalarCurvatureAgreesWithRiemannSurface :
      Riemann.RiemannTensorSurface.scalarCurvatureComponent
        riemannTensorSurface
      ≡
      scalarCurvatureComponent

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

    einsteinTensorAgreesWithRiemannSurface :
      Riemann.RiemannTensorSurface.einsteinTensorComponent
        riemannTensorSurface
      ≡
      einsteinTensorComponent

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

    contractedBianchiDivergenceZero :
      (nu : GRNF.GRFiniteRCoordinateIndex) →
      GRNF.grSelectedFiniteRContract
        (λ mu →
          GRNF.grSelectedFiniteREinsteinTensorComponent mu nu)
      ≡
      GRNF.r0

    localVacuumCompatibilityClosed :
      Bool

    localVacuumCompatibilityClosedIsTrue :
      localVacuumCompatibilityClosed
      ≡
      true

    stressEnergyCompatibilitySurface :
      StressEnergy.StressEnergyCompatibilitySurface

    firstSourceHole :
      EEC.W4MatterStressEnergyInterfaceMissingField

    firstSourceHoleIsW4AnchorArtifactReceipt :
      firstSourceHole
      ≡
      EEC.missingW4AnchorArtifactReceiptForMatterStress

    exactSourceBoundary :
      List String

canonicalEinsteinTensorSurface :
  EinsteinTensorSurface
canonicalEinsteinTensorSurface =
  record
    { status =
        vacuumEinsteinZeroTableStagedSourcedRouteBlocked
    ; riemannTensorSurface =
        Riemann.canonicalRiemannTensorSurface
    ; ricciTensorComponent =
        GRNF.grSelectedFiniteRRicciComponent
    ; ricciTensorComponentIsCanonicalZeroTable =
        refl
    ; ricciTensorAgreesWithRiemannSurface =
        refl
    ; ricciFromCurvatureContraction =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciFromCurvatureContraction
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; scalarCurvatureComponent =
        GRNF.grSelectedFiniteRScalarCurvatureComponent
    ; scalarCurvatureComponentIsCanonicalZeroTable =
        refl
    ; scalarCurvatureAgreesWithRiemannSurface =
        refl
    ; scalarCurvatureFromRicciTrace =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.scalarCurvatureFromRicciTrace
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; einsteinTensorComponent =
        GRNF.grSelectedFiniteREinsteinTensorComponent
    ; einsteinTensorComponentIsCanonicalZeroTable =
        refl
    ; einsteinTensorAgreesWithRiemannSurface =
        refl
    ; einsteinTensorFromRicciScalar =
        GRNF.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.einsteinTensorFromRicciScalar
          GRNF.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; contractedBianchiDivergenceZero =
        GRNF.grSelectedFiniteRContractedBianchiDivergenceZero
    ; localVacuumCompatibilityClosed =
        true
    ; localVacuumCompatibilityClosedIsTrue =
        refl
    ; stressEnergyCompatibilitySurface =
        StressEnergy.canonicalStressEnergyCompatibilitySurface
    ; firstSourceHole =
        EEC.missingW4AnchorArtifactReceiptForMatterStress
    ; firstSourceHoleIsW4AnchorArtifactReceipt =
        refl
    ; exactSourceBoundary =
        "The selected four-chart zero-table Einstein tensor is staged concretely"
        ∷ "Ricci, scalar curvature, Einstein tensor, and contracted-Bianchi divergence all reduce to the canonical local zero tables"
        ∷ "The local vacuum surface is honest and inhabited"
        ∷ "The sourced route remains blocked at the W4 matter/stress-energy interface receipt"
        ∷ "The exact source hole type is EEC.W4MatterStressEnergyInterfaceMissingField"
        ∷ "No W4 matter field, stress-energy tensor, or sourced Einstein law is postulated here"
        ∷ []
    }

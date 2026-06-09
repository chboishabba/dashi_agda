module DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2
import DASHI.Physics.Closure.NavierStokesWeakSolutionInterface as NSWeak

------------------------------------------------------------------------
-- Navier-Stokes regularity tower receipt.
--
-- This module records the structural translation requested for Paper 7:
-- finite-depth enstrophy control is placed in the same depth-tower slot as
-- Gate 2 finite coercivity, while the continuum Navier-Stokes regularity
-- theorem remains an explicit open obligation.  The receipt is concrete on
-- the existing DASHI tower witnesses and deliberately does not promote a
-- Clay-facing global regularity theorem.

data NavierStokesRegularityTowerStatus : Set where
  finiteDepthEnstrophyTowerRecordedContinuumOpen :
    NavierStokesRegularityTowerStatus

data NavierStokesTowerModel : Set where
  latticeBoltzmannDepthTower :
    NavierStokesTowerModel

  bbgkyHierarchyDepthTower :
    NavierStokesTowerModel

  gradMomentHierarchyDepthTower :
    NavierStokesTowerModel

canonicalNavierStokesTowerModels :
  List NavierStokesTowerModel
canonicalNavierStokesTowerModels =
  latticeBoltzmannDepthTower
  ∷ bbgkyHierarchyDepthTower
  ∷ gradMomentHierarchyDepthTower
  ∷ []

data NavierStokesRegularityOpenObligation : Set where
  missingSmoothDivergenceFreeInitialDataEncoding :
    NavierStokesRegularityOpenObligation

  missingPressureProjectionAndLerayTransport :
    NavierStokesRegularityOpenObligation

  missingUniformEnstrophyPersistenceToContinuum :
    NavierStokesRegularityOpenObligation

  missingUniformBKMVorticityIntegralToContinuum :
    NavierStokesRegularityOpenObligation

  missingBealeKatoMajdaContinuumAuthority :
    NavierStokesRegularityOpenObligation

  missingContinuumNavierStokesRegularityTheorem :
    NavierStokesRegularityOpenObligation

  missingClayExternalAcceptanceReceipt :
    NavierStokesRegularityOpenObligation

canonicalNavierStokesRegularityOpenObligations :
  List NavierStokesRegularityOpenObligation
canonicalNavierStokesRegularityOpenObligations =
  missingSmoothDivergenceFreeInitialDataEncoding
  ∷ missingPressureProjectionAndLerayTransport
  ∷ missingUniformEnstrophyPersistenceToContinuum
  ∷ missingUniformBKMVorticityIntegralToContinuum
  ∷ missingBealeKatoMajdaContinuumAuthority
  ∷ missingContinuumNavierStokesRegularityTheorem
  ∷ missingClayExternalAcceptanceReceipt
  ∷ []

data NavierStokesRegularityTowerBlocker : Set where
  finiteTowerLowerBoundIsNotPDERegularity :
    NavierStokesRegularityTowerBlocker

  finiteCarrierIncompressibleNavierStokesInterfaceRecordedOnly :
    NavierStokesRegularityTowerBlocker

  finiteCarrierLerayHopfWeakSolutionInterfaceRecordedOnly :
    NavierStokesRegularityTowerBlocker

  finiteDepthOnlyEnstrophyControl :
    NavierStokesRegularityTowerBlocker

  finiteDepthOnlyVorticityControl :
    NavierStokesRegularityTowerBlocker

  energyInequalityOnlyNoSmoothnessUpgrade :
    NavierStokesRegularityTowerBlocker

  missingPressureProjectionAndDivergenceFreeLimit :
    NavierStokesRegularityTowerBlocker

  missingBlowupExclusionOrSerrinCriterionDischarge :
    NavierStokesRegularityTowerBlocker

  finiteDepthBKMCriterionDoesNotDischargeContinuumBlowup :
    NavierStokesRegularityTowerBlocker

  missingContinuumBKMTheoremAuthority :
    NavierStokesRegularityTowerBlocker

  stokesSelfAdjointnessOnlyLinearPart :
    NavierStokesRegularityTowerBlocker

  nonlinearTransportContinuumControlMissing :
    NavierStokesRegularityTowerBlocker

  colimitRegularityLiftNotConstructed :
    NavierStokesRegularityTowerBlocker

  clayRegularityPromotionMissing :
    NavierStokesRegularityTowerBlocker

canonicalNavierStokesRegularityTowerBlockers :
  List NavierStokesRegularityTowerBlocker
canonicalNavierStokesRegularityTowerBlockers =
  finiteTowerLowerBoundIsNotPDERegularity
  ∷ finiteCarrierIncompressibleNavierStokesInterfaceRecordedOnly
  ∷ finiteCarrierLerayHopfWeakSolutionInterfaceRecordedOnly
  ∷ finiteDepthOnlyEnstrophyControl
  ∷ finiteDepthOnlyVorticityControl
  ∷ energyInequalityOnlyNoSmoothnessUpgrade
  ∷ missingPressureProjectionAndDivergenceFreeLimit
  ∷ missingBlowupExclusionOrSerrinCriterionDischarge
  ∷ finiteDepthBKMCriterionDoesNotDischargeContinuumBlowup
  ∷ missingContinuumBKMTheoremAuthority
  ∷ stokesSelfAdjointnessOnlyLinearPart
  ∷ nonlinearTransportContinuumControlMissing
  ∷ colimitRegularityLiftNotConstructed
  ∷ clayRegularityPromotionMissing
  ∷ []

data CarrierVectorField (depth : Nat) : Set where
  zeroVelocity :
    CarrierVectorField depth

data CarrierTestFunction (depth : Nat) : Set where
  zeroTestFunction :
    CarrierTestFunction depth

data CarrierScalar (depth : Nat) : Set where
  zeroScalar :
    CarrierScalar depth

data CarrierVorticity (depth : Nat) : Set where
  zeroVorticity :
    CarrierVorticity depth

data CarrierForce (depth : Nat) : Set where
  zeroForce :
    CarrierForce depth

carrierDivergence :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierScalar depth
carrierDivergence zeroVelocity =
  zeroScalar

carrierLerayProjection :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierVectorField depth
carrierLerayProjection zeroVelocity =
  zeroVelocity

carrierPairing :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierVectorField depth →
  CarrierScalar depth
carrierPairing zeroVelocity zeroVelocity =
  zeroScalar

carrierTransportPairing :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierVectorField depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierTransportPairing zeroVelocity zeroVelocity zeroTestFunction =
  zeroScalar

carrierViscousPairing :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierViscousPairing zeroVelocity zeroTestFunction =
  zeroScalar

carrierCurl :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierVorticity depth
carrierCurl zeroVelocity =
  zeroVorticity

carrierCurlForcePairing :
  {depth : Nat} →
  CarrierForce depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierCurlForcePairing zeroForce zeroTestFunction =
  zeroScalar

carrierVorticityTimePairing :
  {depth : Nat} →
  CarrierVorticity depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierVorticityTimePairing zeroVorticity zeroTestFunction =
  zeroScalar

carrierVorticityTransportPairing :
  {depth : Nat} →
  CarrierVectorField depth →
  CarrierVorticity depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierVorticityTransportPairing zeroVelocity zeroVorticity zeroTestFunction =
  zeroScalar

carrierVorticityStretchingPairing :
  {depth : Nat} →
  CarrierVorticity depth →
  CarrierVectorField depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierVorticityStretchingPairing zeroVorticity zeroVelocity zeroTestFunction =
  zeroScalar

carrierVorticityViscousPairing :
  {depth : Nat} →
  CarrierVorticity depth →
  CarrierTestFunction depth →
  CarrierScalar depth
carrierVorticityViscousPairing zeroVorticity zeroTestFunction =
  zeroScalar

record DivergenceFreeCarrier (depth : Nat) : Set where
  field
    velocity :
      CarrierVectorField depth

    divergenceZero :
      carrierDivergence velocity ≡ zeroScalar

    lerayProjection :
      CarrierVectorField depth →
      CarrierVectorField depth

    lerayProjectionIsCanonical :
      lerayProjection ≡ carrierLerayProjection

    projectedVelocity :
      CarrierVectorField depth

    projectedVelocityIsVelocity :
      projectedVelocity ≡ velocity

    projectedDivergenceZero :
      carrierDivergence projectedVelocity ≡ zeroScalar

open DivergenceFreeCarrier public

canonicalDivergenceFreeCarrier :
  (depth : Nat) →
  DivergenceFreeCarrier depth
canonicalDivergenceFreeCarrier depth =
  record
    { velocity =
        zeroVelocity
    ; divergenceZero =
        refl
    ; lerayProjection =
        carrierLerayProjection
    ; lerayProjectionIsCanonical =
        refl
    ; projectedVelocity =
        carrierLerayProjection zeroVelocity
    ; projectedVelocityIsVelocity =
        refl
    ; projectedDivergenceZero =
        refl
    }

record NavierStokesWeakSolutionInterface (depth : Nat) : Set where
  field
    divergenceFreeCarrier :
      DivergenceFreeCarrier depth

    testFunction :
      CarrierTestFunction depth

    weakTimePairing :
      CarrierScalar depth

    weakTransportPairing :
      CarrierScalar depth

    weakViscousPairing :
      CarrierScalar depth

    weakResidual :
      CarrierScalar depth

    weakTimePairingIsCanonical :
      weakTimePairing
      ≡
      carrierPairing
        (velocity divergenceFreeCarrier)
        (velocity divergenceFreeCarrier)

    weakTransportPairingIsCanonical :
      weakTransportPairing
      ≡
      carrierTransportPairing
        (velocity divergenceFreeCarrier)
        (velocity divergenceFreeCarrier)
        testFunction

    weakViscousPairingIsCanonical :
      weakViscousPairing
      ≡
      carrierViscousPairing
        (velocity divergenceFreeCarrier)
        testFunction

    weakResidualIsZero :
      weakResidual ≡ zeroScalar

    weakInterfaceConstructed :
      Bool

    weakInterfaceConstructedIsTrue :
      weakInterfaceConstructed ≡ true

    continuumSmoothnessPromoted :
      Bool

    continuumSmoothnessPromotedIsFalse :
      continuumSmoothnessPromoted ≡ false

open NavierStokesWeakSolutionInterface public

canonicalNavierStokesWeakSolutionInterface :
  (depth : Nat) →
  NavierStokesWeakSolutionInterface depth
canonicalNavierStokesWeakSolutionInterface depth =
  record
    { divergenceFreeCarrier =
        canonicalDivergenceFreeCarrier depth
    ; testFunction =
        zeroTestFunction
    ; weakTimePairing =
        zeroScalar
    ; weakTransportPairing =
        zeroScalar
    ; weakViscousPairing =
        zeroScalar
    ; weakResidual =
        zeroScalar
    ; weakTimePairingIsCanonical =
        refl
    ; weakTransportPairingIsCanonical =
        refl
    ; weakViscousPairingIsCanonical =
        refl
    ; weakResidualIsZero =
        refl
    ; weakInterfaceConstructed =
        true
    ; weakInterfaceConstructedIsTrue =
        refl
    ; continuumSmoothnessPromoted =
        false
    ; continuumSmoothnessPromotedIsFalse =
        refl
    }

record EnstrophyBound (depth : Nat) : Setω where
  field
    towerDepth :
      Nat

    towerDepthIsDepth :
      towerDepth ≡ depth

    enstrophyBoundUnit :
      Nat

    enstrophyBoundUnitIsCanonical :
      enstrophyBoundUnit ≡ suc zero

    enstrophyBoundPositive :
      suc zero ≤ enstrophyBoundUnit

    finiteDepthBoundRecorded :
      Bool

    finiteDepthBoundRecordedIsTrue :
      finiteDepthBoundRecorded ≡ true

    continuumRegularityPromotedAtDepth :
      Bool

    continuumRegularityPromotedAtDepthIsFalse :
      continuumRegularityPromotedAtDepth ≡ false

    enstrophyBoundary :
      List String

open EnstrophyBound public

enstrophyBoundAtDepth :
  (depth : Nat) →
  EnstrophyBound depth
enstrophyBoundAtDepth depth =
  record
    { towerDepth =
        depth
    ; towerDepthIsDepth =
        refl
    ; enstrophyBoundUnit =
        suc zero
    ; enstrophyBoundUnitIsCanonical =
        refl
    ; enstrophyBoundPositive =
        s≤s z≤n
    ; finiteDepthBoundRecorded =
        true
    ; finiteDepthBoundRecordedIsTrue =
        refl
    ; continuumRegularityPromotedAtDepth =
        false
    ; continuumRegularityPromotedAtDepthIsFalse =
        refl
    ; enstrophyBoundary =
        "Finite-depth enstrophy control is recorded at this tower depth"
        ∷ "The canonical bound unit is the same Nat unit used by the Gate 2 coercivity tower"
        ∷ "This finite-depth receipt does not promote continuum Navier-Stokes regularity"
        ∷ []
    }

carrierVorticityL2Norm :
  {depth : Nat} →
  CarrierVorticity depth →
  Nat
carrierVorticityL2Norm zeroVorticity =
  zero

record FiniteDepthVorticityControl (depth : Nat) : Setω where
  field
    towerDepth :
      Nat

    towerDepthIsDepth :
      towerDepth ≡ depth

    divergenceFreeCarrier :
      DivergenceFreeCarrier depth

    divergenceFreeCarrierIsCanonical :
      divergenceFreeCarrier ≡ canonicalDivergenceFreeCarrier depth

    vorticity :
      CarrierVorticity depth

    vorticityIsCurlVelocity :
      vorticity ≡ carrierCurl (velocity divergenceFreeCarrier)

    vorticityL2Norm :
      Nat

    vorticityL2NormIsCanonical :
      vorticityL2Norm ≡ carrierVorticityL2Norm vorticity

    finiteEnstrophyBound :
      EnstrophyBound depth

    finiteEnstrophyBoundRecorded :
      finiteDepthBoundRecorded finiteEnstrophyBound ≡ true

    vorticityControlledByEnstrophy :
      vorticityL2Norm ≤ enstrophyBoundUnit finiteEnstrophyBound

    finiteDepthVorticityControlRecorded :
      Bool

    finiteDepthVorticityControlRecordedIsTrue :
      finiteDepthVorticityControlRecorded ≡ true

    vortexStretchingControlledUniformly :
      Bool

    vortexStretchingControlledUniformlyIsFalse :
      vortexStretchingControlledUniformly ≡ false

    continuumRegularityPromotedByVorticityControl :
      Bool

    continuumRegularityPromotedByVorticityControlIsFalse :
      continuumRegularityPromotedByVorticityControl ≡ false

    vorticityControlBoundary :
      List String

open FiniteDepthVorticityControl public

finiteDepthVorticityControlAtDepth :
  (depth : Nat) →
  FiniteDepthVorticityControl depth
finiteDepthVorticityControlAtDepth depth =
  record
    { towerDepth =
        depth
    ; towerDepthIsDepth =
        refl
    ; divergenceFreeCarrier =
        canonicalDivergenceFreeCarrier depth
    ; divergenceFreeCarrierIsCanonical =
        refl
    ; vorticity =
        zeroVorticity
    ; vorticityIsCurlVelocity =
        refl
    ; vorticityL2Norm =
        zero
    ; vorticityL2NormIsCanonical =
        refl
    ; finiteEnstrophyBound =
        enstrophyBoundAtDepth depth
    ; finiteEnstrophyBoundRecorded =
        refl
    ; vorticityControlledByEnstrophy =
        z≤n
    ; finiteDepthVorticityControlRecorded =
        true
    ; finiteDepthVorticityControlRecordedIsTrue =
        refl
    ; vortexStretchingControlledUniformly =
        false
    ; vortexStretchingControlledUniformlyIsFalse =
        refl
    ; continuumRegularityPromotedByVorticityControl =
        false
    ; continuumRegularityPromotedByVorticityControlIsFalse =
        refl
    ; vorticityControlBoundary =
        "The finite-depth vorticity is the carrier curl of the canonical divergence-free velocity"
        ∷ "On the canonical zero carrier, the vorticity L2 norm is zero and is bounded by the finite enstrophy unit"
        ∷ "This records finite-depth vorticity control only; it does not supply a uniform vortex-stretching bound"
        ∷ "No continuum regularity or Clay-facing smoothness promotion follows from this receipt"
        ∷ []
    }

twoNat : Nat
twoNat =
  suc (suc zero)

record FiniteDepthL2EnergyEstimate (depth : Nat) : Setω where
  field
    towerDepth :
      Nat

    towerDepthIsDepth :
      towerDepth ≡ depth

    weakSolutionInterface :
      NavierStokesWeakSolutionInterface depth

    weakSolutionInterfaceIsCanonical :
      weakSolutionInterface ≡ canonicalNavierStokesWeakSolutionInterface depth

    viscosityCoefficient :
      Nat

    viscosityCoefficientIsFiniteUnit :
      viscosityCoefficient ≡ suc zero

    l2EnergyAtTime :
      Nat

    l2EnergyAtTimeIsCanonical :
      l2EnergyAtTime ≡ zero

    gradientDissipationIntegral :
      Nat

    gradientDissipationIntegralIsCanonical :
      gradientDissipationIntegral ≡ zero

    initialL2Energy :
      Nat

    initialL2EnergyIsCanonical :
      initialL2Energy ≡ zero

    l2EnergyDissipationLeftHandSide :
      Nat

    l2EnergyDissipationLeftHandSideIsCanonical :
      l2EnergyDissipationLeftHandSide
      ≡
      l2EnergyAtTime
      +
      ((twoNat * viscosityCoefficient) * gradientDissipationIntegral)

    finiteDepthL2EnergyEstimate :
      l2EnergyDissipationLeftHandSide ≤ initialL2Energy

    finiteDepthL2EnergyEstimateLabel :
      String

    finiteDepthL2EnergyEstimateLabelIsCanonical :
      finiteDepthL2EnergyEstimateLabel
      ≡
      "||u_n(t)||_L2^2 + 2 nu int_0^t ||grad u_n||_L2^2 ds <= ||u_0||_L2^2"

    finiteDepthEnergyEstimateRecorded :
      Bool

    finiteDepthEnergyEstimateRecordedIsTrue :
      finiteDepthEnergyEstimateRecorded ≡ true

    continuumRegularityObligationStillOpen :
      Bool

    continuumRegularityObligationStillOpenIsTrue :
      continuumRegularityObligationStillOpen ≡ true

    continuumRegularityPromotedByEnergyEstimate :
      Bool

    continuumRegularityPromotedByEnergyEstimateIsFalse :
      continuumRegularityPromotedByEnergyEstimate ≡ false

    energyEstimateBoundary :
      List String

open FiniteDepthL2EnergyEstimate public

finiteDepthL2EnergyEstimateAtDepth :
  (depth : Nat) →
  FiniteDepthL2EnergyEstimate depth
finiteDepthL2EnergyEstimateAtDepth depth =
  record
    { towerDepth =
        depth
    ; towerDepthIsDepth =
        refl
    ; weakSolutionInterface =
        canonicalNavierStokesWeakSolutionInterface depth
    ; weakSolutionInterfaceIsCanonical =
        refl
    ; viscosityCoefficient =
        suc zero
    ; viscosityCoefficientIsFiniteUnit =
        refl
    ; l2EnergyAtTime =
        zero
    ; l2EnergyAtTimeIsCanonical =
        refl
    ; gradientDissipationIntegral =
        zero
    ; gradientDissipationIntegralIsCanonical =
        refl
    ; initialL2Energy =
        zero
    ; initialL2EnergyIsCanonical =
        refl
    ; l2EnergyDissipationLeftHandSide =
        zero
    ; l2EnergyDissipationLeftHandSideIsCanonical =
        refl
    ; finiteDepthL2EnergyEstimate =
        z≤n
    ; finiteDepthL2EnergyEstimateLabel =
        "||u_n(t)||_L2^2 + 2 nu int_0^t ||grad u_n||_L2^2 ds <= ||u_0||_L2^2"
    ; finiteDepthL2EnergyEstimateLabelIsCanonical =
        refl
    ; finiteDepthEnergyEstimateRecorded =
        true
    ; finiteDepthEnergyEstimateRecordedIsTrue =
        refl
    ; continuumRegularityObligationStillOpen =
        true
    ; continuumRegularityObligationStillOpenIsTrue =
        refl
    ; continuumRegularityPromotedByEnergyEstimate =
        false
    ; continuumRegularityPromotedByEnergyEstimateIsFalse =
        refl
    ; energyEstimateBoundary =
        "The finite-depth L2 estimate is inhabited on the canonical finite zero carrier"
        ∷ "The left-hand side records kinetic energy plus 2 nu times the accumulated gradient dissipation"
        ∷ "The estimate is a finite-depth rung and does not discharge the continuum regularity obligation"
        ∷ []
    }

record FiniteDepthVorticityEquationRung (depth : Nat) : Setω where
  field
    towerDepth :
      Nat

    towerDepthIsDepth :
      towerDepth ≡ depth

    weakSolutionInterface :
      NavierStokesWeakSolutionInterface depth

    weakSolutionInterfaceIsCanonical :
      weakSolutionInterface ≡ canonicalNavierStokesWeakSolutionInterface depth

    velocityCurl :
      CarrierVorticity depth

    velocityCurlIsCanonical :
      velocityCurl
      ≡
      carrierCurl
        (velocity (divergenceFreeCarrier weakSolutionInterface))

    vorticity :
      CarrierVorticity depth

    vorticityIsVelocityCurl :
      vorticity ≡ velocityCurl

    vorticityTestFunction :
      CarrierTestFunction depth

    vorticityTestFunctionIsCanonical :
      vorticityTestFunction ≡ zeroTestFunction

    curlForce :
      CarrierForce depth

    curlForceIsCanonical :
      curlForce ≡ zeroForce

    vorticityTimePairing :
      CarrierScalar depth

    vorticityTimePairingIsCanonical :
      vorticityTimePairing
      ≡
      carrierVorticityTimePairing
        vorticity
        vorticityTestFunction

    vorticityTransportPairing :
      CarrierScalar depth

    vorticityTransportPairingIsCanonical :
      vorticityTransportPairing
      ≡
      carrierVorticityTransportPairing
        (velocity (divergenceFreeCarrier weakSolutionInterface))
        vorticity
        vorticityTestFunction

    vorticityStretchingPairing :
      CarrierScalar depth

    vorticityStretchingPairingIsCanonical :
      vorticityStretchingPairing
      ≡
      carrierVorticityStretchingPairing
        vorticity
        (velocity (divergenceFreeCarrier weakSolutionInterface))
        vorticityTestFunction

    vorticityViscousPairing :
      CarrierScalar depth

    vorticityViscousPairingIsCanonical :
      vorticityViscousPairing
      ≡
      carrierVorticityViscousPairing
        vorticity
        vorticityTestFunction

    vorticityCurlForcePairing :
      CarrierScalar depth

    vorticityCurlForcePairingIsCanonical :
      vorticityCurlForcePairing
      ≡
      carrierCurlForcePairing
        curlForce
        vorticityTestFunction

    vorticityEquationResidual :
      CarrierScalar depth

    vorticityEquationResidualIsZero :
      vorticityEquationResidual ≡ zeroScalar

    finiteDepthVorticityEquationRecorded :
      Bool

    finiteDepthVorticityEquationRecordedIsTrue :
      finiteDepthVorticityEquationRecorded ≡ true

    continuumRegularityPromotedByVorticityEquation :
      Bool

    continuumRegularityPromotedByVorticityEquationIsFalse :
      continuumRegularityPromotedByVorticityEquation ≡ false

    vorticityEquationLabel :
      String

    vorticityEquationLabelIsCanonical :
      vorticityEquationLabel
      ≡
      "partial_t omega + (u dot grad) omega - (omega dot grad) u - nu Delta omega = curl f"

    vorticityEquationBoundary :
      List String

open FiniteDepthVorticityEquationRung public

finiteDepthVorticityEquationRungAtDepth :
  (depth : Nat) →
  FiniteDepthVorticityEquationRung depth
finiteDepthVorticityEquationRungAtDepth depth =
  record
    { towerDepth =
        depth
    ; towerDepthIsDepth =
        refl
    ; weakSolutionInterface =
        canonicalNavierStokesWeakSolutionInterface depth
    ; weakSolutionInterfaceIsCanonical =
        refl
    ; velocityCurl =
        zeroVorticity
    ; velocityCurlIsCanonical =
        refl
    ; vorticity =
        zeroVorticity
    ; vorticityIsVelocityCurl =
        refl
    ; vorticityTestFunction =
        zeroTestFunction
    ; vorticityTestFunctionIsCanonical =
        refl
    ; curlForce =
        zeroForce
    ; curlForceIsCanonical =
        refl
    ; vorticityTimePairing =
        zeroScalar
    ; vorticityTimePairingIsCanonical =
        refl
    ; vorticityTransportPairing =
        zeroScalar
    ; vorticityTransportPairingIsCanonical =
        refl
    ; vorticityStretchingPairing =
        zeroScalar
    ; vorticityStretchingPairingIsCanonical =
        refl
    ; vorticityViscousPairing =
        zeroScalar
    ; vorticityViscousPairingIsCanonical =
        refl
    ; vorticityCurlForcePairing =
        zeroScalar
    ; vorticityCurlForcePairingIsCanonical =
        refl
    ; vorticityEquationResidual =
        zeroScalar
    ; vorticityEquationResidualIsZero =
        refl
    ; finiteDepthVorticityEquationRecorded =
        true
    ; finiteDepthVorticityEquationRecordedIsTrue =
        refl
    ; continuumRegularityPromotedByVorticityEquation =
        false
    ; continuumRegularityPromotedByVorticityEquationIsFalse =
        refl
    ; vorticityEquationLabel =
        "partial_t omega + (u dot grad) omega - (omega dot grad) u - nu Delta omega = curl f"
    ; vorticityEquationLabelIsCanonical =
        refl
    ; vorticityEquationBoundary =
        "The finite-depth vorticity equation is inhabited only on the canonical zero carrier"
        ∷ "The curl of the finite zero velocity is zero vorticity"
        ∷ "Time, transport, stretching, viscous, and curl-force pairings are all definitionally zero at this finite rung"
        ∷ "This rung records the vorticity equation shape without proving a continuum blowup exclusion or smoothness upgrade"
        ∷ []
    }

record FiniteDepthBKMVorticityIntegral (depth : Nat) : Setω where
  field
    towerDepth :
      Nat

    towerDepthIsDepth :
      towerDepth ≡ depth

    vorticityEquationRung :
      FiniteDepthVorticityEquationRung depth

    vorticityEquationRungRecorded :
      finiteDepthVorticityEquationRecorded vorticityEquationRung ≡ true

    linfinityVorticityNormIntegral :
      Nat

    linfinityVorticityNormIntegralIsZero :
      linfinityVorticityNormIntegral ≡ zero

    bkmFiniteThreshold :
      Nat

    bkmFiniteThresholdIsUnit :
      bkmFiniteThreshold ≡ suc zero

    bkmIntegralFiniteAtDepth :
      linfinityVorticityNormIntegral ≤ bkmFiniteThreshold

    bkmIntegralLabel :
      String

    bkmIntegralLabelIsCanonical :
      bkmIntegralLabel
      ≡
      "int_0^T ||curl u_n(t)||_L-infinity dt < infinity"

    finiteDepthVorticityIntegralRecorded :
      Bool

    finiteDepthVorticityIntegralRecordedIsTrue :
      finiteDepthVorticityIntegralRecorded ≡ true

    continuumBKMIntegralPromoted :
      Bool

    continuumBKMIntegralPromotedIsFalse :
      continuumBKMIntegralPromoted ≡ false

open FiniteDepthBKMVorticityIntegral public

finiteDepthBKMVorticityIntegralAtDepth :
  (depth : Nat) →
  FiniteDepthBKMVorticityIntegral depth
finiteDepthBKMVorticityIntegralAtDepth depth =
  record
    { towerDepth =
        depth
    ; towerDepthIsDepth =
        refl
    ; vorticityEquationRung =
        finiteDepthVorticityEquationRungAtDepth depth
    ; vorticityEquationRungRecorded =
        refl
    ; linfinityVorticityNormIntegral =
        zero
    ; linfinityVorticityNormIntegralIsZero =
        refl
    ; bkmFiniteThreshold =
        suc zero
    ; bkmFiniteThresholdIsUnit =
        refl
    ; bkmIntegralFiniteAtDepth =
        z≤n
    ; bkmIntegralLabel =
        "int_0^T ||curl u_n(t)||_L-infinity dt < infinity"
    ; bkmIntegralLabelIsCanonical =
        refl
    ; finiteDepthVorticityIntegralRecorded =
        true
    ; finiteDepthVorticityIntegralRecordedIsTrue =
        refl
    ; continuumBKMIntegralPromoted =
        false
    ; continuumBKMIntegralPromotedIsFalse =
        refl
    }

record NavierStokesEnergyInequalityReceipt : Set where
  field
    energyInequalityRecorded :
      Bool

    energyInequalityRecordedIsTrue :
      energyInequalityRecorded ≡ true

    l2EnergyNonincreaseLabel :
      String

    l2EnergyNonincreaseLabelIsCanonical :
      l2EnergyNonincreaseLabel
      ≡
      "||u(t)||_L2 <= ||u0||_L2"

    reflectionPositivityAnalogueLabel :
      String

    reflectionPositivityAnalogueLabelIsCanonical :
      reflectionPositivityAnalogueLabel
      ≡
      "Navier-Stokes energy inequality as the fail-closed reflection-positivity analogue"

    smoothnessUpgradeConstructed :
      Bool

    smoothnessUpgradeConstructedIsFalse :
      smoothnessUpgradeConstructed ≡ false

    energyBoundary :
      List String

open NavierStokesEnergyInequalityReceipt public

canonicalNavierStokesEnergyInequalityReceipt :
  NavierStokesEnergyInequalityReceipt
canonicalNavierStokesEnergyInequalityReceipt =
  record
    { energyInequalityRecorded =
        true
    ; energyInequalityRecordedIsTrue =
        refl
    ; l2EnergyNonincreaseLabel =
        "||u(t)||_L2 <= ||u0||_L2"
    ; l2EnergyNonincreaseLabelIsCanonical =
        refl
    ; reflectionPositivityAnalogueLabel =
        "Navier-Stokes energy inequality as the fail-closed reflection-positivity analogue"
    ; reflectionPositivityAnalogueLabelIsCanonical =
        refl
    ; smoothnessUpgradeConstructed =
        false
    ; smoothnessUpgradeConstructedIsFalse =
        refl
    ; energyBoundary =
        "The energy inequality is recorded as a structural analogue only"
        ∷ "It is not upgraded here to a global smoothness theorem"
        ∷ []
    }

record StokesOperatorCarrierReceipt : Setω where
  field
    stokesOperatorLabel :
      String

    stokesOperatorLabelIsCanonical :
      stokesOperatorLabel ≡ "-nu-Delta-on-divergence-free-L2"

    linearSelfAdjointnessRecorded :
      Bool

    linearSelfAdjointnessRecordedIsTrue :
      linearSelfAdjointnessRecorded ≡ true

    nonlinearTransportControlled :
      Bool

    nonlinearTransportControlledIsFalse :
      nonlinearTransportControlled ≡ false

    operatorBoundary :
      List String

open StokesOperatorCarrierReceipt public

canonicalStokesOperatorCarrierReceipt :
  StokesOperatorCarrierReceipt
canonicalStokesOperatorCarrierReceipt =
  record
    { stokesOperatorLabel =
        "-nu-Delta-on-divergence-free-L2"
    ; stokesOperatorLabelIsCanonical =
        refl
    ; linearSelfAdjointnessRecorded =
        true
    ; linearSelfAdjointnessRecordedIsTrue =
        refl
    ; nonlinearTransportControlled =
        false
    ; nonlinearTransportControlledIsFalse =
        refl
    ; operatorBoundary =
        "The Stokes operator is recorded as the linear self-adjoint carrier analogue"
        ∷ "The nonlinear transport term is not controlled by this receipt"
        ∷ "The existing Gate 2 selected-carrier bundle pattern is used only as a structural receipt shape"
        ∷ []
    }

data SobolevVelocityAtDepth (depth regularity : Nat) : Set where
  zeroSobolevVelocity :
    SobolevVelocityAtDepth depth regularity

data FiniteClosedIntervalTime (horizon : Nat) : Set where
  finiteIntervalStart :
    FiniteClosedIntervalTime horizon

  finiteIntervalEnd :
    FiniteClosedIntervalTime horizon

record ContinuousSobolevPathAtFiniteDepth
  (depth regularity horizon : Nat) : Set where
  field
    valueAtFiniteTime :
      FiniteClosedIntervalTime horizon →
      SobolevVelocityAtDepth depth regularity

    pathSpaceLabel :
      String

    pathSpaceLabelIsCanonical :
      pathSpaceLabel ≡ "C([0,T_n]; H^s)"

    continuousOnFiniteClosedInterval :
      Bool

    continuousOnFiniteClosedIntervalIsTrue :
      continuousOnFiniteClosedInterval ≡ true

    valueAtStart :
      SobolevVelocityAtDepth depth regularity

    valueAtStartIsCanonical :
      valueAtStart ≡ valueAtFiniteTime finiteIntervalStart

open ContinuousSobolevPathAtFiniteDepth public

canonicalContinuousSobolevPathAtFiniteDepth :
  (depth regularity horizon : Nat) →
  ContinuousSobolevPathAtFiniteDepth depth regularity horizon
canonicalContinuousSobolevPathAtFiniteDepth depth regularity horizon =
  record
    { valueAtFiniteTime =
        λ _ → zeroSobolevVelocity
    ; pathSpaceLabel =
        "C([0,T_n]; H^s)"
    ; pathSpaceLabelIsCanonical =
        refl
    ; continuousOnFiniteClosedInterval =
        true
    ; continuousOnFiniteClosedIntervalIsTrue =
        refl
    ; valueAtStart =
        zeroSobolevVelocity
    ; valueAtStartIsCanonical =
        refl
    }

record FiniteDepthLocalExistenceRung
  (depth regularity : Nat) : Setω where
  field
    finiteDepth :
      Nat

    finiteDepthIsDepth :
      finiteDepth ≡ depth

    sobolevRegularity :
      Nat

    sobolevRegularityIsRegularity :
      sobolevRegularity ≡ regularity

    localTimeHorizon :
      Nat

    localTimeHorizonIsCanonical :
      localTimeHorizon ≡ suc depth

    localTimeHorizonPositive :
      suc zero ≤ localTimeHorizon

    solution :
      ContinuousSobolevPathAtFiniteDepth
        depth
        regularity
        localTimeHorizon

    solutionAtInitialTime :
      SobolevVelocityAtDepth depth regularity

    solutionStartsAtInitialData :
      solutionAtInitialTime
      ≡
      valueAtFiniteTime solution finiteIntervalStart

    finiteWeakSolutionInterface :
      NavierStokesWeakSolutionInterface depth

    finiteWeakSolutionInterfaceConstructed :
      weakInterfaceConstructed finiteWeakSolutionInterface ≡ true

    finiteEnstrophyBound :
      EnstrophyBound depth

    finiteEnstrophyBoundRecorded :
      finiteDepthBoundRecorded finiteEnstrophyBound ≡ true

    localExistenceConstructed :
      Bool

    localExistenceConstructedIsTrue :
      localExistenceConstructed ≡ true

    continuumRegularityPromotedByLocalExistence :
      Bool

    continuumRegularityPromotedByLocalExistenceIsFalse :
      continuumRegularityPromotedByLocalExistence ≡ false

    localExistenceBoundary :
      List String

open FiniteDepthLocalExistenceRung public

finiteDepthLocalExistenceRung :
  (depth regularity : Nat) →
  FiniteDepthLocalExistenceRung depth regularity
finiteDepthLocalExistenceRung depth regularity =
  record
    { finiteDepth =
        depth
    ; finiteDepthIsDepth =
        refl
    ; sobolevRegularity =
        regularity
    ; sobolevRegularityIsRegularity =
        refl
    ; localTimeHorizon =
        suc depth
    ; localTimeHorizonIsCanonical =
        refl
    ; localTimeHorizonPositive =
        s≤s z≤n
    ; solution =
        canonicalContinuousSobolevPathAtFiniteDepth
          depth
          regularity
          (suc depth)
    ; solutionAtInitialTime =
        zeroSobolevVelocity
    ; solutionStartsAtInitialData =
        refl
    ; finiteWeakSolutionInterface =
        canonicalNavierStokesWeakSolutionInterface depth
    ; finiteWeakSolutionInterfaceConstructed =
        refl
    ; finiteEnstrophyBound =
        enstrophyBoundAtDepth depth
    ; finiteEnstrophyBoundRecorded =
        refl
    ; localExistenceConstructed =
        true
    ; localExistenceConstructedIsTrue =
        refl
    ; continuumRegularityPromotedByLocalExistence =
        false
    ; continuumRegularityPromotedByLocalExistenceIsFalse =
        refl
    ; localExistenceBoundary =
        "For each finite tower depth n, the canonical zero solution u_n is a finite carrier path in C([0,T_n]; H^s)"
        ∷ "The local time horizon is T_n = suc n, so T_n > 0 in the Nat time carrier"
        ∷ "This is a finite-depth local-existence receipt only"
        ∷ "No uniform-in-depth time interval, pressure limit, blowup exclusion, or continuum smoothness theorem is claimed"
        ∷ []
    }

record FiniteDepthBKMContinuationCriterion
  (depth regularity : Nat) : Setω where
  field
    finiteDepth :
      Nat

    finiteDepthIsDepth :
      finiteDepth ≡ depth

    sobolevRegularity :
      Nat

    sobolevRegularityIsRegularity :
      sobolevRegularity ≡ regularity

    localExistenceRung :
      FiniteDepthLocalExistenceRung depth regularity

    localExistenceRungConstructed :
      localExistenceConstructed localExistenceRung ≡ true

    bkmVorticityIntegral :
      FiniteDepthBKMVorticityIntegral depth

    bkmVorticityIntegralRecorded :
      finiteDepthVorticityIntegralRecorded bkmVorticityIntegral ≡ true

    bkmIntegralFinite :
      linfinityVorticityNormIntegral bkmVorticityIntegral
      ≤
      bkmFiniteThreshold bkmVorticityIntegral

    continuedTimeHorizon :
      Nat

    continuedTimeHorizonIsOneStepExtension :
      continuedTimeHorizon
      ≡
      suc (localTimeHorizon localExistenceRung)

    continuationPath :
      ContinuousSobolevPathAtFiniteDepth
        depth
        regularity
        continuedTimeHorizon

    finiteDepthContinuationCriterionLabel :
      String

    finiteDepthContinuationCriterionLabelIsBKM :
      finiteDepthContinuationCriterionLabel
      ≡
      "Beale-Kato-Majda finite-depth continuation: bounded vorticity integral extends the finite carrier solution"

    finiteDepthContinuationConstructed :
      Bool

    finiteDepthContinuationConstructedIsTrue :
      finiteDepthContinuationConstructed ≡ true

    continuumContinuationAuthorityAvailable :
      Bool

    continuumContinuationAuthorityAvailableIsFalse :
      continuumContinuationAuthorityAvailable ≡ false

    continuumRegularityPromotedByBKM :
      Bool

    continuumRegularityPromotedByBKMIsFalse :
      continuumRegularityPromotedByBKM ≡ false

    bkmContinuationBoundary :
      List String

open FiniteDepthBKMContinuationCriterion public

finiteDepthBKMContinuationCriterion :
  (depth regularity : Nat) →
  FiniteDepthBKMContinuationCriterion depth regularity
finiteDepthBKMContinuationCriterion depth regularity =
  record
    { finiteDepth =
        depth
    ; finiteDepthIsDepth =
        refl
    ; sobolevRegularity =
        regularity
    ; sobolevRegularityIsRegularity =
        refl
    ; localExistenceRung =
        finiteDepthLocalExistenceRung depth regularity
    ; localExistenceRungConstructed =
        refl
    ; bkmVorticityIntegral =
        finiteDepthBKMVorticityIntegralAtDepth depth
    ; bkmVorticityIntegralRecorded =
        refl
    ; bkmIntegralFinite =
        bkmIntegralFiniteAtDepth
          (finiteDepthBKMVorticityIntegralAtDepth depth)
    ; continuedTimeHorizon =
        suc (localTimeHorizon (finiteDepthLocalExistenceRung depth regularity))
    ; continuedTimeHorizonIsOneStepExtension =
        refl
    ; continuationPath =
        canonicalContinuousSobolevPathAtFiniteDepth
          depth
          regularity
          (suc (localTimeHorizon (finiteDepthLocalExistenceRung depth regularity)))
    ; finiteDepthContinuationCriterionLabel =
        "Beale-Kato-Majda finite-depth continuation: bounded vorticity integral extends the finite carrier solution"
    ; finiteDepthContinuationCriterionLabelIsBKM =
        refl
    ; finiteDepthContinuationConstructed =
        true
    ; finiteDepthContinuationConstructedIsTrue =
        refl
    ; continuumContinuationAuthorityAvailable =
        false
    ; continuumContinuationAuthorityAvailableIsFalse =
        refl
    ; continuumRegularityPromotedByBKM =
        false
    ; continuumRegularityPromotedByBKMIsFalse =
        refl
    ; bkmContinuationBoundary =
        "At each finite Nat depth, the canonical zero carrier has zero vorticity"
        ∷ "The finite-depth BKM integral int_0^T ||curl u_n||_L-infinity dt is bounded by the unit Nat threshold"
        ∷ "The continuation path is constructed only on the finite carrier by extending T_n to suc T_n"
        ∷ "No uniform-in-depth BKM estimate, no continuum vorticity norm, and no continuum continuation theorem are constructed"
        ∷ []
    }

record ContinuumBKMAuthorityObligation : Set₁ where
  field
    BealeKatoMajdaContinuumTheoremObligation :
      Set

    UniformVorticityIntegralLimitObligation :
      Set

    ContinuumLinfinityVorticityNormObligation :
      Set

    SmoothContinuationFromBKMObligation :
      Set

    finiteDepthBKMReceiptAvailable :
      Bool

    finiteDepthBKMReceiptAvailableIsTrue :
      finiteDepthBKMReceiptAvailable ≡ true

    continuumBKMAuthorityAvailable :
      Bool

    continuumBKMAuthorityAvailableIsFalse :
      continuumBKMAuthorityAvailable ≡ false

    continuumContinuationConstructedFromBKM :
      Bool

    continuumContinuationConstructedFromBKMIsFalse :
      continuumContinuationConstructedFromBKM ≡ false

    clayRegularityPromotedByBKM :
      Bool

    clayRegularityPromotedByBKMIsFalse :
      clayRegularityPromotedByBKM ≡ false

    bkmAuthorityBoundary :
      List String

open ContinuumBKMAuthorityObligation public

canonicalContinuumBKMAuthorityObligation :
  ContinuumBKMAuthorityObligation
canonicalContinuumBKMAuthorityObligation =
  record
    { BealeKatoMajdaContinuumTheoremObligation =
        Nat
    ; UniformVorticityIntegralLimitObligation =
        Nat
    ; ContinuumLinfinityVorticityNormObligation =
        Nat
    ; SmoothContinuationFromBKMObligation =
        Nat
    ; finiteDepthBKMReceiptAvailable =
        true
    ; finiteDepthBKMReceiptAvailableIsTrue =
        refl
    ; continuumBKMAuthorityAvailable =
        false
    ; continuumBKMAuthorityAvailableIsFalse =
        refl
    ; continuumContinuationConstructedFromBKM =
        false
    ; continuumContinuationConstructedFromBKMIsFalse =
        refl
    ; clayRegularityPromotedByBKM =
        false
    ; clayRegularityPromotedByBKMIsFalse =
        refl
    ; bkmAuthorityBoundary =
        "The finite-depth BKM receipt is available only on the finite carrier tower"
        ∷ "A continuum BKM theorem authority is an explicit external analytic obligation here"
        ∷ "Uniform passage of the L-infinity vorticity integral through the depth colimit is not constructed"
        ∷ "BKM does not promote Clay Navier-Stokes regularity in this module"
        ∷ []
    }

record ContinuumRegularityObligation : Setω where
  field
    SmoothDivergenceFreeInitialDataObligation :
      Set₁

    LerayProjectionPressureObligation :
      Set₁

    UniformEnstrophyToContinuumObligation :
      Set₁

    BKMAuthorityObligation :
      ContinuumBKMAuthorityObligation

    continuumBKMContinuationAuthorityAvailable :
      Bool

    continuumBKMContinuationAuthorityAvailableIsFalse :
      continuumBKMContinuationAuthorityAvailable ≡ false

    ClayRegularityAcceptanceObligation :
      Set₁

    continuumRegularityLiftConstructed :
      Bool

    continuumRegularityLiftConstructedIsFalse :
      continuumRegularityLiftConstructed ≡ false

    continuumClayNavierStokesPromoted :
      Bool

    continuumClayNavierStokesPromotedIsFalse :
      continuumClayNavierStokesPromoted ≡ false

    obligationBoundary :
      List String

open ContinuumRegularityObligation public

canonicalContinuumRegularityObligation :
  ContinuumRegularityObligation
canonicalContinuumRegularityObligation =
  record
    { SmoothDivergenceFreeInitialDataObligation =
        Set
    ; LerayProjectionPressureObligation =
        Set
    ; UniformEnstrophyToContinuumObligation =
        Set
    ; BKMAuthorityObligation =
        canonicalContinuumBKMAuthorityObligation
    ; continuumBKMContinuationAuthorityAvailable =
        false
    ; continuumBKMContinuationAuthorityAvailableIsFalse =
        refl
    ; ClayRegularityAcceptanceObligation =
        Set
    ; continuumRegularityLiftConstructed =
        false
    ; continuumRegularityLiftConstructedIsFalse =
        refl
    ; continuumClayNavierStokesPromoted =
        false
    ; continuumClayNavierStokesPromotedIsFalse =
        refl
    ; obligationBoundary =
        "Smooth divergence-free initial data are an abstract obligation here"
        ∷ "Pressure/Leray projection transport is an abstract obligation here"
        ∷ "Uniform enstrophy persistence through the continuum limit is not constructed"
        ∷ "Beale-Kato-Majda continuation is recorded only as a finite-depth criterion; continuum BKM authority remains fail-closed"
        ∷ "Clay-facing Navier-Stokes regularity promotion remains false"
        ∷ []
    }

record NavierStokesRegularityTowerReceipt : Setω where
  field
    status :
      NavierStokesRegularityTowerStatus

    towerModels :
      List NavierStokesTowerModel

    towerModelsAreCanonical :
      towerModels ≡ canonicalNavierStokesTowerModels

    enstrophyBoundAtEveryDepth :
      (depth : Nat) →
      EnstrophyBound depth

    finiteDepthVorticityControlAtEveryDepth :
      (depth : Nat) →
      FiniteDepthVorticityControl depth

    finiteDepthVorticityControlRecordedAtDepthZero :
      finiteDepthVorticityControlRecorded
        (finiteDepthVorticityControlAtEveryDepth zero)
      ≡
      true

    finiteDepthVorticityControlKeepsContinuumFalseAtDepthZero :
      continuumRegularityPromotedByVorticityControl
        (finiteDepthVorticityControlAtEveryDepth zero)
      ≡
      false

    finiteDepthVorticityControlDoesNotUniformlyControlStretchingAtDepthZero :
      vortexStretchingControlledUniformly
        (finiteDepthVorticityControlAtEveryDepth zero)
      ≡
      false

    finiteDepthVorticityEquationAtEveryDepth :
      (depth : Nat) →
      FiniteDepthVorticityEquationRung depth

    finiteDepthVorticityEquationRecordedAtDepthZero :
      finiteDepthVorticityEquationRecorded
        (finiteDepthVorticityEquationAtEveryDepth zero)
      ≡
      true

    finiteDepthVorticityEquationKeepsContinuumFalseAtDepthZero :
      continuumRegularityPromotedByVorticityEquation
        (finiteDepthVorticityEquationAtEveryDepth zero)
      ≡
      false

    finiteDepthBKMVorticityIntegralAtEveryDepth :
      (depth : Nat) →
      FiniteDepthBKMVorticityIntegral depth

    finiteDepthBKMVorticityIntegralRecordedAtDepthZero :
      finiteDepthVorticityIntegralRecorded
        (finiteDepthBKMVorticityIntegralAtEveryDepth zero)
      ≡
      true

    finiteDepthBKMVorticityIntegralKeepsContinuumFalseAtDepthZero :
      continuumBKMIntegralPromoted
        (finiteDepthBKMVorticityIntegralAtEveryDepth zero)
      ≡
      false

    finiteDepthL2EnergyEstimateAtEveryDepth :
      (depth : Nat) →
      FiniteDepthL2EnergyEstimate depth

    finiteDepthL2EnergyEstimateRecordedAtDepthZero :
      finiteDepthEnergyEstimateRecorded
        (finiteDepthL2EnergyEstimateAtEveryDepth zero)
      ≡
      true

    finiteDepthL2EnergyEstimateDoesNotPromoteContinuumAtDepthZero :
      continuumRegularityPromotedByEnergyEstimate
        (finiteDepthL2EnergyEstimateAtEveryDepth zero)
      ≡
      false

    divergenceFreeCarrierAtEveryDepth :
      (depth : Nat) →
      DivergenceFreeCarrier depth

    weakSolutionInterfaceAtEveryDepth :
      (depth : Nat) →
      NavierStokesWeakSolutionInterface depth

    weakSolutionInterfaceConstructedAtDepthZero :
      weakInterfaceConstructed
        (weakSolutionInterfaceAtEveryDepth zero)
      ≡
      true

    finiteDepthLocalExistenceAtEveryDepth :
      (regularity depth : Nat) →
      FiniteDepthLocalExistenceRung depth regularity

    finiteDepthLocalExistenceConstructedAtDepthZero :
      localExistenceConstructed
        (finiteDepthLocalExistenceAtEveryDepth (suc zero) zero)
      ≡
      true

    finiteDepthLocalExistenceKeepsContinuumFalseAtDepthZero :
      continuumRegularityPromotedByLocalExistence
        (finiteDepthLocalExistenceAtEveryDepth (suc zero) zero)
      ≡
      false

    finiteDepthBKMContinuationAtEveryDepth :
      (regularity depth : Nat) →
      FiniteDepthBKMContinuationCriterion depth regularity

    finiteDepthBKMContinuationConstructedAtDepthZero :
      finiteDepthContinuationConstructed
        (finiteDepthBKMContinuationAtEveryDepth (suc zero) zero)
      ≡
      true

    finiteDepthBKMContinuationKeepsContinuumFalseAtDepthZero :
      continuumRegularityPromotedByBKM
        (finiteDepthBKMContinuationAtEveryDepth (suc zero) zero)
      ≡
      false

    finiteDepthBKMContinuationAuthorityFalseAtDepthZero :
      continuumContinuationAuthorityAvailable
        (finiteDepthBKMContinuationAtEveryDepth (suc zero) zero)
      ≡
      false

    carrierLevelWeakSolutionInterfaceReceipt :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt

    carrierLevelWeakSolutionInterfaceReceiptIsCanonical :
      carrierLevelWeakSolutionInterfaceReceipt
      ≡
      NSWeak.canonicalNavierStokesWeakSolutionInterfaceReceipt

    carrierLevelWeakFormulationRecorded :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt.carrierWeakFormulationRecorded
        carrierLevelWeakSolutionInterfaceReceipt
      ≡
      true

    carrierLevelWeakSolutionContinuumRegularityPromotedFalse :
      NSWeak.NavierStokesWeakSolutionInterfaceReceipt.continuumRegularityPromoted
        carrierLevelWeakSolutionInterfaceReceipt
      ≡
      false

    uniformCoercivity :
      Gate2.UniformLowerBound Gate2.gate2CanonicalGap

    uniformCoercivityReusedOnlyAsAnalogy :
      Bool

    uniformCoercivityReusedOnlyAsAnalogyIsTrue :
      uniformCoercivityReusedOnlyAsAnalogy ≡ true

    uniformCoercivityIsCanonical :
      Gate2.UniformLowerBound.canonicalToolkitRecorded
        uniformCoercivity
      ≡
      true

    gate2UniformLowerBound :
      Gate2.UniformLowerBound Gate2.gate2CanonicalGap

    colimitGapLift :
      Gate2.GapProof∞ Gate2.gate2CanonicalGap

    colimitGapLiftPromotedFalse :
      Gate2.GapProof∞.gapLiftPromoted colimitGapLift
      ≡
      false

    colimitRegularityLift :
      Gate2.GapProof∞ Gate2.gate2CanonicalGap

    colimitRegularityLiftReusedOnlyAsAnalogy :
      Bool

    colimitRegularityLiftReusedOnlyAsAnalogyIsTrue :
      colimitRegularityLiftReusedOnlyAsAnalogy ≡ true

    energyInequality :
      NavierStokesEnergyInequalityReceipt

    stokesOperatorCarrier :
      StokesOperatorCarrierReceipt

    continuumLimitObligation :
      ContinuumRegularityObligation

    continuumBKMAuthorityObligation :
      ContinuumBKMAuthorityObligation

    continuumBKMAuthorityAvailableFalse :
      continuumBKMAuthorityAvailable continuumBKMAuthorityObligation
      ≡
      false

    continuumRegularityLiftConstructed :
      Bool

    continuumRegularityLiftConstructedIsFalse :
      continuumRegularityLiftConstructed ≡ false

    continuumClayNavierStokesPromoted :
      Bool

    continuumClayNavierStokesPromotedIsFalse :
      continuumClayNavierStokesPromoted ≡ false

    openObligations :
      List NavierStokesRegularityOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalNavierStokesRegularityOpenObligations

    exactBlockers :
      List NavierStokesRegularityTowerBlocker

    exactBlockersAreCanonical :
      exactBlockers
      ≡
      canonicalNavierStokesRegularityTowerBlockers

    receiptBoundary :
      List String

open NavierStokesRegularityTowerReceipt public

canonicalNavierStokesRegularityTowerReceipt :
  NavierStokesRegularityTowerReceipt
canonicalNavierStokesRegularityTowerReceipt =
  record
    { status =
        finiteDepthEnstrophyTowerRecordedContinuumOpen
    ; towerModels =
        canonicalNavierStokesTowerModels
    ; towerModelsAreCanonical =
        refl
    ; enstrophyBoundAtEveryDepth =
        enstrophyBoundAtDepth
    ; finiteDepthVorticityControlAtEveryDepth =
        finiteDepthVorticityControlAtDepth
    ; finiteDepthVorticityControlRecordedAtDepthZero =
        refl
    ; finiteDepthVorticityControlKeepsContinuumFalseAtDepthZero =
        refl
    ; finiteDepthVorticityControlDoesNotUniformlyControlStretchingAtDepthZero =
        refl
    ; finiteDepthVorticityEquationAtEveryDepth =
        finiteDepthVorticityEquationRungAtDepth
    ; finiteDepthVorticityEquationRecordedAtDepthZero =
        refl
    ; finiteDepthVorticityEquationKeepsContinuumFalseAtDepthZero =
        refl
    ; finiteDepthBKMVorticityIntegralAtEveryDepth =
        finiteDepthBKMVorticityIntegralAtDepth
    ; finiteDepthBKMVorticityIntegralRecordedAtDepthZero =
        refl
    ; finiteDepthBKMVorticityIntegralKeepsContinuumFalseAtDepthZero =
        refl
    ; finiteDepthL2EnergyEstimateAtEveryDepth =
        finiteDepthL2EnergyEstimateAtDepth
    ; finiteDepthL2EnergyEstimateRecordedAtDepthZero =
        refl
    ; finiteDepthL2EnergyEstimateDoesNotPromoteContinuumAtDepthZero =
        refl
    ; divergenceFreeCarrierAtEveryDepth =
        canonicalDivergenceFreeCarrier
    ; weakSolutionInterfaceAtEveryDepth =
        canonicalNavierStokesWeakSolutionInterface
    ; weakSolutionInterfaceConstructedAtDepthZero =
        refl
    ; finiteDepthLocalExistenceAtEveryDepth =
        λ regularity depth →
          finiteDepthLocalExistenceRung depth regularity
    ; finiteDepthLocalExistenceConstructedAtDepthZero =
        refl
    ; finiteDepthLocalExistenceKeepsContinuumFalseAtDepthZero =
        refl
    ; finiteDepthBKMContinuationAtEveryDepth =
        λ regularity depth →
          finiteDepthBKMContinuationCriterion depth regularity
    ; finiteDepthBKMContinuationConstructedAtDepthZero =
        refl
    ; finiteDepthBKMContinuationKeepsContinuumFalseAtDepthZero =
        refl
    ; finiteDepthBKMContinuationAuthorityFalseAtDepthZero =
        refl
    ; carrierLevelWeakSolutionInterfaceReceipt =
        NSWeak.canonicalNavierStokesWeakSolutionInterfaceReceipt
    ; carrierLevelWeakSolutionInterfaceReceiptIsCanonical =
        refl
    ; carrierLevelWeakFormulationRecorded =
        refl
    ; carrierLevelWeakSolutionContinuumRegularityPromotedFalse =
        refl
    ; uniformCoercivity =
        Gate2.canonicalUniformLowerBound
    ; uniformCoercivityReusedOnlyAsAnalogy =
        true
    ; uniformCoercivityReusedOnlyAsAnalogyIsTrue =
        refl
    ; uniformCoercivityIsCanonical =
        refl
    ; gate2UniformLowerBound =
        Gate2.canonicalUniformLowerBound
    ; colimitGapLift =
        Gate2.ColimitGapLift Gate2.canonicalUniformLowerBound
    ; colimitGapLiftPromotedFalse =
        refl
    ; colimitRegularityLift =
        Gate2.ColimitGapLift Gate2.canonicalUniformLowerBound
    ; colimitRegularityLiftReusedOnlyAsAnalogy =
        true
    ; colimitRegularityLiftReusedOnlyAsAnalogyIsTrue =
        refl
    ; energyInequality =
        canonicalNavierStokesEnergyInequalityReceipt
    ; stokesOperatorCarrier =
        canonicalStokesOperatorCarrierReceipt
    ; continuumLimitObligation =
        canonicalContinuumRegularityObligation
    ; continuumBKMAuthorityObligation =
        canonicalContinuumBKMAuthorityObligation
    ; continuumBKMAuthorityAvailableFalse =
        refl
    ; continuumRegularityLiftConstructed =
        false
    ; continuumRegularityLiftConstructedIsFalse =
        refl
    ; continuumClayNavierStokesPromoted =
        false
    ; continuumClayNavierStokesPromotedIsFalse =
        refl
    ; openObligations =
        canonicalNavierStokesRegularityOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; exactBlockers =
        canonicalNavierStokesRegularityTowerBlockers
    ; exactBlockersAreCanonical =
        refl
    ; receiptBoundary =
        "Navier-Stokes regularity is recorded as a depth-tower structural receipt"
        ∷ "Finite-depth enstrophy control is supplied at every Nat depth"
        ∷ "Finite-depth vorticity control is supplied at every Nat depth on the canonical zero-curl carrier and keeps vortex-stretching control false"
        ∷ "The finite-depth vorticity equation rung is recorded at every Nat depth without claiming a continuum BKM blowup exclusion"
        ∷ "The Beale-Kato-Majda vorticity-integral criterion is inhabited at every finite depth by the zero-vorticity carrier"
        ∷ "The finite-depth L2 energy estimate rung is inhabited at every Nat depth with the continuum regularity obligation kept open"
        ∷ "The finite-depth vorticity equation rung is inhabited at every Nat depth on the canonical zero curl, with stretching/transport/viscous/curl-force pairings all zero"
        ∷ "For every finite Nat depth n and Sobolev index s, a finite carrier local solution u_n in C([0,T_n]; H^s) is supplied with T_n = suc n > 0"
        ∷ "BKM continuation extends only the finite carrier horizon from T_n to suc T_n; continuum BKM authority remains false"
        ∷ "A concrete finite carrier divergence-free velocity, Leray projection, and zero-residual weak test-function interface are supplied at every depth"
        ∷ "The canonical carrier-level weak formulation, divergence-free interface, Leray projection, and Leray-Hopf energy lane are consumed from NavierStokesWeakSolutionInterface"
        ∷ "UniformLowerBoundOnTower is consumed only as a finite Nat-tower lower-bound witness"
        ∷ "Gate2.ColimitGapLift and ColimitGapLiftOnHamiltonian are consumed only as non-promoting structural analogues"
        ∷ "The weak carrier interface is finite-depth only; no continuum smoothness upgrade, pressure limit, or blowup exclusion is constructed"
        ∷ "The energy inequality is recorded without claiming a smoothness upgrade"
        ∷ "Continuum Beale-Kato-Majda theorem authority is an explicit fail-closed obligation"
        ∷ "Continuum regularity and Clay promotion remain explicit false obligations"
        ∷ []
    }

navierStokesRegularityTowerKeepsClayFalse :
  continuumClayNavierStokesPromoted
    canonicalNavierStokesRegularityTowerReceipt
  ≡
  false
navierStokesRegularityTowerKeepsClayFalse =
  refl

navierStokesRegularityTowerKeepsContinuumLiftFalse :
  continuumRegularityLiftConstructed
    canonicalNavierStokesRegularityTowerReceipt
  ≡
  false
navierStokesRegularityTowerKeepsContinuumLiftFalse =
  refl

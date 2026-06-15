module DASHI.Physics.Closure.GRProofArchitectureAggregationTest where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GRConcreteLeviCivita as LeviCivita
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as Bianchi
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as Scalar
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as CRTConnection
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as EinsteinTensor
import DASHI.Physics.Closure.EinsteinEquationCandidate as EinsteinEquation
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild
import DASHI.Physics.Closure.ContinuumLimitTheorem as Continuum
import DASHI.Physics.Closure.GRGate4TowerSchemaInstance as Gate4
import MonsterOntos as MO
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- GR proof-architecture aggregation test.
--
-- This module checks that the currently importable GR closure surfaces can be
-- threaded together without adding unproved axioms or promoting any GR claim.

data GRProofArchitectureAggregationStatus : Set where
  checkedAggregationOnlyNoPromotion :
    GRProofArchitectureAggregationStatus

record GRProofArchitectureAggregationTest : Setω where
  field
    status :
      GRProofArchitectureAggregationStatus

    flatLeviCivitaSurface :
      LeviCivita.GRConcreteLeviCivitaSurface

    flatLeviCivitaResidual :
      LeviCivita.GRConcreteLeviCivitaSurface.residual flatLeviCivitaSurface
      ≡
      LeviCivita.nonFlatSelectedGRStillOpen

    flatLeviCivitaFirstMissing :
      LeviCivita.GRConcreteLeviCivitaSurface.remainingSelectedGRFirstMissing
        flatLeviCivitaSurface
      ≡
      Bianchi.missingFiniteRScalarAlgebra

    selectedFiniteLeviCivitaAdapter :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter

    selectedFiniteLeviCivitaAdapterStatus :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter.status
        selectedFiniteLeviCivitaAdapter
      ≡
      LeviCivita.selectedFourChartChristoffelLeviCivitaWitnessNoPromotion

    selectedFiniteLeviCivitaAdapterDischargesCarrierConnection :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter.missingCarrierConnectionIsLeviCivitaDischargedLocally
        selectedFiniteLeviCivitaAdapter
      ≡
      true

    selectedFiniteLeviCivitaAdapterNextResidual :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter.nextResidualAfterSelectedLeviCivita
        selectedFiniteLeviCivitaAdapter
      ≡
      Bianchi.missingCurvatureToRicciEinsteinContractionBoundary

    selectedFiniteLeviCivitaAdapterNoSchwarzschildPromotion :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter.unsupportedSchwarzschildContinuumPromotion
        selectedFiniteLeviCivitaAdapter
      ≡
      false

    selectedFiniteLeviCivitaAdapterNoTerminalPromotion :
      LeviCivita.GRConcreteSelectedLeviCivitaAdapter.unsupportedTerminalPromotion
        selectedFiniteLeviCivitaAdapter
      ≡
      false

    ricciCandidate :
      Ricci.GRDiscreteRicciCandidateFromCurvature

    ricciCandidateFirstMissing :
      Ricci.GRDiscreteRicciCandidateFromCurvature.firstMissing ricciCandidate
      ≡
      Ricci.missingBianchiIdentityProof

    ricciCandidateLocalFibreDecompositionAvailable :
      Ricci.GRDiscreteRicciCandidateFromCurvature.localFibreDecompositionAvailable
        ricciCandidate
      ≡
      true

    ricciCandidateNoGlobalEagerSweep :
      Ricci.GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
        ricciCandidate
      ≡
      false

    finiteRBianchiMissingIngredients :
      List Bianchi.GRDiscreteBianchiFiniteRMissingIngredient

    finiteRBianchiMissingIngredientsAreCanonical :
      finiteRBianchiMissingIngredients
      ≡
      Bianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients

    schwarzschildLimitCandidate :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic

    schwarzschildLimitStatusIsRequestOnly :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.status
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.requestSurfaceOnlyNoPromotion

    schwarzschildLimitFirstMissing :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.firstMissing
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.missingRadialValuation

    schwarzschildCanonicalCandidateReceipt :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt

    schwarzschildCanonicalFullLimitNotPromoted :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.fullSchwarzschildLimitPromoted
        schwarzschildCanonicalCandidateReceipt
      ≡
      false

    finiteRScalarCarrierWitness :
      Scalar.GRConcreteFiniteRScalarAlgebraAndCarrierWitness

    finiteRScalarCarrierWitnessStillOpen :
      Scalar.GRConcreteFiniteRScalarAlgebraAndCarrierWitness.selectedGRScalarAlgebraDischarged
        finiteRScalarCarrierWitness
      ≡
      false

    finiteRBaseDerivationBracketConnectionStaging :
      Scalar.GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt

    finiteRBaseDerivationFirstMetricInterface :
      Scalar.GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt.firstUndischargedSelectedMetricInterface
        finiteRBaseDerivationBracketConnectionStaging
      ≡
      "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"

    finiteRUnitMetricAlgebraStaging :
      Scalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt

    finiteRUnitMetricAlgebraTrace :
      Scalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.traceOfUnitMetric
        finiteRUnitMetricAlgebraStaging
      ≡
      Scalar.r0

    finiteRUnitMetricAlgebraNoNonFlatLeviCivitaPromotion :
      Scalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesNonFlatLeviCivita
        finiteRUnitMetricAlgebraStaging
      ≡
      false

    finiteRUnitMetricAlgebraNoGRPromotion :
      Scalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesGR
        finiteRUnitMetricAlgebraStaging
      ≡
      false

    selectedNonFlatScalarAlgebraObligation :
      Scalar.GRSelectedNonFlatScalarAlgebraObligationReceipt

    selectedNonFlatScalarAlgebraFirstMissing :
      Scalar.GRSelectedNonFlatScalarAlgebraObligationReceipt.firstMissingInterface
        selectedNonFlatScalarAlgebraObligation
      ≡
      "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"

    inverseMetricC0DerivativeConsistencyReceipt :
      Scalar.GRInverseMetricC0DerivativeConsistencyReceipt

    inverseMetricC0ControlClosed :
      Scalar.GRInverseMetricC0DerivativeConsistencyReceipt.missingInverseMetricC0ControlClosed
        inverseMetricC0DerivativeConsistencyReceipt
      ≡
      true

    finiteCarrierMetricDerivativeConsistencyClosed :
      Scalar.GRInverseMetricC0DerivativeConsistencyReceipt.finiteCarrierMetricDerivativeConsistencyClosed
        inverseMetricC0DerivativeConsistencyReceipt
      ≡
      true

    inverseMetricC0DerivativeNoAnalyticQQPromotion :
      Scalar.GRInverseMetricC0DerivativeConsistencyReceipt.promotesAnalyticQQOrderLipschitzTheorem
        inverseMetricC0DerivativeConsistencyReceipt
      ≡
      false

    inverseMetricC0DerivativeNoNonFlatGRPromotion :
      Scalar.GRInverseMetricC0DerivativeConsistencyReceipt.promotesNonFlatGRSolution
        inverseMetricC0DerivativeConsistencyReceipt
      ≡
      false

    discreteEinsteinTensorDiagnostic :
      EinsteinTensor.DiscreteEinsteinTensorCandidateDiagnostic

    discreteEinsteinTensorFirstMissing :
      EinsteinTensor.DiscreteEinsteinTensorCandidateDiagnostic.firstMissing
        discreteEinsteinTensorDiagnostic
      ≡
      EinsteinTensor.missingCarrierInternalNonFlatConnectionFromCRT

    factorVecSSPConstructionRequest :
      EinsteinTensor.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface

    factorVecSSPConstructionBasePointIsFactorVec :
      EinsteinTensor.DiscreteEinsteinTensorConstructionRequestSurface.BasePoint
        (EinsteinTensor.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface.constructionRequest
          factorVecSSPConstructionRequest)
      ≡
      GL.FactorVec

    factorVecSSPConstructionCoordinateIndexIsSSP :
      EinsteinTensor.DiscreteEinsteinTensorConstructionRequestSurface.CoordinateIndex
        (EinsteinTensor.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface.constructionRequest
          factorVecSSPConstructionRequest)
      ≡
      MO.SSP

    factorVecSSPAllLaneContractionEinsteinTensorLaw :
      EinsteinTensor.FactorVecSSPAllLaneContractionEinsteinTensorLaw

    factorVecSSPNonFlatConnectionWitnessRequest :
      EinsteinTensor.FactorVecSSPNonFlatConnectionWitnessRequest

    factorVecSSPNonFlatConnectionFirstMissing :
      EinsteinTensor.FactorVecSSPNonFlatConnectionWitnessRequest.firstMissingField
        factorVecSSPNonFlatConnectionWitnessRequest
      ≡
      EinsteinTensor.missingFactorVecSSPConnectionCoefficientsDifferFromZero

    crtConnectionCandidate :
      CRTConnection.DiscreteConnectionCandidateFromCRT

    crtConnectionCandidateStatus :
      CRTConnection.DiscreteConnectionCandidateFromCRT.status
        crtConnectionCandidate
      ≡
      CRTConnection.typedCRTConnectionCandidateNoEinsteinPromotion

    crtConnectionCandidateFirstMissing :
      CRTConnection.DiscreteConnectionCandidateFromCRT.firstMissingAfterConnectionCandidate
        crtConnectionCandidate
      ≡
      EinsteinTensor.missingCurvatureToRicciContraction

    crtConnectionDiagnostic :
      CRTConnection.DiscreteConnectionCandidateFromCRTDiagnostic

    crtConnectionDiagnosticFirstMissing :
      CRTConnection.DiscreteConnectionCandidateFromCRTDiagnostic.firstMissing
        crtConnectionDiagnostic
      ≡
      EinsteinTensor.missingCarrierInternalNonFlatConnectionFromCRT

    einsteinEquationObligation :
      EinsteinEquation.EinsteinEquationCandidateObligationSurface

    einsteinEquationStatus :
      EinsteinEquation.EinsteinEquationCandidateObligationSurface.status
        einsteinEquationObligation
      ≡
      EinsteinEquation.flatVacuumCorrectW4MatterCouplingNeeded

    einsteinEquationFirstMissing :
      EinsteinEquation.EinsteinEquationCandidateObligationSurface.firstMissing
        einsteinEquationObligation
      ≡
      EinsteinEquation.missingW4MatterCouplingReceipt

    w4MatterStressEnergyDiagnostic :
      EinsteinEquation.W4MatterStressEnergyInterfaceDiagnostic

    w4MatterStressEnergyFirstMissing :
      EinsteinEquation.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
        w4MatterStressEnergyDiagnostic
      ≡
      EinsteinEquation.missingW4AnchorArtifactReceiptForMatterStress

    downstreamRicciConvergenceReadiness :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt

    downstreamRicciZeroTableReady :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.zeroTableArithmeticReadyForTier3
        downstreamRicciConvergenceReadiness
      ≡
      true

    downstreamRicciConvergesC0NotPromoted :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.ricciConvergesC0Promoted
        downstreamRicciConvergenceReadiness
      ≡
      false

    downstreamRicciContractedBianchiNotPromoted :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.contractedBianchiPromoted
        downstreamRicciConvergenceReadiness
      ≡
      false

    downstreamRicciSourcedEinsteinNotPromoted :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.sourcedEinsteinPromoted
        downstreamRicciConvergenceReadiness
      ≡
      false

    downstreamRicciGRPromotionNotClaimed :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.grPromotionClaimed
        downstreamRicciConvergenceReadiness
      ≡
      false

    downstreamRicciFirstBlocker :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.firstDownstreamBlocker
        downstreamRicciConvergenceReadiness
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    selectedRationalUndoubledChristoffelLift :
      Bianchi.GRSelectedRationalUndoubledChristoffelLift
        Bianchi.canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput

    selectedRationalHalfWitnessIsCanonical :
      Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitness
        selectedRationalUndoubledChristoffelLift
      ≡
      Bianchi.qqHalf

    selectedRationalHalfWitnessDoublesToOne :
      Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessDoublesToOne
        selectedRationalUndoubledChristoffelLift
      ≡
      Bianchi.qqHalfDoubleIsOne

    upper6U3SelectedLeviCivitaTorsionFreeUniqueness :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt

    upper6U3RationalDivisionByTwoAvailable :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalDivisionByTwoAdapterAvailable
        upper6U3SelectedLeviCivitaTorsionFreeUniqueness
      ≡
      true

    upper6U3RationalDivisionByTwoNotRemainingBlocker :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalDivisionByTwoIsNotRemainingBlocker
        upper6U3SelectedLeviCivitaTorsionFreeUniqueness
      ≡
      true

    upper6U3SelectedChristoffelFromMetricLawNotSupplied :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedChristoffelFromMetricLawSupplied
        upper6U3SelectedLeviCivitaTorsionFreeUniqueness
      ≡
      false

    upper6U3SelectedCarrierConnectionLeviCivitaNotPromoted :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        upper6U3SelectedLeviCivitaTorsionFreeUniqueness
      ≡
      false

    upper6U3ExactFirstSelectedNonFlatBlocker :
      Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.exactFirstSelectedNonFlatBlocker
        upper6U3SelectedLeviCivitaTorsionFreeUniqueness
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    m3FourRTwoGEinsteinFiniteArithmetic :
      Bianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt

    m3FourRTwoGEinsteinNoPromotion :
      Bianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciEinsteinTowerPromoted
        m3FourRTwoGEinsteinFiniteArithmetic
      ≡
      false

    m3FourRTwoGEinsteinFirstBlocker :
      Bianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.exactFirstSelectedNonFlatBlocker
        m3FourRTwoGEinsteinFiniteArithmetic
      ≡
      Bianchi.missingMetricCompatibility

    gate4TowerSchemaInstance :
      Gate4.GRGate4TowerSchemaInstance

    gate4TowerGRPromotedFalse :
      Gate4.GRGate4TowerSchemaInstance.gate4GRPromoted
        gate4TowerSchemaInstance
      ≡
      false

    gate4TowerCosmologyPromotedFalse :
      Gate4.GRGate4TowerSchemaInstance.cosmologyPromoted
        gate4TowerSchemaInstance
      ≡
      false

    continuumLimitCandidate :
      Continuum.ContinuumLimitTheoremCandidate

    continuumLimitStatusIsRequestOnly :
      Continuum.ContinuumLimitTheoremCandidate.status
        continuumLimitCandidate
      ≡
      Continuum.theoremRequestOnlyW2RateBlockedNoPromotion

    continuumLimitW2Role :
      Continuum.ContinuumLimitTheoremCandidate.w2ResolutionRole
        continuumLimitCandidate
      ≡
      Continuum.w2ResolutionAffectsRateNotExistence

    machineCheckedChristoffelC0Constants :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt

    machineCheckedChristoffelL_Gamma48 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        machineCheckedChristoffelC0Constants
      ≡
      48

    machineCheckedRicciContractionConstant640 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
        machineCheckedChristoffelC0Constants
      ≡
      640

    machineCheckedShell_C_Gamma2 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
        machineCheckedChristoffelC0Constants
      ≡
      2

    machineCheckedInverseMetricC0Shape :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.inverseMetricC0Shape
        machineCheckedChristoffelC0Constants
      ≡
      Continuum.inverseMetricC0PointwiseFiniteCarrierShape

    machineCheckedNoExternalAnalyticAuthorityFabricated :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.noExternalAnalyticAuthorityFabricated
        machineCheckedChristoffelC0Constants
      ≡
      false

    unsafeExternalSurfaceReceipts :
      List String

    unsafeExternalSurfaceReceiptsAreCanonicalCurrentBlockers :
      unsafeExternalSurfaceReceipts
      ≡
      []

    aggregationBoundary :
      List String

canonicalGRProofArchitectureAggregationTest :
  GRProofArchitectureAggregationTest
canonicalGRProofArchitectureAggregationTest =
  record
    { status =
        checkedAggregationOnlyNoPromotion
    ; flatLeviCivitaSurface =
        LeviCivita.canonicalGRConcreteLeviCivitaSurface
    ; flatLeviCivitaResidual =
        LeviCivita.grConcreteLeviCivitaResidualIsNonFlat
    ; flatLeviCivitaFirstMissing =
        LeviCivita.grConcreteLeviCivitaFirstMissingIsFiniteRScalarAlgebra
    ; selectedFiniteLeviCivitaAdapter =
        LeviCivita.canonicalGRConcreteSelectedLeviCivitaAdapter
    ; selectedFiniteLeviCivitaAdapterStatus =
        refl
    ; selectedFiniteLeviCivitaAdapterDischargesCarrierConnection =
        LeviCivita.grConcreteSelectedLeviCivitaAdapterClosesCarrierConnection
    ; selectedFiniteLeviCivitaAdapterNextResidual =
        LeviCivita.grConcreteSelectedLeviCivitaAdapterNextResidual
    ; selectedFiniteLeviCivitaAdapterNoSchwarzschildPromotion =
        LeviCivita.grConcreteSelectedLeviCivitaAdapterNoSchwarzschildPromotion
    ; selectedFiniteLeviCivitaAdapterNoTerminalPromotion =
        LeviCivita.GRConcreteSelectedLeviCivitaAdapter.unsupportedTerminalPromotionIsFalse
          LeviCivita.canonicalGRConcreteSelectedLeviCivitaAdapter
    ; ricciCandidate =
        Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; ricciCandidateFirstMissing =
        Ricci.grDiscreteRicciCandidateFirstMissing
    ; ricciCandidateLocalFibreDecompositionAvailable =
        Ricci.grDiscreteRicciCandidateLocalFibreDecompositionAvailable
    ; ricciCandidateNoGlobalEagerSweep =
        Ricci.grDiscreteRicciCandidateNoGlobalEagerRicciSweep
    ; finiteRBianchiMissingIngredients =
        Bianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; finiteRBianchiMissingIngredientsAreCanonical =
        refl
    ; schwarzschildLimitCandidate =
        Schwarzschild.canonicalSchwarzschildLimitCandidateDiagnostic
    ; schwarzschildLimitStatusIsRequestOnly =
        Schwarzschild.schwarzschildLimitStatusIsRequestOnly
    ; schwarzschildLimitFirstMissing =
        Schwarzschild.schwarzschildLimitExactFirstMissing
    ; schwarzschildCanonicalCandidateReceipt =
        Schwarzschild.canonicalSchwarzschildLimitCanonicalCandidateReceipt
    ; schwarzschildCanonicalFullLimitNotPromoted =
        Schwarzschild.schwarzschildCanonicalFullLimitNotPromoted
    ; finiteRScalarCarrierWitness =
        Scalar.canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
    ; finiteRScalarCarrierWitnessStillOpen =
        Scalar.grConcreteFiniteRScalarWitnessStillNotDischarged
    ; finiteRBaseDerivationBracketConnectionStaging =
        Scalar.canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt
    ; finiteRBaseDerivationFirstMetricInterface =
        Scalar.grConcreteFiniteRBaseDerivationBracketConnectionStagingFirstMetricInterface
    ; finiteRUnitMetricAlgebraStaging =
        Scalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; finiteRUnitMetricAlgebraTrace =
        Scalar.grConcreteFiniteRUnitMetricAlgebraTrace
    ; finiteRUnitMetricAlgebraNoNonFlatLeviCivitaPromotion =
        refl
    ; finiteRUnitMetricAlgebraNoGRPromotion =
        Scalar.grConcreteFiniteRUnitMetricAlgebraNoGRPromotion
    ; selectedNonFlatScalarAlgebraObligation =
        Scalar.canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
    ; selectedNonFlatScalarAlgebraFirstMissing =
        Scalar.selectedNonFlatScalarAlgebraReceiptFirstMissing
    ; inverseMetricC0DerivativeConsistencyReceipt =
        Scalar.canonicalGRInverseMetricC0DerivativeConsistencyReceipt
    ; inverseMetricC0ControlClosed =
        Scalar.missingInverseMetricC0ControlNowClosed
    ; finiteCarrierMetricDerivativeConsistencyClosed =
        Scalar.grFiniteCarrierMetricDerivativeConsistencyNowClosed
    ; inverseMetricC0DerivativeNoAnalyticQQPromotion =
        Scalar.GRInverseMetricC0DerivativeConsistencyReceipt.promotesAnalyticQQOrderLipschitzTheoremIsFalse
          Scalar.canonicalGRInverseMetricC0DerivativeConsistencyReceipt
    ; inverseMetricC0DerivativeNoNonFlatGRPromotion =
        Scalar.grInverseMetricC0DerivativeConsistencyNoNonFlatGRPromotion
    ; discreteEinsteinTensorDiagnostic =
        EinsteinTensor.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; discreteEinsteinTensorFirstMissing =
        refl
    ; factorVecSSPConstructionRequest =
        EinsteinTensor.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface
    ; factorVecSSPConstructionBasePointIsFactorVec =
        EinsteinTensor.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface.basePointIsFactorVec
          EinsteinTensor.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface
    ; factorVecSSPConstructionCoordinateIndexIsSSP =
        EinsteinTensor.FactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface.coordinateIndexIsSSP
          EinsteinTensor.canonicalFactorVecSSPDiscreteEinsteinTensorConstructionRequestSurface
    ; factorVecSSPAllLaneContractionEinsteinTensorLaw =
        EinsteinTensor.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw
    ; factorVecSSPNonFlatConnectionWitnessRequest =
        EinsteinTensor.canonicalFactorVecSSPNonFlatConnectionWitnessRequest
    ; factorVecSSPNonFlatConnectionFirstMissing =
        EinsteinTensor.factorVecSSPNonFlatConnectionWitnessRequestExactFirstMissing
    ; crtConnectionCandidate =
        CRTConnection.canonicalDiscreteConnectionCandidateFromCRT
    ; crtConnectionCandidateStatus =
        CRTConnection.discreteConnectionCandidateFromCRTStatusIsTypedCandidate
    ; crtConnectionCandidateFirstMissing =
        CRTConnection.discreteConnectionCandidateFromCRTFirstMissingIsRicci
    ; crtConnectionDiagnostic =
        CRTConnection.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; crtConnectionDiagnosticFirstMissing =
        CRTConnection.discreteConnectionFromCRTExactFirstMissing
    ; einsteinEquationObligation =
        EinsteinEquation.canonicalEinsteinEquationCandidateObligationSurface
    ; einsteinEquationStatus =
        EinsteinEquation.einsteinEquationCandidateStatusIsObligationOnly
    ; einsteinEquationFirstMissing =
        EinsteinEquation.einsteinEquationCandidateExactFirstMissing
    ; w4MatterStressEnergyDiagnostic =
        EinsteinEquation.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; w4MatterStressEnergyFirstMissing =
        EinsteinEquation.w4MatterStressEnergyInterfaceExactFirstMissing
    ; downstreamRicciConvergenceReadiness =
        Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciZeroTableReady =
        Ricci.grDiscreteRicciDownstreamZeroTableReady
    ; downstreamRicciConvergesC0NotPromoted =
        Ricci.grDiscreteRicciDownstreamRicciConvergesC0NotPromoted
    ; downstreamRicciContractedBianchiNotPromoted =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.contractedBianchiPromotedIsFalse
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciSourcedEinsteinNotPromoted =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.sourcedEinsteinPromotedIsFalse
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciGRPromotionNotClaimed =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.grPromotionClaimedIsFalse
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciFirstBlocker =
        Ricci.grDiscreteRicciDownstreamFirstBlocker
    ; selectedRationalUndoubledChristoffelLift =
        Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedRationalHalfWitnessIsCanonical =
        Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessIsCanonical
          Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedRationalHalfWitnessDoublesToOne =
        refl
    ; upper6U3SelectedLeviCivitaTorsionFreeUniqueness =
        Bianchi.canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; upper6U3RationalDivisionByTwoAvailable =
        Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalDivisionByTwoAdapterAvailableIsTrue
          Bianchi.canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; upper6U3RationalDivisionByTwoNotRemainingBlocker =
        Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalDivisionByTwoIsNotRemainingBlockerIsTrue
          Bianchi.canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; upper6U3SelectedChristoffelFromMetricLawNotSupplied =
        Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedChristoffelFromMetricLawSuppliedIsFalse
          Bianchi.canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; upper6U3SelectedCarrierConnectionLeviCivitaNotPromoted =
        Bianchi.grUpper6U3SelectedLeviCivitaStillBlocked
    ; upper6U3ExactFirstSelectedNonFlatBlocker =
        Bianchi.GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita
          Bianchi.canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; m3FourRTwoGEinsteinFiniteArithmetic =
        Bianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; m3FourRTwoGEinsteinNoPromotion =
        Bianchi.grM3FourRTwoGEinsteinNoPromotion
    ; m3FourRTwoGEinsteinFirstBlocker =
        Bianchi.grM3FourRTwoGEinsteinReceiptStillBlocked
    ; gate4TowerSchemaInstance =
        Gate4.canonicalGRGate4TowerSchemaInstance
    ; gate4TowerGRPromotedFalse =
        Gate4.grGate4TowerSchemaGRPromotionFalse
    ; gate4TowerCosmologyPromotedFalse =
        Gate4.grGate4TowerSchemaCosmologyPromotionFalse
    ; continuumLimitCandidate =
        Continuum.canonicalContinuumLimitTheoremCandidate
    ; continuumLimitStatusIsRequestOnly =
        Continuum.continuumLimitCandidateExactStatus
    ; continuumLimitW2Role =
        Continuum.continuumLimitCandidateW2Role
    ; machineCheckedChristoffelC0Constants =
        Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedChristoffelL_Gamma48 =
        Continuum.machineCheckedChristoffelL_GammaIs48
    ; machineCheckedRicciContractionConstant640 =
        Continuum.machineCheckedRicciContractionExtractionConstantIs640
    ; machineCheckedShell_C_Gamma2 =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.shell_C_GammaIs2
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedInverseMetricC0Shape =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.inverseMetricC0ShapeIsPointwiseFiniteCarrier
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedNoExternalAnalyticAuthorityFabricated =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.noExternalAnalyticAuthorityFabricatedIsFalse
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; unsafeExternalSurfaceReceipts =
        []
    ; unsafeExternalSurfaceReceiptsAreCanonicalCurrentBlockers =
        refl
    ; aggregationBoundary =
        "Imports and checks the flat Levi-Civita prerequisite surface"
        ∷ "Imports and checks the selected finite Levi-Civita adapter discharge surface"
        ∷ "Imports and checks the Ricci candidate local-fibre staging surface"
        ∷ "Imports and checks the inverse-metric C0 and metric-derivative consistency closure"
        ∷ "Imports and checks the finite-r scalar/carrier and unit-metric algebra staging surfaces"
        ∷ "Imports and checks the FactorVec/SSP all-lane Einstein-tensor construction request"
        ∷ "Imports and checks the CRT monodromy connection candidate and its Ricci first-missing boundary"
        ∷ "Imports and checks the finite-r Bianchi missing-ingredient index"
        ∷ "Imports and checks the Einstein-equation W4 matter-coupling obligation surface"
        ∷ "Imports and checks the downstream Ricci convergence readiness surface"
        ∷ "Imports and checks the rational undoubled Christoffel lift and its remaining selected metric-law blocker"
        ∷ "Imports and checks the finite 4R/Ricci/scalar/2G arithmetic receipt without GR promotion"
        ∷ "Imports and checks the Gate 4 GR/cosmology schema instance as fail-closed"
        ∷ "Imports and checks the strengthened Schwarzschild request and canonical fail-closed gate receipt"
        ∷ "Imports and checks the continuum theorem-request surface"
        ∷ "Imports and checks the Continuum machine-checked Christoffel C0 constants"
        ∷ "No GR, Schwarzschild, Bianchi, or Einstein-equation promotion is introduced here"
        ∷ []
    }

grProofArchitectureAggregationStatus :
  GRProofArchitectureAggregationTest.status
    canonicalGRProofArchitectureAggregationTest
  ≡
  checkedAggregationOnlyNoPromotion
grProofArchitectureAggregationStatus = refl

grProofArchitectureAggregationRicciFirstMissing :
  GRProofArchitectureAggregationTest.ricciCandidateFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciCandidateFirstMissing
grProofArchitectureAggregationRicciFirstMissing = refl

grProofArchitectureAggregationSelectedFiniteLeviCivitaAdapterNextResidual :
  GRProofArchitectureAggregationTest.selectedFiniteLeviCivitaAdapterNextResidual
    canonicalGRProofArchitectureAggregationTest
  ≡
  LeviCivita.grConcreteSelectedLeviCivitaAdapterNextResidual
grProofArchitectureAggregationSelectedFiniteLeviCivitaAdapterNextResidual = refl

grProofArchitectureAggregationInverseMetricC0ControlClosed :
  GRProofArchitectureAggregationTest.inverseMetricC0ControlClosed
    canonicalGRProofArchitectureAggregationTest
  ≡
  Scalar.missingInverseMetricC0ControlNowClosed
grProofArchitectureAggregationInverseMetricC0ControlClosed = refl

grProofArchitectureAggregationSchwarzschildFullLimitNotPromoted :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalFullLimitNotPromoted
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildCanonicalFullLimitNotPromoted
grProofArchitectureAggregationSchwarzschildFullLimitNotPromoted = refl

grProofArchitectureAggregationFiniteRUnitMetricNoGRPromotion :
  GRProofArchitectureAggregationTest.finiteRUnitMetricAlgebraNoGRPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Scalar.grConcreteFiniteRUnitMetricAlgebraNoGRPromotion
grProofArchitectureAggregationFiniteRUnitMetricNoGRPromotion = refl

grProofArchitectureAggregationCRTConnectionFirstMissing :
  GRProofArchitectureAggregationTest.crtConnectionCandidateFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  CRTConnection.discreteConnectionCandidateFromCRTFirstMissingIsRicci
grProofArchitectureAggregationCRTConnectionFirstMissing = refl

grProofArchitectureAggregationEinsteinEquationFirstMissing :
  GRProofArchitectureAggregationTest.einsteinEquationFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  EinsteinEquation.einsteinEquationCandidateExactFirstMissing
grProofArchitectureAggregationEinsteinEquationFirstMissing = refl

grProofArchitectureAggregationDownstreamRicciFirstBlocker :
  GRProofArchitectureAggregationTest.downstreamRicciFirstBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciDownstreamFirstBlocker
grProofArchitectureAggregationDownstreamRicciFirstBlocker = refl

grProofArchitectureAggregationRationalHalfWitness :
  GRProofArchitectureAggregationTest.selectedRationalHalfWitnessIsCanonical
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessIsCanonical
    Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
grProofArchitectureAggregationRationalHalfWitness = refl

grProofArchitectureAggregationUpper6U3StillBlocked :
  GRProofArchitectureAggregationTest.upper6U3SelectedCarrierConnectionLeviCivitaNotPromoted
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.grUpper6U3SelectedLeviCivitaStillBlocked
grProofArchitectureAggregationUpper6U3StillBlocked = refl

grProofArchitectureAggregationM3FourRTwoGEinsteinNoPromotion :
  GRProofArchitectureAggregationTest.m3FourRTwoGEinsteinNoPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.grM3FourRTwoGEinsteinNoPromotion
grProofArchitectureAggregationM3FourRTwoGEinsteinNoPromotion = refl

grProofArchitectureAggregationGate4GRPromotionFalse :
  GRProofArchitectureAggregationTest.gate4TowerGRPromotedFalse
    canonicalGRProofArchitectureAggregationTest
  ≡
  Gate4.grGate4TowerSchemaGRPromotionFalse
grProofArchitectureAggregationGate4GRPromotionFalse = refl

grProofArchitectureAggregationContinuumLimitStatus :
  GRProofArchitectureAggregationTest.continuumLimitStatusIsRequestOnly
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.continuumLimitCandidateExactStatus
grProofArchitectureAggregationContinuumLimitStatus = refl

grProofArchitectureAggregationMachineCheckedChristoffelL_Gamma48 :
  GRProofArchitectureAggregationTest.machineCheckedChristoffelL_Gamma48
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.machineCheckedChristoffelL_GammaIs48
grProofArchitectureAggregationMachineCheckedChristoffelL_Gamma48 = refl

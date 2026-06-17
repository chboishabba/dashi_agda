module DASHI.Physics.Closure.GRProofArchitectureAggregationTest where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_≤_)

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
import DASHI.Core.Q as Q
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

record GRProofArchitectureNextAnalyticKernelTrancheReceipt : Setω where
  field
    status :
      GRProofArchitectureAggregationStatus

    gaugeToolkitTierName :
      String

    gaugeToolkitTierNameIsCanonical :
      gaugeToolkitTierName
      ≡
      "tier 1: ordered rational gauge toolkit"

    gaugeToolkitTargetFile :
      String

    gaugeToolkitTargetFileIsCanonical :
      gaugeToolkitTargetFile
      ≡
      "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"

    gaugeToolkitTargetVars :
      List String

    gaugeToolkitTargetVarsAreCanonical :
      gaugeToolkitTargetVars
      ≡
      "canonicalOrderedRationalGaugeToolkitReceipt"
      ∷ "orderedRationalGaugeD_QQZeroLawPrimitive"
      ∷ "orderedRationalGaugeD_QQSymmetryLawPrimitive"
      ∷ "orderedRationalGaugeD_QQTriangleLawPrimitive"
      ∷ "orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive"
      ∷ "orderedRationalGaugeThreeMinusNPositiveLawPrimitive"
      ∷ "orderedRationalGaugeScale48Is48"
      ∷ "orderedRationalGaugeScale48NonnegativeLawPrimitive"
      ∷ []

    shellADenominatorTierName :
      String

    shellADenominatorTierNameIsCanonical :
      shellADenominatorTierName
      ≡
      "tier 2: Shell A denominator chain"

    shellADenominatorTargetFile :
      String

    shellADenominatorTargetFileIsCanonical :
      shellADenominatorTargetFile
      ≡
      "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"

    shellADenominatorTargetVars :
      List String

    shellADenominatorTargetVarsAreCanonical :
      shellADenominatorTargetVars
      ≡
      "canonicalOrderedRationalShellADenominatorReciprocalReceipt"
      ∷ "orderedRationalShellARadialMinusSchwarzschildLowerBoundIs1"
      ∷ "orderedRationalShellAInverseMetricAbsMaxIs4"
      ∷ "orderedRationalShellAMetricDerivativeAbsMaxIs8"
      ∷ "orderedRationalShellAChristoffelFormulaEnvelopeIs72"
      ∷ "orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable"
      ∷ []

    christoffelDerivativeBoundsTierName :
      String

    christoffelDerivativeBoundsTierNameIsCanonical :
      christoffelDerivativeBoundsTierName
      ≡
      "tier 3: Christoffel derivative bounds"

    christoffelDerivativeBoundsTargetFile :
      String

    christoffelDerivativeBoundsTargetFileIsCanonical :
      christoffelDerivativeBoundsTargetFile
      ≡
      "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"

    christoffelDerivativeBoundsTargetVars :
      List String

    christoffelDerivativeBoundsTargetVarsAreCanonical :
      christoffelDerivativeBoundsTargetVars
      ≡
      "canonicalOrderedRationalShellAChristoffelC0ConstantReceipt"
      ∷ "orderedRationalShellA_C_GammaIs1"
      ∷ "orderedRationalShellA_CPrime_GammaNumeratorIs26"
      ∷ "orderedRationalShellA_CPrime_GammaDenominatorIs27"
      ∷ "orderedRationalShellARequestedInequalityPrimitive"
      ∷ "canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt"
      ∷ []

    christoffelC0StabilityTierName :
      String

    christoffelC0StabilityTierNameIsCanonical :
      christoffelC0StabilityTierName
      ≡
      "tier 4: Christoffel C0 stability"

    christoffelC0StabilityTargetFile :
      String

    christoffelC0StabilityTargetFileIsCanonical :
      christoffelC0StabilityTargetFile
      ≡
      "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"

    christoffelC0StabilityTargetVars :
      List String

    christoffelC0StabilityTargetVarsAreCanonical :
      christoffelC0StabilityTargetVars
      ≡
      "canonicalMachineCheckedChristoffelC0ConstantReceipt"
      ∷ "machineCheckedChristoffelL_GammaIs48"
      ∷ "canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt"
      ∷ "selectedSymbolicRationalChristoffelC0FormulaStabilityIs48"
      ∷ "canonicalSelectedSymbolicRationalChristoffelC0Primitive"
      ∷ "selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound"
      ∷ []

    ricciPerturbationExtractionTierName :
      String

    ricciPerturbationExtractionTierNameIsCanonical :
      ricciPerturbationExtractionTierName
      ≡
      "tier 5: Ricci perturbation extraction"

    ricciPerturbationExtractionTargetFile :
      String

    ricciPerturbationExtractionTargetFileIsCanonical :
      ricciPerturbationExtractionTargetFile
      ≡
      "DASHI/Physics/Closure/GRDiscreteRicciCandidateFromCurvature.agda"

    ricciPerturbationExtractionTargetVars :
      List String

    ricciPerturbationExtractionTargetVarsAreCanonical :
      ricciPerturbationExtractionTargetVars
      ≡
      "canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt"
      ∷ "grDiscreteRicciExtractionConnectionErrorBoundExtractionDependencyNameExact"
      ∷ "grDiscreteRicciExtractionPointCRConstantIs48"
      ∷ "grDiscreteRicciExtractionShellACRConstantIs80"
      ∷ "grDiscreteRicciExtractionConservativeCRExtractionConstantIs640"
      ∷ "canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt"
      ∷ "grSchwarzschildFiniteRicciPerturbationPointCRConstantIs48"
      ∷ "grSchwarzschildFiniteRicciPerturbationConservativeCRConstantIs640"
      ∷ []

    currentGRAnalyticKernelRemainingVars :
      List String

    currentGRAnalyticKernelRemainingVarsAreCanonical :
      currentGRAnalyticKernelRemainingVars
      ≡
      "nextAnalyticKernelShellA_LGammaIs72"
      ∷ "nextAnalyticKernelShellA_CRIs80"
      ∷ "nextAnalyticKernelShellA_CPrimeDenominatorIs27"
      ∷ "nextAnalyticKernelSchwarzschildShellAEnvelope640"
      ∷ "nextAnalyticKernelRicciPerturbationBound640"
      ∷ []

    nsGW1DegeneracyStatusContext :
      String

    nsGW1DegeneracyStatusContextIsCanonical :
      nsGW1DegeneracyStatusContext
      ≡
      "NS-GW-1 degeneracy status is settled here only as non-promoting context: numeric evidence lane only; DNS confirmation and DNS sign classification remain outside this GR analytic-kernel tranche."

    nsGW1DegeneracyStatusNonPromoting :
      Bool

    nsGW1DegeneracyStatusNonPromotingIsTrue :
      nsGW1DegeneracyStatusNonPromoting
      ≡
      true

    nsGW1DegeneracyDoesNotPromoteGRKernel :
      Bool

    nsGW1DegeneracyDoesNotPromoteGRKernelIsTrue :
      nsGW1DegeneracyDoesNotPromoteGRKernel
      ≡
      true

    machineCheckedChristoffelC0Constants :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt

    machineCheckedChristoffelC0ConstantsAreCanonical :
      machineCheckedChristoffelC0Constants
      ≡
      Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt

    finalShellA_LGammaIs48 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        machineCheckedChristoffelC0Constants
      ≡
      48

    finalShellA_RicciExtractionConstantIs640 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
        machineCheckedChristoffelC0Constants
      ≡
      640

    finalShellA_ConservativeCGammaUsed :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.conservativeShellCGammaUsed
        machineCheckedChristoffelC0Constants
      ≡
      true

    correctedTightShellA_LGamma :
      Nat

    correctedTightShellA_LGammaIs44 :
      correctedTightShellA_LGamma
      ≡
      44

    correctedTightShellA_LGammaDocumentationOnly :
      Bool

    correctedTightShellA_LGammaDocumentationOnlyIsTrue :
      correctedTightShellA_LGammaDocumentationOnly
      ≡
      true

    correctedTightShellA_LGammaPreservesFinal48 :
      Bool

    correctedTightShellA_LGammaPreservesFinal48IsTrue :
      correctedTightShellA_LGammaPreservesFinal48
      ≡
      true

    correctedTightShellA_LGammaPreservesLegacy72 :
      Bool

    correctedTightShellA_LGammaPreservesLegacy72IsTrue :
      correctedTightShellA_LGammaPreservesLegacy72
      ≡
      true

    selectedChristoffelC0Constants :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedChristoffelC0ConstantsAreCanonical :
      selectedChristoffelC0Constants
      ≡
      Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedChristoffelC0FormulaStability48 :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
        selectedChristoffelC0Constants
      ≡
      48

    selectedChristoffelC0NoArbitraryConnectionEquality :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.noArbitraryConnectionEqualityClaimed
        selectedChristoffelC0Constants
      ≡
      true

    shellADenominatorReciprocal :
      Continuum.OrderedRationalShellADenominatorReciprocalReceipt

    shellADenominatorReciprocalIsCanonical :
      shellADenominatorReciprocal
      ≡
      Continuum.canonicalOrderedRationalShellADenominatorReciprocalReceipt

    shellADenominatorReciprocalFeedsC0Stability :
      Continuum.OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0Stable
        shellADenominatorReciprocal
      ≡
      true

    orderedGaugeToolkit :
      Continuum.OrderedRationalGaugeToolkitReceipt

    orderedGaugeToolkitIsCanonical :
      orderedGaugeToolkit
      ≡
      Continuum.canonicalOrderedRationalGaugeToolkitReceipt

    orderedGaugeScale48 :
      Continuum.OrderedRationalGaugeToolkitReceipt.scaleConstant48
        orderedGaugeToolkit
      ≡
      48

    orderedGaugeToolkitNotPromoted :
      Continuum.OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromoted
        orderedGaugeToolkit
      ≡
      false

    orderedShellAConstants :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      Continuum.canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellA_LGammaIs72 :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants
      ≡
      72

    orderedShellA_CRIs80 :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
        orderedShellAConstants
      ≡
      80

    orderedShellA_CGammaIs1 :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
        orderedShellAConstants
      ≡
      1

    orderedShellA_CPrimeNumeratorIs26 :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
        orderedShellAConstants
      ≡
      26

    orderedShellA_CPrimeDenominatorIs27 :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
        orderedShellAConstants
      ≡
      27

    orderedShellARequestedInequalityPrimitive :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
        orderedShellAConstants
      ≡
      Continuum.shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    orderedShellAQQTheoremNotPromoted :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.orderedQQTheoremPromoted
        orderedShellAConstants
      ≡
      false

    orderedShellAAnalyticEstimateNotPromoted :
      Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.analyticEstimatePromoted
        orderedShellAConstants
      ≡
      false

    orderedShellAPerturbationRoute :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteIsCanonical :
      orderedShellAPerturbationRoute
      ≡
      Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteL_GammaIs72 :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      72

    orderedShellAPerturbationRouteNotPromoted :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.fullOrderedQQEstimatePromoted
        orderedShellAPerturbationRoute
      ≡
      false

    schwarzschildShellAExactCalculation :
      Schwarzschild.SchwarzschildShellAExactCalculationReceipt

    schwarzschildShellAExactCalculationIsCanonical :
      schwarzschildShellAExactCalculation
      ≡
      Schwarzschild.canonicalSchwarzschildShellAExactCalculationReceipt

    schwarzschildShellAConservativeEnvelope640 :
      Schwarzschild.SchwarzschildShellAExactCalculationReceipt.conservativeEnvelope
        schwarzschildShellAExactCalculation
      ≡
      Schwarzschild.sixHundredFortyN

    schwarzschildShellANoContinuumRicciPromotion :
      Schwarzschild.SchwarzschildShellAExactCalculationReceipt.continuumRicciPromoted
        schwarzschildShellAExactCalculation
      ≡
      false

    ricciFinitePerturbationReceipt :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt

    ricciFinitePerturbationReceiptIsCanonical :
      Bool

    ricciFinitePerturbationReceiptIsCanonicalTrue :
      ricciFinitePerturbationReceiptIsCanonical
      ≡
      true

    ricciPerturbationBound640 :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBound
        ricciFinitePerturbationReceipt
      ≡
      640

    ricciPerturbationPointCRConstant48 :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.pointCRConstant
        ricciFinitePerturbationReceipt
      ≡
      48

    ricciPerturbationShellACRConstant80 :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.shellACRConstant
        ricciFinitePerturbationReceipt
      ≡
      80

    ricciPerturbationConservativeCRConstant640 :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.conservativeCRExtractionConstant
        ricciFinitePerturbationReceipt
      ≡
      640

    ricciPerturbationConnectionErrorExtractionDependency :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.connectionErrorBoundExtractionDependencyName
        ricciFinitePerturbationReceipt
      ≡
      "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel.connectionErrorBoundExtraction"

    ricciPerturbationNotConvergencePromotion :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.ricciPerturbationBoundPromotedAsConvergence
        ricciFinitePerturbationReceipt
      ≡
      false

    ricciExternalContinuumAuthorityNotClaimed :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.externalContinuumSchwarzschildAuthorityClaimed
        ricciFinitePerturbationReceipt
      ≡
      false

    kernelDependencyName :
      String

    kernelDependencyNameIsCanonical :
      kernelDependencyName
      ≡
      "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel"

    analyticKernelStillOpen :
      Bool

    analyticKernelStillOpenIsTrue :
      analyticKernelStillOpen
      ≡
      true

    kernelObstructionReceipt :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt

    kernelObstructionReceiptIsCanonical :
      kernelObstructionReceipt
      ≡
      Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt

    kernelObstructionGlobalKernelNotConstructed :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.globalKernelLocallyConstructed
        kernelObstructionReceipt
      ≡
      false

    kernelObstructionNoFinFourTensorLayer :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.concreteFinFourTensorLayerPresent
        kernelObstructionReceipt
      ≡
      false

    kernelObstructionNoComponentChristoffelFormula :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.componentChristoffelFormulaPresent
        kernelObstructionReceipt
      ≡
      false

    kernelObstructionNoRicciContractionLayer :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.ricciComponentContractionLayerPresent
        kernelObstructionReceipt
      ≡
      false

    kernelObstructionSchwarzschildRowsCanonical :
      Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.schwarzschildSevenSlotDerivativeBoundRows
        kernelObstructionReceipt
      ≡
      Schwarzschild.schwarzschildShellASevenSlotDerivativeBoundReceipts

    requiredAnalyticalProofs :
      List String

    requiredAnalyticalProofsAreCanonical :
      requiredAnalyticalProofs
      ≡
      "tier 1: ordered rational gauge toolkit in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalGaugeToolkitReceipt and orderedRationalGauge* projections"
      ∷ "tier 2: Shell A denominator chain in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalShellADenominatorReciprocalReceipt and orderedRationalShellA* projections"
      ∷ "tier 3: Christoffel derivative bounds in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalShellAChristoffelC0ConstantReceipt, C_Gamma=1, and C'_Gamma=26/27 projections"
      ∷ "corrected tight Shell A L_Gamma=44 is recorded as documentation-only aggregation metadata; final/conservative L_Gamma=48 and legacy 72 overbound projections are preserved"
      ∷ "tier 4: Christoffel C0 stability in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalMachineCheckedChristoffelC0ConstantReceipt and selectedSymbolicRationalChristoffelC0FormulaStabilityIs48"
      ∷ "tier 5: Ricci perturbation extraction in DASHI/Physics/Closure/GRDiscreteRicciCandidateFromCurvature.agda at canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt and canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt"
      ∷ "current GR analytic-kernel remaining variables are recorded explicitly as five non-promoting aggregation booleans; NS-GW-1 degeneracy context remains numeric-evidence-only and outside promotion"
      ∷ []

canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt :
  GRProofArchitectureNextAnalyticKernelTrancheReceipt
canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt =
  record
    { status =
        checkedAggregationOnlyNoPromotion
    ; gaugeToolkitTierName =
        "tier 1: ordered rational gauge toolkit"
    ; gaugeToolkitTierNameIsCanonical =
        refl
    ; gaugeToolkitTargetFile =
        "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"
    ; gaugeToolkitTargetFileIsCanonical =
        refl
    ; gaugeToolkitTargetVars =
        "canonicalOrderedRationalGaugeToolkitReceipt"
        ∷ "orderedRationalGaugeD_QQZeroLawPrimitive"
        ∷ "orderedRationalGaugeD_QQSymmetryLawPrimitive"
        ∷ "orderedRationalGaugeD_QQTriangleLawPrimitive"
        ∷ "orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive"
        ∷ "orderedRationalGaugeThreeMinusNPositiveLawPrimitive"
        ∷ "orderedRationalGaugeScale48Is48"
        ∷ "orderedRationalGaugeScale48NonnegativeLawPrimitive"
        ∷ []
    ; gaugeToolkitTargetVarsAreCanonical =
        refl
    ; shellADenominatorTierName =
        "tier 2: Shell A denominator chain"
    ; shellADenominatorTierNameIsCanonical =
        refl
    ; shellADenominatorTargetFile =
        "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"
    ; shellADenominatorTargetFileIsCanonical =
        refl
    ; shellADenominatorTargetVars =
        "canonicalOrderedRationalShellADenominatorReciprocalReceipt"
        ∷ "orderedRationalShellARadialMinusSchwarzschildLowerBoundIs1"
        ∷ "orderedRationalShellAInverseMetricAbsMaxIs4"
        ∷ "orderedRationalShellAMetricDerivativeAbsMaxIs8"
        ∷ "orderedRationalShellAChristoffelFormulaEnvelopeIs72"
        ∷ "orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable"
        ∷ []
    ; shellADenominatorTargetVarsAreCanonical =
        refl
    ; christoffelDerivativeBoundsTierName =
        "tier 3: Christoffel derivative bounds"
    ; christoffelDerivativeBoundsTierNameIsCanonical =
        refl
    ; christoffelDerivativeBoundsTargetFile =
        "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"
    ; christoffelDerivativeBoundsTargetFileIsCanonical =
        refl
    ; christoffelDerivativeBoundsTargetVars =
        "canonicalOrderedRationalShellAChristoffelC0ConstantReceipt"
        ∷ "orderedRationalShellA_C_GammaIs1"
        ∷ "orderedRationalShellA_CPrime_GammaNumeratorIs26"
        ∷ "orderedRationalShellA_CPrime_GammaDenominatorIs27"
        ∷ "orderedRationalShellARequestedInequalityPrimitive"
        ∷ "canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt"
        ∷ []
    ; christoffelDerivativeBoundsTargetVarsAreCanonical =
        refl
    ; christoffelC0StabilityTierName =
        "tier 4: Christoffel C0 stability"
    ; christoffelC0StabilityTierNameIsCanonical =
        refl
    ; christoffelC0StabilityTargetFile =
        "DASHI/Physics/Closure/ContinuumLimitTheorem.agda"
    ; christoffelC0StabilityTargetFileIsCanonical =
        refl
    ; christoffelC0StabilityTargetVars =
        "canonicalMachineCheckedChristoffelC0ConstantReceipt"
        ∷ "machineCheckedChristoffelL_GammaIs48"
        ∷ "canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt"
        ∷ "selectedSymbolicRationalChristoffelC0FormulaStabilityIs48"
        ∷ "canonicalSelectedSymbolicRationalChristoffelC0Primitive"
        ∷ "selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound"
        ∷ []
    ; christoffelC0StabilityTargetVarsAreCanonical =
        refl
    ; ricciPerturbationExtractionTierName =
        "tier 5: Ricci perturbation extraction"
    ; ricciPerturbationExtractionTierNameIsCanonical =
        refl
    ; ricciPerturbationExtractionTargetFile =
        "DASHI/Physics/Closure/GRDiscreteRicciCandidateFromCurvature.agda"
    ; ricciPerturbationExtractionTargetFileIsCanonical =
        refl
    ; ricciPerturbationExtractionTargetVars =
        "canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt"
        ∷ "grDiscreteRicciExtractionConnectionErrorBoundExtractionDependencyNameExact"
        ∷ "grDiscreteRicciExtractionPointCRConstantIs48"
        ∷ "grDiscreteRicciExtractionShellACRConstantIs80"
        ∷ "grDiscreteRicciExtractionConservativeCRExtractionConstantIs640"
        ∷ "canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt"
        ∷ "grSchwarzschildFiniteRicciPerturbationPointCRConstantIs48"
        ∷ "grSchwarzschildFiniteRicciPerturbationConservativeCRConstantIs640"
        ∷ []
    ; ricciPerturbationExtractionTargetVarsAreCanonical =
        refl
    ; currentGRAnalyticKernelRemainingVars =
        "nextAnalyticKernelShellA_LGammaIs72"
        ∷ "nextAnalyticKernelShellA_CRIs80"
        ∷ "nextAnalyticKernelShellA_CPrimeDenominatorIs27"
        ∷ "nextAnalyticKernelSchwarzschildShellAEnvelope640"
        ∷ "nextAnalyticKernelRicciPerturbationBound640"
        ∷ []
    ; currentGRAnalyticKernelRemainingVarsAreCanonical =
        refl
    ; nsGW1DegeneracyStatusContext =
        "NS-GW-1 degeneracy status is settled here only as non-promoting context: numeric evidence lane only; DNS confirmation and DNS sign classification remain outside this GR analytic-kernel tranche."
    ; nsGW1DegeneracyStatusContextIsCanonical =
        refl
    ; nsGW1DegeneracyStatusNonPromoting =
        true
    ; nsGW1DegeneracyStatusNonPromotingIsTrue =
        refl
    ; nsGW1DegeneracyDoesNotPromoteGRKernel =
        true
    ; nsGW1DegeneracyDoesNotPromoteGRKernelIsTrue =
        refl
    ; machineCheckedChristoffelC0Constants =
        Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedChristoffelC0ConstantsAreCanonical =
        refl
    ; finalShellA_LGammaIs48 =
        Continuum.machineCheckedChristoffelL_GammaIs48
    ; finalShellA_RicciExtractionConstantIs640 =
        Continuum.machineCheckedRicciContractionExtractionConstantIs640
    ; finalShellA_ConservativeCGammaUsed =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.conservativeShellCGammaUsedIsTrue
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; correctedTightShellA_LGamma =
        44
    ; correctedTightShellA_LGammaIs44 =
        refl
    ; correctedTightShellA_LGammaDocumentationOnly =
        true
    ; correctedTightShellA_LGammaDocumentationOnlyIsTrue =
        refl
    ; correctedTightShellA_LGammaPreservesFinal48 =
        true
    ; correctedTightShellA_LGammaPreservesFinal48IsTrue =
        refl
    ; correctedTightShellA_LGammaPreservesLegacy72 =
        true
    ; correctedTightShellA_LGammaPreservesLegacy72IsTrue =
        refl
    ; selectedChristoffelC0Constants =
        Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedChristoffelC0ConstantsAreCanonical =
        refl
    ; selectedChristoffelC0FormulaStability48 =
        Continuum.selectedSymbolicRationalChristoffelC0FormulaStabilityIs48
    ; selectedChristoffelC0NoArbitraryConnectionEquality =
        Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.noArbitraryConnectionEqualityClaimedIsTrue
          Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; shellADenominatorReciprocal =
        Continuum.canonicalOrderedRationalShellADenominatorReciprocalReceipt
    ; shellADenominatorReciprocalIsCanonical =
        refl
    ; shellADenominatorReciprocalFeedsC0Stability =
        Continuum.orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable
    ; orderedGaugeToolkit =
        Continuum.canonicalOrderedRationalGaugeToolkitReceipt
    ; orderedGaugeToolkitIsCanonical =
        refl
    ; orderedGaugeScale48 =
        Continuum.orderedRationalGaugeScale48Is48
    ; orderedGaugeToolkitNotPromoted =
        Continuum.OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromotedIsFalse
          Continuum.canonicalOrderedRationalGaugeToolkitReceipt
    ; orderedShellAConstants =
        Continuum.canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; orderedShellAConstantsAreCanonical =
        refl
    ; orderedShellA_LGammaIs72 =
        Continuum.orderedRationalShellA_L_GammaIs72
    ; orderedShellA_CRIs80 =
        Continuum.orderedRationalShellA_C_RIs80
    ; orderedShellA_CGammaIs1 =
        Continuum.orderedRationalShellA_C_GammaIs1
    ; orderedShellA_CPrimeNumeratorIs26 =
        Continuum.orderedRationalShellA_CPrime_GammaNumeratorIs26
    ; orderedShellA_CPrimeDenominatorIs27 =
        Continuum.orderedRationalShellA_CPrime_GammaDenominatorIs27
    ; orderedShellARequestedInequalityPrimitive =
        Continuum.orderedRationalShellARequestedInequalityPrimitive
    ; orderedShellAQQTheoremNotPromoted =
        Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.orderedQQTheoremPromotedIsFalse
          Continuum.canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; orderedShellAAnalyticEstimateNotPromoted =
        Continuum.OrderedRationalShellAChristoffelC0ConstantReceipt.analyticEstimatePromotedIsFalse
          Continuum.canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; orderedShellAPerturbationRoute =
        Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; orderedShellAPerturbationRouteIsCanonical =
        refl
    ; orderedShellAPerturbationRouteL_GammaIs72 =
        Continuum.orderedRationalShellAPerturbationRouteL_GammaIs72
    ; orderedShellAPerturbationRouteNotPromoted =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.fullOrderedQQEstimatePromotedIsFalse
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; schwarzschildShellAExactCalculation =
        Schwarzschild.canonicalSchwarzschildShellAExactCalculationReceipt
    ; schwarzschildShellAExactCalculationIsCanonical =
        refl
    ; schwarzschildShellAConservativeEnvelope640 =
        Schwarzschild.SchwarzschildShellAExactCalculationReceipt.conservativeEnvelopeIsSixHundredForty
          Schwarzschild.canonicalSchwarzschildShellAExactCalculationReceipt
    ; schwarzschildShellANoContinuumRicciPromotion =
        Schwarzschild.SchwarzschildShellAExactCalculationReceipt.continuumRicciPromotedIsFalse
          Schwarzschild.canonicalSchwarzschildShellAExactCalculationReceipt
    ; ricciFinitePerturbationReceipt =
        Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciFinitePerturbationReceiptIsCanonical =
        true
    ; ricciFinitePerturbationReceiptIsCanonicalTrue =
        refl
    ; ricciPerturbationBound640 =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBoundIs640
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciPerturbationPointCRConstant48 =
        Ricci.grSchwarzschildFiniteRicciPerturbationPointCRConstantIs48
    ; ricciPerturbationShellACRConstant80 =
        Ricci.grSchwarzschildFiniteRicciPerturbationShellACRConstantIs80
    ; ricciPerturbationConservativeCRConstant640 =
        Ricci.grSchwarzschildFiniteRicciPerturbationConservativeCRConstantIs640
    ; ricciPerturbationConnectionErrorExtractionDependency =
        Ricci.grSchwarzschildFiniteRicciConnectionErrorBoundExtractionDependencyNameExact
    ; ricciPerturbationNotConvergencePromotion =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.ricciPerturbationBoundPromotedAsConvergenceIsFalse
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciExternalContinuumAuthorityNotClaimed =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.externalContinuumSchwarzschildAuthorityClaimedIsFalse
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; kernelDependencyName =
        "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel"
    ; kernelDependencyNameIsCanonical =
        refl
    ; analyticKernelStillOpen =
        true
    ; analyticKernelStillOpenIsTrue =
        refl
    ; kernelObstructionReceipt =
        Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; kernelObstructionReceiptIsCanonical =
        refl
    ; kernelObstructionGlobalKernelNotConstructed =
        Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.globalKernelLocallyConstructedIsFalse
          Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; kernelObstructionNoFinFourTensorLayer =
        Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.concreteFinFourTensorLayerPresentIsFalse
          Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; kernelObstructionNoComponentChristoffelFormula =
        Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.componentChristoffelFormulaPresentIsFalse
          Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; kernelObstructionNoRicciContractionLayer =
        Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.ricciComponentContractionLayerPresentIsFalse
          Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; kernelObstructionSchwarzschildRowsCanonical =
        Continuum.SymbolicRationalChristoffelC0KernelObstructionReceipt.schwarzschildSevenSlotDerivativeBoundRowsAreCanonical
          Continuum.canonicalSymbolicRationalChristoffelC0KernelObstructionReceipt
    ; requiredAnalyticalProofs =
        "tier 1: ordered rational gauge toolkit in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalGaugeToolkitReceipt and orderedRationalGauge* projections"
        ∷ "tier 2: Shell A denominator chain in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalShellADenominatorReciprocalReceipt and orderedRationalShellA* projections"
        ∷ "tier 3: Christoffel derivative bounds in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalOrderedRationalShellAChristoffelC0ConstantReceipt, C_Gamma=1, and C'_Gamma=26/27 projections"
        ∷ "corrected tight Shell A L_Gamma=44 is recorded as documentation-only aggregation metadata; final/conservative L_Gamma=48 and legacy 72 overbound projections are preserved"
        ∷ "tier 4: Christoffel C0 stability in DASHI/Physics/Closure/ContinuumLimitTheorem.agda at canonicalMachineCheckedChristoffelC0ConstantReceipt and selectedSymbolicRationalChristoffelC0FormulaStabilityIs48"
        ∷ "tier 5: Ricci perturbation extraction in DASHI/Physics/Closure/GRDiscreteRicciCandidateFromCurvature.agda at canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt and canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt"
        ∷ "current GR analytic-kernel remaining variables are recorded explicitly as five non-promoting aggregation booleans; NS-GW-1 degeneracy context remains numeric-evidence-only and outside promotion"
        ∷ []
    ; requiredAnalyticalProofsAreCanonical =
        refl
    }

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

    schwarzschildCanonicalRequestExternalGates :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateRequest.externalGates
        (Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.request
          schwarzschildCanonicalCandidateReceipt)
      ≡
      Schwarzschild.canonicalSchwarzschildExternalGates

    schwarzschildCanonicalBirkhoffGateFalse :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.birkhoffExteriorUniquenessPromoted
        schwarzschildCanonicalCandidateReceipt
      ≡
      false

    schwarzschildCanonicalW4MassGateFalse :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.w4MassAuthorityPromoted
        schwarzschildCanonicalCandidateReceipt
      ≡
      false

    schwarzschildCanonicalContinuumRicciGateFalse :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.continuumRicciConvergencePromoted
        schwarzschildCanonicalCandidateReceipt
      ≡
      false

    schwarzschildCanonicalCandidate256GateFalse :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.candidate256AuthorityPromoted
        schwarzschildCanonicalCandidateReceipt
      ≡
      false

    rationalShellWeakFieldMatchAdapter :
      Schwarzschild.RationalShellWeakFieldMatchAdapter

    rationalShellWeakFieldAdapterFirstMissing :
      Schwarzschild.RationalShellWeakFieldMatchAdapter.firstMissingAfterAdapter
        rationalShellWeakFieldMatchAdapter
      ≡
      Schwarzschild.missingSchwarzschildMetricMatch

    rationalShellWeakFieldAdapterNoVacuumPromotion :
      Schwarzschild.RationalShellWeakFieldMatchAdapter.vacuumPromotion
        rationalShellWeakFieldMatchAdapter
      ≡
      false

    schwarzschildRs2R3AnalyticTable :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt

    schwarzschildRs2R3AnalyticTableNoVacuumPromotion :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotion
        schwarzschildRs2R3AnalyticTable
      ≡
      false

    schwarzschildRs2R3LeviCivitaRicciClosure :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt

    schwarzschildRs2R3PointTableLeviCivitaClosed :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableLeviCivitaClosed
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      true

    schwarzschildRs2R3PointTableRicciZeroClosed :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableRicciZeroClosed
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      true

    schwarzschildRs2R3PointTableEinsteinZeroClosed :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableEinsteinZeroClosed
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      true

    schwarzschildRs2R3ClosureNoBirkhoffPromotion :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.birkhoffPromoted
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      false

    schwarzschildRs2R3ClosureNoW4Promotion :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.w4Promoted
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      false

    schwarzschildRs2R3ClosureNoCandidate256Promotion :
      Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.candidate256Promoted
        schwarzschildRs2R3LeviCivitaRicciClosure
      ≡
      false

    schwarzschildShellSupremumBounds :
      Schwarzschild.SchwarzschildShellSupremumBoundsReceipt

    schwarzschildShellSupremumRsIsTwo :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRs
        (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
          schwarzschildShellSupremumBounds)
      ≡
      Schwarzschild.twoN

    schwarzschildShellSupremumRMinIsThree :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMin
        (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
          schwarzschildShellSupremumBounds)
      ≡
      Schwarzschild.threeN

    schwarzschildShellSupremumRMaxIsThree :
      Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMax
        (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
          schwarzschildShellSupremumBounds)
      ≡
      Schwarzschild.threeN

    schwarzschildShellConservativeCGammaIsTwo :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.conservativeShellCGamma
        (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
          schwarzschildShellSupremumBounds)
      ≡
      Schwarzschild.posTwo

    schwarzschildShellRepoConservativeRicciConstantIs640 :
      Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeRicciContraction
        (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
          schwarzschildShellSupremumBounds)
      ≡
      Schwarzschild.sixHundredFortyN

    schwarzschildNonDegenerateShellAudit :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts

    schwarzschildNonDegenerateShellAIsCanonical :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.shellA
        schwarzschildNonDegenerateShellAudit
      ≡
      Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt

    schwarzschildNonDegenerateShellBIsCanonical :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.shellB
        schwarzschildNonDegenerateShellAudit
      ≡
      Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt

    schwarzschildNonDegeneratePointShellRemainsCanonical :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.pointShellConstants
        schwarzschildNonDegenerateShellAudit
      ≡
      Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt

    schwarzschildShellA_LGammaIs72 :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGamma
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
      ≡
      Schwarzschild.posFortyEight

    schwarzschildShellA_CRIs80 :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cR
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
      ≡
      Schwarzschild.posEighty

    schwarzschildShellA_NoBirkhoffPromotion :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.birkhoffPromoted
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
      ≡
      false

    schwarzschildShellB_LGammaIs112 :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGamma
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
      ≡
      Schwarzschild.posOneHundredTwelve

    schwarzschildShellB_CRIs220 :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cR
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
      ≡
      Schwarzschild.posTwoHundredTwenty

    schwarzschildShellB_NoBirkhoffPromotion :
      Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.birkhoffPromoted
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
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

    downstreamRicciShellAIntervalConstant80 :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellASafeIntervalRicciContinuityConstant
        downstreamRicciConvergenceReadiness
      ≡
      80

    downstreamRicciShellBIntervalConstant220 :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellBSafeIntervalRicciContinuityConstant
        downstreamRicciConvergenceReadiness
      ≡
      220

    downstreamRicciConservativeExtractionConstant640 :
      Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.conservativeRicciExtractionConstant
        downstreamRicciConvergenceReadiness
      ≡
      640

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

    ricciFiniteZeroTableArithmetic :
      Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt

    ricciFiniteZeroTableFirstBlocker :
      Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticFirstBlocker
        ricciFiniteZeroTableArithmetic
      ≡
      Bianchi.missingMetricCompatibility

    ricciFiniteZeroTableContractedBianchiBlocker :
      Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiDependencyBlocker
        ricciFiniteZeroTableArithmetic
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    ricciFiniteZeroTableNoRicciEinsteinPromotion :
      Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.ricciEinsteinTowerPromoted
        ricciFiniteZeroTableArithmetic
      ≡
      false

    ricciFiniteZeroTableNoContractedBianchiPromotion :
      Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiPromoted
        ricciFiniteZeroTableArithmetic
      ≡
      false

    ricciGate4SelectedChainFailClosed :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt

    ricciGate4SelectedChainFirstMetricBlocker :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlocker
        ricciGate4SelectedChainFailClosed
      ≡
      Bianchi.missingMetricCompatibility

    ricciGate4SelectedChainPostCompatibilityConnectionBlocker :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostCompatibilitySelectedConnectionBlocker
        ricciGate4SelectedChainFailClosed
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    ricciGate4SelectedChainPostGeometryBlocker :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostLocalGeometryBlocker
        ricciGate4SelectedChainFailClosed
      ≡
      Bianchi.missingStressEnergyCompatibilityForContractedBianchi

    ricciGate4SelectedChainNoContractedBianchiPromotion :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.contractedBianchiAfterSelectedLeviCivitaDependencyPromoted
        ricciGate4SelectedChainFailClosed
      ≡
      false

    ricciGate4SelectedChainNoNonFlatGRPromotion :
      Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGR
        ricciGate4SelectedChainFailClosed
      ≡
      false

    ricciSchwarzschildFiniteCarrierLeviCivita :
      Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt

    ricciSchwarzschildFiniteCarrierLeviCivitaStillBlocked :
      Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.exactRemainingLeviCivitaBlocker
        ricciSchwarzschildFiniteCarrierLeviCivita
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    ricciSchwarzschildFiniteCarrierNoLeviCivitaPromotion :
      Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        ricciSchwarzschildFiniteCarrierLeviCivita
      ≡
      false

    ricciSchwarzschildFiniteCarrierZeroConsumersTypeable :
      Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.ricciBianchiZeroConsumersTypeable
        ricciSchwarzschildFiniteCarrierLeviCivita
      ≡
      true

    ricciSchwarzschildFiniteCarrierNoSourcedEinsteinPromotion :
      Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.sourcedEinsteinPromoted
        ricciSchwarzschildFiniteCarrierLeviCivita
      ≡
      false

    ricciExtractionReadinessDependencies :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt

    ricciExtractionKernelDependencyName :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelDependencyName
        ricciExtractionReadinessDependencies
      ≡
      "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel"

    ricciExtractionSelectedPairIdentityDependencyName :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityDependencyName
        ricciExtractionReadinessDependencies
      ≡
      "selected-pair identity for finite Ricci contraction extraction"

    ricciExtractionFiniteRicciZeroReady :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.finiteRicciZeroReady
        ricciExtractionReadinessDependencies
      ≡
      true

    ricciExtractionShellAIntervalConstant80 :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellASafeIntervalRicciContinuityConstant
        ricciExtractionReadinessDependencies
      ≡
      80

    ricciExtractionShellBIntervalConstant220 :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellBSafeIntervalRicciContinuityConstant
        ricciExtractionReadinessDependencies
      ≡
      220

    ricciExtractionConservativeConstant640 :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.conservativeRicciExtractionConstant
        ricciExtractionReadinessDependencies
      ≡
      640

    ricciExtractionKernelNotPromotedHere :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelPromotedHere
        ricciExtractionReadinessDependencies
      ≡
      false

    ricciExtractionSelectedPairIdentityNotPromotedHere :
      Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityPromotedHere
        ricciExtractionReadinessDependencies
      ≡
      false

    ricciContractionContinuityConstants :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt

    ricciContractionSharpNumerator1280 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.sharpCRNumerator
        ricciContractionContinuityConstants
      ≡
      1280

    ricciContractionSharpDenominator27 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.sharpCRDenominator
        ricciContractionContinuityConstants
      ≡
      27

    ricciContractionRoundedConstant48 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.ricciContractionContinuityConstant
        ricciContractionContinuityConstants
      ≡
      48

    ricciContractionPointShellConstant48 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShellRicciContinuityConstant
        ricciContractionContinuityConstants
      ≡
      48

    ricciContractionPointShell48Only :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShell48Only
        ricciContractionContinuityConstants
      ≡
      true

    ricciContractionShellAIntervalConstant80 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellASafeIntervalRicciContinuityConstant
        ricciContractionContinuityConstants
      ≡
      80

    ricciContractionShellBIntervalConstant220 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellBSafeIntervalRicciContinuityConstant
        ricciContractionContinuityConstants
      ≡
      220

    ricciContractionIntervalShellsUseSafeConstants :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.intervalShellsUseSafeConstants
        ricciContractionContinuityConstants
      ≡
      true

    ricciContractionIntervalShellsDoNotUsePoint48 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.intervalShellsDoNotUsePoint48
        ricciContractionContinuityConstants
      ≡
      true

    ricciContractionConservativeConstant640 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.existingConservativeRicciConstant
        ricciContractionContinuityConstants
      ≡
      640

    ricciContractionConservative640StillValid :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.existingConservative640RemainsValid
        ricciContractionContinuityConstants
      ≡
      true

    ricciContractionConservativeExtractionConstant640 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.conservativeCRExtractionConstant
        ricciContractionContinuityConstants
      ≡
      640

    ricciContractionOptionalTightNumerator112 :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumerator
        ricciContractionContinuityConstants
      ≡
      112

    ricciContractionOptionalTightNumeratorNoPromotion :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumeratorUsedAsPromotion
        ricciContractionContinuityConstants
      ≡
      false

    ricciContractionConstantNoConvergencePromotion :
      Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.constantPromotedAsRicciConvergence
        ricciContractionContinuityConstants
      ≡
      false

    selectedRationalUndoubledChristoffelLift :
      Bianchi.GRSelectedRationalUndoubledChristoffelLift
        Bianchi.canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput

    selectedRationalHalfWitnessIsCanonical :
      Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitness
        selectedRationalUndoubledChristoffelLift
      ≡
      Bianchi.qqHalf

    selectedRationalHalfWitnessDoublesToOne :
      Bianchi.qqDouble
        (Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitness
          selectedRationalUndoubledChristoffelLift)
      ≡
      Q.oneℚ

    selectedRationalPairIdentityHandoff :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt

    selectedRationalPairIdentityRouteStaged :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRouteStaged
        selectedRationalPairIdentityHandoff
      ≡
      true

    selectedRationalPairQQHalfDoublesToOne :
      Bianchi.qqDouble
        (Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.qqDivisionByTwoWitness
          selectedRationalPairIdentityHandoff)
      ≡
      Q.oneℚ

    selectedRationalPairBypassesQQHalvingObstruction :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.qqSelectedSurfaceBypassesOddHalvingObstruction
        selectedRationalPairIdentityHandoff
      ≡
      true

    selectedRationalPairFiniteRObstructionStillPresent :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.finiteRCarrierOddHalvingObstructionStillPresent
        selectedRationalPairIdentityHandoff
      ≡
      true

    selectedRationalPairNoFiniteRChristoffelPromotion :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesFiniteRChristoffel
        selectedRationalPairIdentityHandoff
      ≡
      false

    selectedRationalPairNoContinuumBianchiPromotion :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesContinuumBianchi
        selectedRationalPairIdentityHandoff
      ≡
      false

    selectedRationalPairKeepsLeviCivitaBlocked :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        selectedRationalPairIdentityHandoff
      ≡
      false

    selectedRationalPairExactDownstreamBlocker :
      Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.exactDownstreamBlocker
        selectedRationalPairIdentityHandoff
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

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

    machineCheckedChristoffelL_Ricci640 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.L_Ricci
        machineCheckedChristoffelC0Constants
      ≡
      640

    machineCheckedChristoffelOptionalSharpL_Ricci112 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.optionalSharpL_Ricci
        machineCheckedChristoffelC0Constants
      ≡
      112

    machineCheckedShell_C_Gamma2 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
        machineCheckedChristoffelC0Constants
      ≡
      2

    machineCheckedShell_C_GammaBound :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
        machineCheckedChristoffelC0Constants
      ≤
      2

    machineCheckedConservativeShellCGammaUsed :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.conservativeShellCGammaUsed
        machineCheckedChristoffelC0Constants
      ≡
      true

    correctedTightShellA_LGamma :
      Nat

    correctedTightShellA_LGammaIs44 :
      correctedTightShellA_LGamma
      ≡
      44

    correctedTightShellA_LGammaDocumentationOnly :
      Bool

    correctedTightShellA_LGammaDocumentationOnlyIsTrue :
      correctedTightShellA_LGammaDocumentationOnly
      ≡
      true

    correctedTightShellA_LGammaPreservesFinal48 :
      Bool

    correctedTightShellA_LGammaPreservesFinal48IsTrue :
      correctedTightShellA_LGammaPreservesFinal48
      ≡
      true

    correctedTightShellA_LGammaPreservesLegacy72 :
      Bool

    correctedTightShellA_LGammaPreservesLegacy72IsTrue :
      correctedTightShellA_LGammaPreservesLegacy72
      ≡
      true

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

    selectedChristoffelC0ConstantReceipt :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedChristoffelC0ConstantsAreCanonical :
      selectedChristoffelC0ConstantReceipt
      ≡
      Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedChristoffelC0ShellA_TightCGammaIsOne :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.selectedTight_C_GammaNat
        selectedChristoffelC0ConstantReceipt
      ≡
      1

    selectedChristoffelC0ShellB_ConservativeCGammaIsTwo :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.conservativeShell_C_GammaNat
        selectedChristoffelC0ConstantReceipt
      ≡
      2

    selectedChristoffelC0FormulaStabilityConstant48 :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
        selectedChristoffelC0ConstantReceipt
      ≡
      48

    selectedChristoffelC0RicciIntervalNumerator48 :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNat
        selectedChristoffelC0ConstantReceipt
      ≡
      48

    selectedChristoffelC0RicciIntervalDenominator640 :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNat
        selectedChristoffelC0ConstantReceipt
      ≡
      640

    selectedChristoffelC0NoArbitraryConnectionEquality :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.noArbitraryConnectionEqualityClaimed
        selectedChristoffelC0ConstantReceipt
      ≡
      true

    selectedChristoffelC0Primitive :
      Continuum.SelectedSymbolicRationalChristoffelC0Primitive

    selectedChristoffelC0PrimitivePairIdentity :
      Continuum.SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
        selectedChristoffelC0Primitive
      ≡
      Continuum.SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
        selectedChristoffelC0Primitive

    zeroEpsilonSelectedChristoffelC0EqualityBridge :
      Continuum.ContinuumLimitAnalyticPrimitives.connectionErrorBound
        Continuum.symbolicRationalContinuumAnalyticPrimitives
        0
        0
        (Continuum.SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
          selectedChristoffelC0Primitive)
        (Continuum.SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
          selectedChristoffelC0Primitive)

    selectedChristoffelC0OnlySelectedPairReflExtraction :
      Continuum.SelectedSymbolicRationalChristoffelC0Primitive.onlySelectedPairReflExtraction
        selectedChristoffelC0Primitive
      ≡
      true

    selectedChristoffelC0NoArbitraryEqualityPromotion :
      Continuum.SelectedSymbolicRationalChristoffelC0Primitive.arbitraryConnectionEqualityPromoted
        selectedChristoffelC0Primitive
      ≡
      false

    nextAnalyticKernelTranche :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt

    nextAnalyticKernelTrancheIsCanonical :
      Bool

    nextAnalyticKernelTrancheIsCanonicalTrue :
      nextAnalyticKernelTrancheIsCanonical
      ≡
      true

    nextAnalyticKernelStillOpen :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.analyticKernelStillOpen
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelDependencyName :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.kernelDependencyName
        nextAnalyticKernelTranche
      ≡
      "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel"

    nextAnalyticKernelGaugeToolkitTargets :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.gaugeToolkitTargetVars
        nextAnalyticKernelTranche
      ≡
      "canonicalOrderedRationalGaugeToolkitReceipt"
      ∷ "orderedRationalGaugeD_QQZeroLawPrimitive"
      ∷ "orderedRationalGaugeD_QQSymmetryLawPrimitive"
      ∷ "orderedRationalGaugeD_QQTriangleLawPrimitive"
      ∷ "orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive"
      ∷ "orderedRationalGaugeThreeMinusNPositiveLawPrimitive"
      ∷ "orderedRationalGaugeScale48Is48"
      ∷ "orderedRationalGaugeScale48NonnegativeLawPrimitive"
      ∷ []

    nextAnalyticKernelShellADenominatorTargets :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.shellADenominatorTargetVars
        nextAnalyticKernelTranche
      ≡
      "canonicalOrderedRationalShellADenominatorReciprocalReceipt"
      ∷ "orderedRationalShellARadialMinusSchwarzschildLowerBoundIs1"
      ∷ "orderedRationalShellAInverseMetricAbsMaxIs4"
      ∷ "orderedRationalShellAMetricDerivativeAbsMaxIs8"
      ∷ "orderedRationalShellAChristoffelFormulaEnvelopeIs72"
      ∷ "orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable"
      ∷ []

    nextAnalyticKernelChristoffelDerivativeTargets :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelDerivativeBoundsTargetVars
        nextAnalyticKernelTranche
      ≡
      "canonicalOrderedRationalShellAChristoffelC0ConstantReceipt"
      ∷ "orderedRationalShellA_C_GammaIs1"
      ∷ "orderedRationalShellA_CPrime_GammaNumeratorIs26"
      ∷ "orderedRationalShellA_CPrime_GammaDenominatorIs27"
      ∷ "orderedRationalShellARequestedInequalityPrimitive"
      ∷ "canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt"
      ∷ []

    nextAnalyticKernelChristoffelC0Targets :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelC0StabilityTargetVars
        nextAnalyticKernelTranche
      ≡
      "canonicalMachineCheckedChristoffelC0ConstantReceipt"
      ∷ "machineCheckedChristoffelL_GammaIs48"
      ∷ "canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt"
      ∷ "selectedSymbolicRationalChristoffelC0FormulaStabilityIs48"
      ∷ "canonicalSelectedSymbolicRationalChristoffelC0Primitive"
      ∷ "selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound"
      ∷ []

    nextAnalyticKernelRicciExtractionTargets :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.ricciPerturbationExtractionTargetVars
        nextAnalyticKernelTranche
      ≡
      "canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt"
      ∷ "grDiscreteRicciExtractionConnectionErrorBoundExtractionDependencyNameExact"
      ∷ "grDiscreteRicciExtractionPointCRConstantIs48"
      ∷ "grDiscreteRicciExtractionShellACRConstantIs80"
      ∷ "grDiscreteRicciExtractionConservativeCRExtractionConstantIs640"
      ∷ "canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt"
      ∷ "grSchwarzschildFiniteRicciPerturbationPointCRConstantIs48"
      ∷ "grSchwarzschildFiniteRicciPerturbationConservativeCRConstantIs640"
      ∷ []

    nextAnalyticKernelRemainingVars :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.currentGRAnalyticKernelRemainingVars
        nextAnalyticKernelTranche
      ≡
      "nextAnalyticKernelShellA_LGammaIs72"
      ∷ "nextAnalyticKernelShellA_CRIs80"
      ∷ "nextAnalyticKernelShellA_CPrimeDenominatorIs27"
      ∷ "nextAnalyticKernelSchwarzschildShellAEnvelope640"
      ∷ "nextAnalyticKernelRicciPerturbationBound640"
      ∷ []

    nextAnalyticKernelNSGW1DegeneracyContext :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyStatusContext
        nextAnalyticKernelTranche
      ≡
      "NS-GW-1 degeneracy status is settled here only as non-promoting context: numeric evidence lane only; DNS confirmation and DNS sign classification remain outside this GR analytic-kernel tranche."

    nextAnalyticKernelNSGW1DegeneracyNonPromoting :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyStatusNonPromoting
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelNSGW1DegeneracyDoesNotPromoteGR :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyDoesNotPromoteGRKernel
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelFinalShellA_LGammaIs48 :
      Continuum.MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        (GRProofArchitectureNextAnalyticKernelTrancheReceipt.machineCheckedChristoffelC0Constants
          nextAnalyticKernelTranche)
      ≡
      48

    nextAnalyticKernelFinalShellASelectedFormula48 :
      Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
        (GRProofArchitectureNextAnalyticKernelTrancheReceipt.selectedChristoffelC0Constants
          nextAnalyticKernelTranche)
      ≡
      48

    nextAnalyticKernelRicciPointCR48 :
      Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.pointCRConstant
        (GRProofArchitectureNextAnalyticKernelTrancheReceipt.ricciFinitePerturbationReceipt
          nextAnalyticKernelTranche)
      ≡
      48

    nextAnalyticKernelCorrectedTightShellA_LGamma44 :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGamma
        nextAnalyticKernelTranche
      ≡
      44

    nextAnalyticKernelCorrectedTightShellA_DocumentationOnly :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaDocumentationOnly
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelCorrectedTightShellA_PreservesFinal48 :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesFinal48
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelCorrectedTightShellA_PreservesLegacy72 :
      GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesLegacy72
        nextAnalyticKernelTranche
      ≡
      true

    nextAnalyticKernelShellA_LGammaIs72 :
      Bool

    nextAnalyticKernelShellA_CRIs80 :
      Bool

    nextAnalyticKernelShellA_CPrimeDenominatorIs27 :
      Bool

    nextAnalyticKernelSchwarzschildShellAEnvelope640 :
      Bool

    nextAnalyticKernelRicciPerturbationBound640 :
      Bool

    nextAnalyticKernelNoRicciConvergencePromotion :
      Bool

    conservativeGRRouteRows :
      List String

    conservativeGRRouteRowsAreCanonical :
      conservativeGRRouteRows
      ≡
      "angular ledger=13 nonzero / 51 zero"
      ∷ "bracket_le=8 via r_max=4M and bracket_le=2*r_max"
      ∷ "theta-shell/cot-bound required for angular cot slots"
      ∷ "C_shell=8 Γ background shell bound"
      ∷ "h_dΓ_tight=11/2"
      ∷ "derivTermBound_44"
      ∷ "productTermBound via 176<=640"
      ∷ "fail-closed/no promotion"
      ∷ []

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
    ; schwarzschildCanonicalRequestExternalGates =
        Schwarzschild.SchwarzschildLimitCanonicalCandidateRequest.externalGatesAreCanonical
          (Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.request
            Schwarzschild.canonicalSchwarzschildLimitCanonicalCandidateReceipt)
    ; schwarzschildCanonicalBirkhoffGateFalse =
        Schwarzschild.schwarzschildCanonicalBirkhoffGateFalse
    ; schwarzschildCanonicalW4MassGateFalse =
        Schwarzschild.schwarzschildCanonicalW4MassGateFalse
    ; schwarzschildCanonicalContinuumRicciGateFalse =
        Schwarzschild.schwarzschildCanonicalContinuumRicciGateFalse
    ; schwarzschildCanonicalCandidate256GateFalse =
        Schwarzschild.schwarzschildCanonicalCandidate256GateFalse
    ; rationalShellWeakFieldMatchAdapter =
        Schwarzschild.canonicalRationalShellWeakFieldMatchAdapter
    ; rationalShellWeakFieldAdapterFirstMissing =
        Schwarzschild.rationalShellWeakFieldAdapterFirstMissingMetricMatch
    ; rationalShellWeakFieldAdapterNoVacuumPromotion =
        Schwarzschild.RationalShellWeakFieldMatchAdapter.vacuumPromotionIsFalse
          Schwarzschild.canonicalRationalShellWeakFieldMatchAdapter
    ; schwarzschildRs2R3AnalyticTable =
        Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; schwarzschildRs2R3AnalyticTableNoVacuumPromotion =
        Schwarzschild.schwarzschildRs2R3AnalyticTableNoVacuumPromotion
    ; schwarzschildRs2R3LeviCivitaRicciClosure =
        Schwarzschild.canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
    ; schwarzschildRs2R3PointTableLeviCivitaClosed =
        Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableLeviCivitaClosedIsTrue
          Schwarzschild.canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
    ; schwarzschildRs2R3PointTableRicciZeroClosed =
        Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableRicciZeroClosedIsTrue
          Schwarzschild.canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
    ; schwarzschildRs2R3PointTableEinsteinZeroClosed =
        Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableEinsteinZeroClosedIsTrue
          Schwarzschild.canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
    ; schwarzschildRs2R3ClosureNoBirkhoffPromotion =
        Schwarzschild.schwarzschildRs2R3ClosureBirkhoffFalse
    ; schwarzschildRs2R3ClosureNoW4Promotion =
        Schwarzschild.schwarzschildRs2R3ClosureW4False
    ; schwarzschildRs2R3ClosureNoCandidate256Promotion =
        Schwarzschild.schwarzschildRs2R3ClosureCandidate256False
    ; schwarzschildShellSupremumBounds =
        Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt
    ; schwarzschildShellSupremumRsIsTwo =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRsIsTwo
          (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
            Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
    ; schwarzschildShellSupremumRMinIsThree =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMinIsThree
          (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
            Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
    ; schwarzschildShellSupremumRMaxIsThree =
        Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRMaxIsThree
          (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
            Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
    ; schwarzschildShellConservativeCGammaIsTwo =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.conservativeShellCGammaIsTwo
          (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
            Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
    ; schwarzschildShellRepoConservativeRicciConstantIs640 =
        Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeRicciContractionIsSixHundredForty
          (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
            Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
    ; schwarzschildNonDegenerateShellAudit =
        Schwarzschild.canonicalSchwarzschildNonDegenerateShellSupremumAuditReceipts
    ; schwarzschildNonDegenerateShellAIsCanonical =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.shellAIsCanonical
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellSupremumAuditReceipts
    ; schwarzschildNonDegenerateShellBIsCanonical =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.shellBIsCanonical
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellSupremumAuditReceipts
    ; schwarzschildNonDegeneratePointShellRemainsCanonical =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumAuditReceipts.pointShellConstantsRemainCanonical
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellSupremumAuditReceipts
    ; schwarzschildShellA_LGammaIs72 =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGammaMatchesAudit
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
    ; schwarzschildShellA_CRIs80 =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cRMatchesAudit
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
    ; schwarzschildShellA_NoBirkhoffPromotion =
        Schwarzschild.schwarzschildNonDegenerateShellABirkhoffFalse
    ; schwarzschildShellB_LGammaIs112 =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGammaMatchesAudit
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
    ; schwarzschildShellB_CRIs220 =
        Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cRMatchesAudit
          Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
    ; schwarzschildShellB_NoBirkhoffPromotion =
        Schwarzschild.schwarzschildNonDegenerateShellBBirkhoffFalse
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
    ; downstreamRicciShellAIntervalConstant80 =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellASafeIntervalRicciContinuityConstantIs80
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciShellBIntervalConstant220 =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellBSafeIntervalRicciContinuityConstantIs220
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
    ; downstreamRicciConservativeExtractionConstant640 =
        Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.conservativeRicciExtractionConstantIs640
          Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
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
    ; ricciFiniteZeroTableArithmetic =
        Ricci.canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
    ; ricciFiniteZeroTableFirstBlocker =
        Ricci.grDiscreteRicciFiniteZeroTableFirstBlocker
    ; ricciFiniteZeroTableContractedBianchiBlocker =
        Ricci.grDiscreteRicciFiniteZeroTableContractedBianchiBlocker
    ; ricciFiniteZeroTableNoRicciEinsteinPromotion =
        Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.ricciEinsteinTowerPromotedIsFalse
          Ricci.canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
    ; ricciFiniteZeroTableNoContractedBianchiPromotion =
        Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiPromotedIsFalse
          Ricci.canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
    ; ricciGate4SelectedChainFailClosed =
        Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; ricciGate4SelectedChainFirstMetricBlocker =
        Ricci.grDiscreteRicciGate4SelectedChainFirstMetricBlocker
    ; ricciGate4SelectedChainPostCompatibilityConnectionBlocker =
        Ricci.grDiscreteRicciGate4SelectedChainPostCompatibilityConnectionBlocker
    ; ricciGate4SelectedChainPostGeometryBlocker =
        Ricci.grDiscreteRicciGate4SelectedChainPostGeometryBlocker
    ; ricciGate4SelectedChainNoContractedBianchiPromotion =
        Ricci.grDiscreteRicciGate4ContractedBianchiAfterSelectedDependencyStillBlocked
    ; ricciGate4SelectedChainNoNonFlatGRPromotion =
        Ricci.grDiscreteRicciGate4SelectedChainNoNonFlatPromotion
    ; ricciSchwarzschildFiniteCarrierLeviCivita =
        Ricci.canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; ricciSchwarzschildFiniteCarrierLeviCivitaStillBlocked =
        Ricci.grSchwarzschildFiniteCarrierLeviCivitaStillBlocked
    ; ricciSchwarzschildFiniteCarrierNoLeviCivitaPromotion =
        Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedCarrierConnectionIsLeviCivitaPromotedIsFalse
          Ricci.canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; ricciSchwarzschildFiniteCarrierZeroConsumersTypeable =
        Ricci.grSchwarzschildFiniteCarrierRicciBianchiConsumersType
    ; ricciSchwarzschildFiniteCarrierNoSourcedEinsteinPromotion =
        Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.sourcedEinsteinPromotedIsFalse
          Ricci.canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; ricciExtractionReadinessDependencies =
        Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionKernelDependencyName =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelDependencyNameIsCanonical
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionSelectedPairIdentityDependencyName =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityDependencyNameIsCanonical
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionFiniteRicciZeroReady =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.finiteRicciZeroReadyIsTrue
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionShellAIntervalConstant80 =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellASafeIntervalRicciContinuityConstantIs80
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionShellBIntervalConstant220 =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellBSafeIntervalRicciContinuityConstantIs220
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionConservativeConstant640 =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.conservativeRicciExtractionConstantIs640
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionKernelNotPromotedHere =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelPromotedHereIsFalse
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciExtractionSelectedPairIdentityNotPromotedHere =
        Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityPromotedHereIsFalse
          Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
    ; ricciContractionContinuityConstants =
        Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionSharpNumerator1280 =
        Ricci.grDiscreteRicciSharpCRNumeratorIs1280
    ; ricciContractionSharpDenominator27 =
        Ricci.grDiscreteRicciSharpCRDenominatorIs27
    ; ricciContractionRoundedConstant48 =
        Ricci.grDiscreteRicciContinuityRoundedConstantIs48
    ; ricciContractionPointShellConstant48 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShellRicciContinuityConstantIs48
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionPointShell48Only =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShell48OnlyIsTrue
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionShellAIntervalConstant80 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellASafeIntervalRicciContinuityConstantIs80
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionShellBIntervalConstant220 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellBSafeIntervalRicciContinuityConstantIs220
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionIntervalShellsUseSafeConstants =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.intervalShellsUseSafeConstantsIsTrue
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionIntervalShellsDoNotUsePoint48 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.intervalShellsDoNotUsePoint48IsTrue
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionConservativeConstant640 =
        Ricci.grDiscreteRicciExistingConservativeConstantIs640
    ; ricciContractionConservative640StillValid =
        Ricci.grDiscreteRicciExistingConservative640StillValid
    ; ricciContractionConservativeExtractionConstant640 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.conservativeCRExtractionConstantIs640
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionOptionalTightNumerator112 =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumeratorIs112
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionOptionalTightNumeratorNoPromotion =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumeratorUsedAsPromotionIsFalse
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; ricciContractionConstantNoConvergencePromotion =
        Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.constantPromotedAsRicciConvergenceIsFalse
          Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
    ; selectedRationalUndoubledChristoffelLift =
        Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedRationalHalfWitnessIsCanonical =
        Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessIsCanonical
          Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedRationalHalfWitnessDoublesToOne =
        Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessDoublesToOne
          Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedRationalPairIdentityHandoff =
        Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairIdentityRouteStaged =
        Bianchi.grSelectedRationalSelectedPairConnectionIdentityAvailable
    ; selectedRationalPairQQHalfDoublesToOne =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.qqDivisionByTwoWitnessDoublesToOne
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairBypassesQQHalvingObstruction =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.qqSelectedSurfaceBypassesOddHalvingObstructionIsTrue
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairFiniteRObstructionStillPresent =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.finiteRCarrierOddHalvingObstructionStillPresentIsTrue
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairNoFiniteRChristoffelPromotion =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesFiniteRChristoffelIsFalse
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairNoContinuumBianchiPromotion =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesContinuumBianchiIsFalse
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; selectedRationalPairKeepsLeviCivitaBlocked =
        Bianchi.grSelectedRationalSelectedPairKeepsLeviCivitaBlocked
    ; selectedRationalPairExactDownstreamBlocker =
        Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.exactDownstreamBlockerIsCarrierConnectionIsLeviCivita
          Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
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
    ; machineCheckedChristoffelL_Ricci640 =
        Continuum.machineCheckedChristoffelL_RicciIs640
    ; machineCheckedChristoffelOptionalSharpL_Ricci112 =
        Continuum.machineCheckedChristoffelOptionalSharpL_RicciIs112
    ; machineCheckedShell_C_Gamma2 =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.shell_C_GammaIs2
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedShell_C_GammaBound =
        Continuum.machineCheckedShell_C_Gamma≤2
    ; machineCheckedConservativeShellCGammaUsed =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.conservativeShellCGammaUsedIsTrue
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; correctedTightShellA_LGamma =
        44
    ; correctedTightShellA_LGammaIs44 =
        refl
    ; correctedTightShellA_LGammaDocumentationOnly =
        true
    ; correctedTightShellA_LGammaDocumentationOnlyIsTrue =
        refl
    ; correctedTightShellA_LGammaPreservesFinal48 =
        true
    ; correctedTightShellA_LGammaPreservesFinal48IsTrue =
        refl
    ; correctedTightShellA_LGammaPreservesLegacy72 =
        true
    ; correctedTightShellA_LGammaPreservesLegacy72IsTrue =
        refl
    ; machineCheckedInverseMetricC0Shape =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.inverseMetricC0ShapeIsPointwiseFiniteCarrier
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedNoExternalAnalyticAuthorityFabricated =
        Continuum.MachineCheckedChristoffelC0ConstantReceipt.noExternalAnalyticAuthorityFabricatedIsFalse
          Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; selectedChristoffelC0ConstantReceipt =
        Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedChristoffelC0ConstantsAreCanonical =
        refl
    ; selectedChristoffelC0ShellA_TightCGammaIsOne =
        Continuum.selectedSymbolicRationalChristoffelC0Tight_C_GammaIs1
    ; selectedChristoffelC0ShellB_ConservativeCGammaIsTwo =
        Continuum.selectedSymbolicRationalChristoffelC0Conservative_C_GammaIs2
    ; selectedChristoffelC0FormulaStabilityConstant48 =
        Continuum.selectedSymbolicRationalChristoffelC0FormulaStabilityIs48
    ; selectedChristoffelC0RicciIntervalNumerator48 =
        Continuum.selectedSymbolicRationalChristoffelC0RicciBoundNumeratorIs48
    ; selectedChristoffelC0RicciIntervalDenominator640 =
        Continuum.selectedSymbolicRationalChristoffelC0RicciBoundDenominatorIs640
    ; selectedChristoffelC0NoArbitraryConnectionEquality =
        Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.noArbitraryConnectionEqualityClaimedIsTrue
          Continuum.canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedChristoffelC0Primitive =
        Continuum.canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedChristoffelC0PrimitivePairIdentity =
        Continuum.selectedSymbolicRationalChristoffelC0PrimitivePairIdentity
    ; zeroEpsilonSelectedChristoffelC0EqualityBridge =
        Continuum.selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound
          0
          0
    ; selectedChristoffelC0OnlySelectedPairReflExtraction =
        Continuum.SelectedSymbolicRationalChristoffelC0Primitive.onlySelectedPairReflExtractionIsTrue
          Continuum.canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedChristoffelC0NoArbitraryEqualityPromotion =
        Continuum.SelectedSymbolicRationalChristoffelC0Primitive.arbitraryConnectionEqualityPromotedIsFalse
          Continuum.canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; nextAnalyticKernelTranche =
        canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelTrancheIsCanonical =
        true
    ; nextAnalyticKernelTrancheIsCanonicalTrue =
        refl
    ; nextAnalyticKernelStillOpen =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.analyticKernelStillOpenIsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelDependencyName =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.kernelDependencyNameIsCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelGaugeToolkitTargets =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.gaugeToolkitTargetVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelShellADenominatorTargets =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.shellADenominatorTargetVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelChristoffelDerivativeTargets =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelDerivativeBoundsTargetVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelChristoffelC0Targets =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelC0StabilityTargetVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelRicciExtractionTargets =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.ricciPerturbationExtractionTargetVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelRemainingVars =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.currentGRAnalyticKernelRemainingVarsAreCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelNSGW1DegeneracyContext =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyStatusContextIsCanonical
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelNSGW1DegeneracyNonPromoting =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyStatusNonPromotingIsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelNSGW1DegeneracyDoesNotPromoteGR =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.nsGW1DegeneracyDoesNotPromoteGRKernelIsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelFinalShellA_LGammaIs48 =
        refl
    ; nextAnalyticKernelFinalShellASelectedFormula48 =
        refl
    ; nextAnalyticKernelRicciPointCR48 =
        refl
    ; nextAnalyticKernelCorrectedTightShellA_LGamma44 =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaIs44
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelCorrectedTightShellA_DocumentationOnly =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaDocumentationOnlyIsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelCorrectedTightShellA_PreservesFinal48 =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesFinal48IsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelCorrectedTightShellA_PreservesLegacy72 =
        GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesLegacy72IsTrue
          canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
    ; nextAnalyticKernelShellA_LGammaIs72 =
        true
    ; nextAnalyticKernelShellA_CRIs80 =
        true
    ; nextAnalyticKernelShellA_CPrimeDenominatorIs27 =
        true
    ; nextAnalyticKernelSchwarzschildShellAEnvelope640 =
        true
    ; nextAnalyticKernelRicciPerturbationBound640 =
        true
    ; nextAnalyticKernelNoRicciConvergencePromotion =
        true
    ; conservativeGRRouteRows =
        "angular ledger=13 nonzero / 51 zero"
        ∷ "bracket_le=8 via r_max=4M and bracket_le=2*r_max"
        ∷ "theta-shell/cot-bound required for angular cot slots"
        ∷ "C_shell=8 Γ background shell bound"
        ∷ "h_dΓ_tight=11/2"
        ∷ "derivTermBound_44"
        ∷ "productTermBound via 176<=640"
        ∷ "fail-closed/no promotion"
        ∷ []
    ; conservativeGRRouteRowsAreCanonical =
        refl
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
        ∷ "Imports and checks the Ricci finite zero-table arithmetic and selected-chain fail-closed receipts"
        ∷ "Imports and checks the Ricci Schwarzschild finite-carrier and extraction readiness dependency receipts"
        ∷ "Imports and checks the Ricci interval constants 1280/27, rounded 48, and conservative 640 without convergence promotion"
        ∷ "Imports and checks the rational undoubled Christoffel lift and selected-pair equality handoff while preserving the finite-r blocker"
        ∷ "Imports and checks the finite 4R/Ricci/scalar/2G arithmetic receipt without GR promotion"
        ∷ "Imports and checks the Gate 4 GR/cosmology schema instance as fail-closed"
        ∷ "Imports and checks the strengthened Schwarzschild request and canonical fail-closed gate receipt"
        ∷ "Imports and checks the rational shell weak-field adapter and r_s=2,r=3 Schwarzschild point-table closure receipts"
        ∷ "Imports and checks the Schwarzschild shell supremum bounds receipt without promoting analytic order or continuum Ricci claims"
        ∷ "Imports and checks the continuum theorem-request surface"
        ∷ "Imports and checks the Continuum machine-checked Christoffel C0 constants"
        ∷ "Imports and checks Shell A/B selected Christoffel constants and the zero-epsilon selected equality bridge without arbitrary equality promotion"
        ∷ "Imports and checks the next analytic-kernel tranche requirements without promoting the ordered QQ theorem or Ricci convergence"
        ∷ "Records the conservative GR route rows: angular ledger=13 nonzero / 51 zero, bracket_le=8 via r_max=4M and bracket_le=2*r_max, theta-shell/cot-bound required for angular cot slots, C_shell=8 Γ background shell bound, h_dΓ_tight=11/2, derivTermBound_44, productTermBound via 176<=640, and fail-closed/no promotion"
        ∷ "Records the five current GR analytic-kernel remaining variables and the settled NS-GW-1 degeneracy status as non-promoting context"
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

grProofArchitectureAggregationSchwarzschildExternalGatesCanonical :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalRequestExternalGates
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildLimitCanonicalCandidateRequest.externalGatesAreCanonical
    (Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.request
      Schwarzschild.canonicalSchwarzschildLimitCanonicalCandidateReceipt)
grProofArchitectureAggregationSchwarzschildExternalGatesCanonical = refl

grProofArchitectureAggregationSchwarzschildBirkhoffGateFalse :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalBirkhoffGateFalse
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildCanonicalBirkhoffGateFalse
grProofArchitectureAggregationSchwarzschildBirkhoffGateFalse = refl

grProofArchitectureAggregationSchwarzschildW4MassGateFalse :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalW4MassGateFalse
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildCanonicalW4MassGateFalse
grProofArchitectureAggregationSchwarzschildW4MassGateFalse = refl

grProofArchitectureAggregationSchwarzschildContinuumRicciGateFalse :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalContinuumRicciGateFalse
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildCanonicalContinuumRicciGateFalse
grProofArchitectureAggregationSchwarzschildContinuumRicciGateFalse = refl

grProofArchitectureAggregationSchwarzschildCandidate256GateFalse :
  GRProofArchitectureAggregationTest.schwarzschildCanonicalCandidate256GateFalse
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildCanonicalCandidate256GateFalse
grProofArchitectureAggregationSchwarzschildCandidate256GateFalse = refl

grProofArchitectureAggregationRationalShellAdapterFirstMissing :
  GRProofArchitectureAggregationTest.rationalShellWeakFieldAdapterFirstMissing
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.rationalShellWeakFieldAdapterFirstMissingMetricMatch
grProofArchitectureAggregationRationalShellAdapterFirstMissing = refl

grProofArchitectureAggregationRationalShellAdapterNoVacuumPromotion :
  GRProofArchitectureAggregationTest.rationalShellWeakFieldAdapterNoVacuumPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.RationalShellWeakFieldMatchAdapter.vacuumPromotionIsFalse
    Schwarzschild.canonicalRationalShellWeakFieldMatchAdapter
grProofArchitectureAggregationRationalShellAdapterNoVacuumPromotion = refl

grProofArchitectureAggregationSchwarzschildAnalyticTableNoVacuumPromotion :
  GRProofArchitectureAggregationTest.schwarzschildRs2R3AnalyticTableNoVacuumPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildRs2R3AnalyticTableNoVacuumPromotion
grProofArchitectureAggregationSchwarzschildAnalyticTableNoVacuumPromotion = refl

grProofArchitectureAggregationSchwarzschildPointTableRicciZeroClosed :
  GRProofArchitectureAggregationTest.schwarzschildRs2R3PointTableRicciZeroClosed
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.pointTableRicciZeroClosedIsTrue
    Schwarzschild.canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
grProofArchitectureAggregationSchwarzschildPointTableRicciZeroClosed = refl

grProofArchitectureAggregationSchwarzschildClosureNoBirkhoffPromotion :
  GRProofArchitectureAggregationTest.schwarzschildRs2R3ClosureNoBirkhoffPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildRs2R3ClosureBirkhoffFalse
grProofArchitectureAggregationSchwarzschildClosureNoBirkhoffPromotion = refl

grProofArchitectureAggregationSchwarzschildClosureNoW4Promotion :
  GRProofArchitectureAggregationTest.schwarzschildRs2R3ClosureNoW4Promotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildRs2R3ClosureW4False
grProofArchitectureAggregationSchwarzschildClosureNoW4Promotion = refl

grProofArchitectureAggregationSchwarzschildClosureNoCandidate256Promotion :
  GRProofArchitectureAggregationTest.schwarzschildRs2R3ClosureNoCandidate256Promotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildRs2R3ClosureCandidate256False
grProofArchitectureAggregationSchwarzschildClosureNoCandidate256Promotion = refl

grProofArchitectureAggregationSchwarzschildShellRsIsTwo :
  GRProofArchitectureAggregationTest.schwarzschildShellSupremumRsIsTwo
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildShellSupremumParameterReceipt.shellRsIsTwo
    (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.shellParameters
      Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
grProofArchitectureAggregationSchwarzschildShellRsIsTwo = refl

grProofArchitectureAggregationSchwarzschildShellCGammaIsTwo :
  GRProofArchitectureAggregationTest.schwarzschildShellConservativeCGammaIsTwo
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildShellSupremumConstantReceipt.conservativeShellCGammaIsTwo
    (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
      Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
grProofArchitectureAggregationSchwarzschildShellCGammaIsTwo = refl

grProofArchitectureAggregationSchwarzschildShellRicciConstant640 :
  GRProofArchitectureAggregationTest.schwarzschildShellRepoConservativeRicciConstantIs640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildShellSupremumConstantReceipt.repoConservativeRicciContractionIsSixHundredForty
    (Schwarzschild.SchwarzschildShellSupremumBoundsReceipt.selectedConstants
      Schwarzschild.canonicalSchwarzschildShellSupremumBoundsReceipt)
grProofArchitectureAggregationSchwarzschildShellRicciConstant640 = refl

grProofArchitectureAggregationSchwarzschildShellA_LGamma72 :
  GRProofArchitectureAggregationTest.schwarzschildShellA_LGammaIs72
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGammaMatchesAudit
    Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
grProofArchitectureAggregationSchwarzschildShellA_LGamma72 = refl

grProofArchitectureAggregationSchwarzschildShellA_CR80 :
  GRProofArchitectureAggregationTest.schwarzschildShellA_CRIs80
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cRMatchesAudit
    Schwarzschild.canonicalSchwarzschildNonDegenerateShellAReceipt
grProofArchitectureAggregationSchwarzschildShellA_CR80 = refl

grProofArchitectureAggregationSchwarzschildShellA_NoBirkhoffPromotion :
  GRProofArchitectureAggregationTest.schwarzschildShellA_NoBirkhoffPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildNonDegenerateShellABirkhoffFalse
grProofArchitectureAggregationSchwarzschildShellA_NoBirkhoffPromotion = refl

grProofArchitectureAggregationSchwarzschildShellB_LGamma112 :
  GRProofArchitectureAggregationTest.schwarzschildShellB_LGammaIs112
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.lGammaMatchesAudit
    Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
grProofArchitectureAggregationSchwarzschildShellB_LGamma112 = refl

grProofArchitectureAggregationSchwarzschildShellB_CR220 :
  GRProofArchitectureAggregationTest.schwarzschildShellB_CRIs220
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.SchwarzschildNonDegenerateShellSupremumReceipt.cRMatchesAudit
    Schwarzschild.canonicalSchwarzschildNonDegenerateShellBReceipt
grProofArchitectureAggregationSchwarzschildShellB_CR220 = refl

grProofArchitectureAggregationSchwarzschildShellB_NoBirkhoffPromotion :
  GRProofArchitectureAggregationTest.schwarzschildShellB_NoBirkhoffPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Schwarzschild.schwarzschildNonDegenerateShellBBirkhoffFalse
grProofArchitectureAggregationSchwarzschildShellB_NoBirkhoffPromotion = refl

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

grProofArchitectureAggregationDownstreamRicciShellAInterval80 :
  GRProofArchitectureAggregationTest.downstreamRicciShellAIntervalConstant80
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellASafeIntervalRicciContinuityConstantIs80
    Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
grProofArchitectureAggregationDownstreamRicciShellAInterval80 = refl

grProofArchitectureAggregationDownstreamRicciShellBInterval220 :
  GRProofArchitectureAggregationTest.downstreamRicciShellBIntervalConstant220
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.shellBSafeIntervalRicciContinuityConstantIs220
    Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
grProofArchitectureAggregationDownstreamRicciShellBInterval220 = refl

grProofArchitectureAggregationDownstreamRicciConservativeExtraction640 :
  GRProofArchitectureAggregationTest.downstreamRicciConservativeExtractionConstant640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciDownstreamConvergenceReadinessReceipt.conservativeRicciExtractionConstantIs640
    Ricci.canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
grProofArchitectureAggregationDownstreamRicciConservativeExtraction640 = refl

grProofArchitectureAggregationRicciFiniteZeroTableFirstBlocker :
  GRProofArchitectureAggregationTest.ricciFiniteZeroTableFirstBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciFiniteZeroTableFirstBlocker
grProofArchitectureAggregationRicciFiniteZeroTableFirstBlocker = refl

grProofArchitectureAggregationRicciFiniteZeroTableContractedBianchiBlocker :
  GRProofArchitectureAggregationTest.ricciFiniteZeroTableContractedBianchiBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciFiniteZeroTableContractedBianchiBlocker
grProofArchitectureAggregationRicciFiniteZeroTableContractedBianchiBlocker = refl

grProofArchitectureAggregationRicciFiniteZeroTableNoRicciEinsteinPromotion :
  GRProofArchitectureAggregationTest.ricciFiniteZeroTableNoRicciEinsteinPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.ricciEinsteinTowerPromotedIsFalse
    Ricci.canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
grProofArchitectureAggregationRicciFiniteZeroTableNoRicciEinsteinPromotion = refl

grProofArchitectureAggregationRicciFiniteZeroTableNoContractedBianchiPromotion :
  GRProofArchitectureAggregationTest.ricciFiniteZeroTableNoContractedBianchiPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiPromotedIsFalse
    Ricci.canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
grProofArchitectureAggregationRicciFiniteZeroTableNoContractedBianchiPromotion = refl

grProofArchitectureAggregationRicciGate4SelectedChainFirstMetricBlocker :
  GRProofArchitectureAggregationTest.ricciGate4SelectedChainFirstMetricBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciGate4SelectedChainFirstMetricBlocker
grProofArchitectureAggregationRicciGate4SelectedChainFirstMetricBlocker = refl

grProofArchitectureAggregationRicciGate4SelectedChainPostCompatibilityConnectionBlocker :
  GRProofArchitectureAggregationTest.ricciGate4SelectedChainPostCompatibilityConnectionBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciGate4SelectedChainPostCompatibilityConnectionBlocker
grProofArchitectureAggregationRicciGate4SelectedChainPostCompatibilityConnectionBlocker = refl

grProofArchitectureAggregationRicciGate4SelectedChainPostGeometryBlocker :
  GRProofArchitectureAggregationTest.ricciGate4SelectedChainPostGeometryBlocker
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciGate4SelectedChainPostGeometryBlocker
grProofArchitectureAggregationRicciGate4SelectedChainPostGeometryBlocker = refl

grProofArchitectureAggregationRicciGate4SelectedChainNoContractedBianchiPromotion :
  GRProofArchitectureAggregationTest.ricciGate4SelectedChainNoContractedBianchiPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciGate4ContractedBianchiAfterSelectedDependencyStillBlocked
grProofArchitectureAggregationRicciGate4SelectedChainNoContractedBianchiPromotion = refl

grProofArchitectureAggregationRicciGate4SelectedChainNoNonFlatGRPromotion :
  GRProofArchitectureAggregationTest.ricciGate4SelectedChainNoNonFlatGRPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciGate4SelectedChainNoNonFlatPromotion
grProofArchitectureAggregationRicciGate4SelectedChainNoNonFlatGRPromotion = refl

grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierLeviCivitaStillBlocked :
  GRProofArchitectureAggregationTest.ricciSchwarzschildFiniteCarrierLeviCivitaStillBlocked
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grSchwarzschildFiniteCarrierLeviCivitaStillBlocked
grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierLeviCivitaStillBlocked = refl

grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierNoLeviCivitaPromotion :
  GRProofArchitectureAggregationTest.ricciSchwarzschildFiniteCarrierNoLeviCivitaPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedCarrierConnectionIsLeviCivitaPromotedIsFalse
    Ricci.canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierNoLeviCivitaPromotion = refl

grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierZeroConsumersTypeable :
  GRProofArchitectureAggregationTest.ricciSchwarzschildFiniteCarrierZeroConsumersTypeable
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grSchwarzschildFiniteCarrierRicciBianchiConsumersType
grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierZeroConsumersTypeable = refl

grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierNoSourcedEinsteinPromotion :
  GRProofArchitectureAggregationTest.ricciSchwarzschildFiniteCarrierNoSourcedEinsteinPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRSchwarzschildFiniteCarrierLeviCivitaReceipt.sourcedEinsteinPromotedIsFalse
    Ricci.canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
grProofArchitectureAggregationRicciSchwarzschildFiniteCarrierNoSourcedEinsteinPromotion = refl

grProofArchitectureAggregationRicciExtractionKernelDependencyName :
  GRProofArchitectureAggregationTest.ricciExtractionKernelDependencyName
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelDependencyNameIsCanonical
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionKernelDependencyName = refl

grProofArchitectureAggregationRicciExtractionSelectedPairIdentityDependencyName :
  GRProofArchitectureAggregationTest.ricciExtractionSelectedPairIdentityDependencyName
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityDependencyNameIsCanonical
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionSelectedPairIdentityDependencyName = refl

grProofArchitectureAggregationRicciExtractionKernelNotPromoted :
  GRProofArchitectureAggregationTest.ricciExtractionKernelNotPromotedHere
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.christoffelC0StabilityKernelPromotedHereIsFalse
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionKernelNotPromoted = refl

grProofArchitectureAggregationRicciExtractionSelectedPairIdentityNotPromoted :
  GRProofArchitectureAggregationTest.ricciExtractionSelectedPairIdentityNotPromotedHere
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.selectedPairIdentityPromotedHereIsFalse
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionSelectedPairIdentityNotPromoted = refl

grProofArchitectureAggregationRicciExtractionShellAInterval80 :
  GRProofArchitectureAggregationTest.ricciExtractionShellAIntervalConstant80
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellASafeIntervalRicciContinuityConstantIs80
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionShellAInterval80 = refl

grProofArchitectureAggregationRicciExtractionShellBInterval220 :
  GRProofArchitectureAggregationTest.ricciExtractionShellBIntervalConstant220
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.shellBSafeIntervalRicciContinuityConstantIs220
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionShellBInterval220 = refl

grProofArchitectureAggregationRicciExtractionConservative640 :
  GRProofArchitectureAggregationTest.ricciExtractionConservativeConstant640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciExtractionReadinessDependencyReceipt.conservativeRicciExtractionConstantIs640
    Ricci.canonicalGRDiscreteRicciExtractionReadinessDependencyReceipt
grProofArchitectureAggregationRicciExtractionConservative640 = refl

grProofArchitectureAggregationRicciContractionSharpNumerator1280 :
  GRProofArchitectureAggregationTest.ricciContractionSharpNumerator1280
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciSharpCRNumeratorIs1280
grProofArchitectureAggregationRicciContractionSharpNumerator1280 = refl

grProofArchitectureAggregationRicciContractionSharpDenominator27 :
  GRProofArchitectureAggregationTest.ricciContractionSharpDenominator27
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciSharpCRDenominatorIs27
grProofArchitectureAggregationRicciContractionSharpDenominator27 = refl

grProofArchitectureAggregationRicciContractionRoundedConstant48 :
  GRProofArchitectureAggregationTest.ricciContractionRoundedConstant48
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciContinuityRoundedConstantIs48
grProofArchitectureAggregationRicciContractionRoundedConstant48 = refl

grProofArchitectureAggregationRicciContractionPointShell48 :
  GRProofArchitectureAggregationTest.ricciContractionPointShellConstant48
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShellRicciContinuityConstantIs48
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionPointShell48 = refl

grProofArchitectureAggregationRicciContractionPointShell48Only :
  GRProofArchitectureAggregationTest.ricciContractionPointShell48Only
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.pointShell48OnlyIsTrue
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionPointShell48Only = refl

grProofArchitectureAggregationRicciContractionShellAInterval80 :
  GRProofArchitectureAggregationTest.ricciContractionShellAIntervalConstant80
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellASafeIntervalRicciContinuityConstantIs80
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionShellAInterval80 = refl

grProofArchitectureAggregationRicciContractionShellBInterval220 :
  GRProofArchitectureAggregationTest.ricciContractionShellBIntervalConstant220
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.shellBSafeIntervalRicciContinuityConstantIs220
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionShellBInterval220 = refl

grProofArchitectureAggregationRicciContractionConservativeConstant640 :
  GRProofArchitectureAggregationTest.ricciContractionConservativeConstant640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.grDiscreteRicciExistingConservativeConstantIs640
grProofArchitectureAggregationRicciContractionConservativeConstant640 = refl

grProofArchitectureAggregationRicciContractionConservativeExtraction640 :
  GRProofArchitectureAggregationTest.ricciContractionConservativeExtractionConstant640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.conservativeCRExtractionConstantIs640
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionConservativeExtraction640 = refl

grProofArchitectureAggregationRicciContractionOptionalTightNumerator112 :
  GRProofArchitectureAggregationTest.ricciContractionOptionalTightNumerator112
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumeratorIs112
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionOptionalTightNumerator112 = refl

grProofArchitectureAggregationRicciContractionOptionalTightNoPromotion :
  GRProofArchitectureAggregationTest.ricciContractionOptionalTightNumeratorNoPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.optionalTightRicciNumeratorUsedAsPromotionIsFalse
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionOptionalTightNoPromotion = refl

grProofArchitectureAggregationRicciContractionNoConvergencePromotion :
  GRProofArchitectureAggregationTest.ricciContractionConstantNoConvergencePromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Ricci.GRDiscreteRicciContractionContinuityConstantReceipt.constantPromotedAsRicciConvergenceIsFalse
    Ricci.canonicalGRDiscreteRicciContractionContinuityConstantReceipt
grProofArchitectureAggregationRicciContractionNoConvergencePromotion = refl

grProofArchitectureAggregationRationalHalfWitness :
  GRProofArchitectureAggregationTest.selectedRationalHalfWitnessIsCanonical
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessIsCanonical
    Bianchi.canonicalSelectedRationalUndoubledChristoffelLift
grProofArchitectureAggregationRationalHalfWitness = refl

grProofArchitectureAggregationSelectedRationalPairIdentityRouteStaged :
  GRProofArchitectureAggregationTest.selectedRationalPairIdentityRouteStaged
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.grSelectedRationalSelectedPairConnectionIdentityAvailable
grProofArchitectureAggregationSelectedRationalPairIdentityRouteStaged = refl

grProofArchitectureAggregationSelectedRationalPairFiniteRObstructionStillPresent :
  GRProofArchitectureAggregationTest.selectedRationalPairFiniteRObstructionStillPresent
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.finiteRCarrierOddHalvingObstructionStillPresentIsTrue
    Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
grProofArchitectureAggregationSelectedRationalPairFiniteRObstructionStillPresent = refl

grProofArchitectureAggregationSelectedRationalPairNoFiniteRChristoffelPromotion :
  GRProofArchitectureAggregationTest.selectedRationalPairNoFiniteRChristoffelPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesFiniteRChristoffelIsFalse
    Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
grProofArchitectureAggregationSelectedRationalPairNoFiniteRChristoffelPromotion = refl

grProofArchitectureAggregationSelectedRationalPairNoContinuumBianchiPromotion :
  GRProofArchitectureAggregationTest.selectedRationalPairNoContinuumBianchiPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRoutePromotesContinuumBianchiIsFalse
    Bianchi.canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
grProofArchitectureAggregationSelectedRationalPairNoContinuumBianchiPromotion = refl

grProofArchitectureAggregationSelectedRationalPairKeepsLeviCivitaBlocked :
  GRProofArchitectureAggregationTest.selectedRationalPairKeepsLeviCivitaBlocked
    canonicalGRProofArchitectureAggregationTest
  ≡
  Bianchi.grSelectedRationalSelectedPairKeepsLeviCivitaBlocked
grProofArchitectureAggregationSelectedRationalPairKeepsLeviCivitaBlocked = refl

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

grProofArchitectureAggregationMachineCheckedChristoffelL_Ricci640 :
  GRProofArchitectureAggregationTest.machineCheckedChristoffelL_Ricci640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.machineCheckedChristoffelL_RicciIs640
grProofArchitectureAggregationMachineCheckedChristoffelL_Ricci640 = refl

grProofArchitectureAggregationMachineCheckedOptionalSharpL_Ricci112 :
  GRProofArchitectureAggregationTest.machineCheckedChristoffelOptionalSharpL_Ricci112
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.machineCheckedChristoffelOptionalSharpL_RicciIs112
grProofArchitectureAggregationMachineCheckedOptionalSharpL_Ricci112 = refl

grProofArchitectureAggregationMachineCheckedConservativeShellCGammaUsed :
  GRProofArchitectureAggregationTest.machineCheckedConservativeShellCGammaUsed
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.MachineCheckedChristoffelC0ConstantReceipt.conservativeShellCGammaUsedIsTrue
    Continuum.canonicalMachineCheckedChristoffelC0ConstantReceipt
grProofArchitectureAggregationMachineCheckedConservativeShellCGammaUsed = refl

grProofArchitectureAggregationCorrectedTightShellA_LGamma44 :
  GRProofArchitectureAggregationTest.correctedTightShellA_LGamma
    canonicalGRProofArchitectureAggregationTest
  ≡
  44
grProofArchitectureAggregationCorrectedTightShellA_LGamma44 = refl

grProofArchitectureAggregationCorrectedTightShellA_DocumentationOnly :
  GRProofArchitectureAggregationTest.correctedTightShellA_LGammaDocumentationOnly
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationCorrectedTightShellA_DocumentationOnly = refl

grProofArchitectureAggregationCorrectedTightShellA_PreservesFinal48 :
  GRProofArchitectureAggregationTest.correctedTightShellA_LGammaPreservesFinal48
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationCorrectedTightShellA_PreservesFinal48 = refl

grProofArchitectureAggregationCorrectedTightShellA_PreservesLegacy72 :
  GRProofArchitectureAggregationTest.correctedTightShellA_LGammaPreservesLegacy72
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationCorrectedTightShellA_PreservesLegacy72 = refl

grProofArchitectureAggregationSelectedChristoffelC0ShellA_TightCGammaIsOne :
  GRProofArchitectureAggregationTest.selectedChristoffelC0ShellA_TightCGammaIsOne
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0Tight_C_GammaIs1
grProofArchitectureAggregationSelectedChristoffelC0ShellA_TightCGammaIsOne = refl

grProofArchitectureAggregationSelectedChristoffelC0ShellB_ConservativeCGammaIsTwo :
  GRProofArchitectureAggregationTest.selectedChristoffelC0ShellB_ConservativeCGammaIsTwo
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0Conservative_C_GammaIs2
grProofArchitectureAggregationSelectedChristoffelC0ShellB_ConservativeCGammaIsTwo = refl

grProofArchitectureAggregationSelectedChristoffelC0FormulaStabilityConstant48 :
  GRProofArchitectureAggregationTest.selectedChristoffelC0FormulaStabilityConstant48
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0FormulaStabilityIs48
grProofArchitectureAggregationSelectedChristoffelC0FormulaStabilityConstant48 = refl

grProofArchitectureAggregationSelectedChristoffelC0RicciIntervalNumerator48 :
  GRProofArchitectureAggregationTest.selectedChristoffelC0RicciIntervalNumerator48
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0RicciBoundNumeratorIs48
grProofArchitectureAggregationSelectedChristoffelC0RicciIntervalNumerator48 = refl

grProofArchitectureAggregationSelectedChristoffelC0RicciIntervalDenominator640 :
  GRProofArchitectureAggregationTest.selectedChristoffelC0RicciIntervalDenominator640
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0RicciBoundDenominatorIs640
grProofArchitectureAggregationSelectedChristoffelC0RicciIntervalDenominator640 = refl

grProofArchitectureAggregationSelectedChristoffelC0PrimitivePairIdentity :
  GRProofArchitectureAggregationTest.selectedChristoffelC0PrimitivePairIdentity
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0PrimitivePairIdentity
grProofArchitectureAggregationSelectedChristoffelC0PrimitivePairIdentity = refl

grProofArchitectureAggregationZeroEpsilonSelectedChristoffelC0EqualityBridge :
  GRProofArchitectureAggregationTest.zeroEpsilonSelectedChristoffelC0EqualityBridge
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound
    0
    0
grProofArchitectureAggregationZeroEpsilonSelectedChristoffelC0EqualityBridge = refl

grProofArchitectureAggregationSelectedChristoffelC0NoArbitraryEqualityPromotion :
  GRProofArchitectureAggregationTest.selectedChristoffelC0NoArbitraryEqualityPromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  Continuum.SelectedSymbolicRationalChristoffelC0Primitive.arbitraryConnectionEqualityPromotedIsFalse
    Continuum.canonicalSelectedSymbolicRationalChristoffelC0Primitive
grProofArchitectureAggregationSelectedChristoffelC0NoArbitraryEqualityPromotion = refl

grProofArchitectureAggregationNextAnalyticKernelTrancheCanonical :
  GRProofArchitectureAggregationTest.nextAnalyticKernelTrancheIsCanonical
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelTrancheCanonical = refl

grProofArchitectureAggregationNextAnalyticKernelStillOpen :
  GRProofArchitectureAggregationTest.nextAnalyticKernelStillOpen
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.analyticKernelStillOpenIsTrue
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelStillOpen = refl

grProofArchitectureAggregationNextAnalyticKernelDependencyName :
  GRProofArchitectureAggregationTest.nextAnalyticKernelDependencyName
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.kernelDependencyNameIsCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelDependencyName = refl

grProofArchitectureAggregationNextAnalyticKernelGaugeToolkitTargets :
  GRProofArchitectureAggregationTest.nextAnalyticKernelGaugeToolkitTargets
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.gaugeToolkitTargetVarsAreCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelGaugeToolkitTargets = refl

grProofArchitectureAggregationNextAnalyticKernelShellADenominatorTargets :
  GRProofArchitectureAggregationTest.nextAnalyticKernelShellADenominatorTargets
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.shellADenominatorTargetVarsAreCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelShellADenominatorTargets = refl

grProofArchitectureAggregationNextAnalyticKernelChristoffelDerivativeTargets :
  GRProofArchitectureAggregationTest.nextAnalyticKernelChristoffelDerivativeTargets
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelDerivativeBoundsTargetVarsAreCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelChristoffelDerivativeTargets = refl

grProofArchitectureAggregationNextAnalyticKernelChristoffelC0Targets :
  GRProofArchitectureAggregationTest.nextAnalyticKernelChristoffelC0Targets
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.christoffelC0StabilityTargetVarsAreCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelChristoffelC0Targets = refl

grProofArchitectureAggregationNextAnalyticKernelRicciExtractionTargets :
  GRProofArchitectureAggregationTest.nextAnalyticKernelRicciExtractionTargets
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.ricciPerturbationExtractionTargetVarsAreCanonical
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelRicciExtractionTargets = refl

grProofArchitectureAggregationNextAnalyticKernelFinalShellA_LGamma48 :
  Continuum.MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
    (GRProofArchitectureNextAnalyticKernelTrancheReceipt.machineCheckedChristoffelC0Constants
      (GRProofArchitectureAggregationTest.nextAnalyticKernelTranche
        canonicalGRProofArchitectureAggregationTest))
  ≡
  48
grProofArchitectureAggregationNextAnalyticKernelFinalShellA_LGamma48 =
  GRProofArchitectureAggregationTest.nextAnalyticKernelFinalShellA_LGammaIs48
    canonicalGRProofArchitectureAggregationTest

grProofArchitectureAggregationNextAnalyticKernelFinalShellASelectedFormula48 :
  Continuum.SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
    (GRProofArchitectureNextAnalyticKernelTrancheReceipt.selectedChristoffelC0Constants
      (GRProofArchitectureAggregationTest.nextAnalyticKernelTranche
        canonicalGRProofArchitectureAggregationTest))
  ≡
  48
grProofArchitectureAggregationNextAnalyticKernelFinalShellASelectedFormula48 =
  GRProofArchitectureAggregationTest.nextAnalyticKernelFinalShellASelectedFormula48
    canonicalGRProofArchitectureAggregationTest

grProofArchitectureAggregationNextAnalyticKernelRicciPointCR48 :
  Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.pointCRConstant
    (GRProofArchitectureNextAnalyticKernelTrancheReceipt.ricciFinitePerturbationReceipt
      (GRProofArchitectureAggregationTest.nextAnalyticKernelTranche
        canonicalGRProofArchitectureAggregationTest))
  ≡
  48
grProofArchitectureAggregationNextAnalyticKernelRicciPointCR48 =
  GRProofArchitectureAggregationTest.nextAnalyticKernelRicciPointCR48
    canonicalGRProofArchitectureAggregationTest

grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_LGamma44 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelCorrectedTightShellA_LGamma44
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaIs44
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_LGamma44 = refl

grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_DocumentationOnly :
  GRProofArchitectureAggregationTest.nextAnalyticKernelCorrectedTightShellA_DocumentationOnly
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaDocumentationOnlyIsTrue
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_DocumentationOnly = refl

grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_PreservesFinal48 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelCorrectedTightShellA_PreservesFinal48
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesFinal48IsTrue
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_PreservesFinal48 = refl

grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_PreservesLegacy72 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelCorrectedTightShellA_PreservesLegacy72
    canonicalGRProofArchitectureAggregationTest
  ≡
  GRProofArchitectureNextAnalyticKernelTrancheReceipt.correctedTightShellA_LGammaPreservesLegacy72IsTrue
    canonicalGRProofArchitectureNextAnalyticKernelTrancheReceipt
grProofArchitectureAggregationNextAnalyticKernelCorrectedTightShellA_PreservesLegacy72 = refl

grProofArchitectureAggregationNextAnalyticKernelShellA_LGamma72 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelShellA_LGammaIs72
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelShellA_LGamma72 = refl

grProofArchitectureAggregationNextAnalyticKernelShellA_CR80 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelShellA_CRIs80
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelShellA_CR80 = refl

grProofArchitectureAggregationNextAnalyticKernelShellA_CPrimeDenominator27 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelShellA_CPrimeDenominatorIs27
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelShellA_CPrimeDenominator27 = refl

grProofArchitectureAggregationNextAnalyticKernelSchwarzschildShellAEnvelope640 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelSchwarzschildShellAEnvelope640
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelSchwarzschildShellAEnvelope640 = refl

grProofArchitectureAggregationNextAnalyticKernelRicciPerturbationBound640 :
  GRProofArchitectureAggregationTest.nextAnalyticKernelRicciPerturbationBound640
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelRicciPerturbationBound640 = refl

grProofArchitectureAggregationNextAnalyticKernelNoRicciConvergencePromotion :
  GRProofArchitectureAggregationTest.nextAnalyticKernelNoRicciConvergencePromotion
    canonicalGRProofArchitectureAggregationTest
  ≡
  true
grProofArchitectureAggregationNextAnalyticKernelNoRicciConvergencePromotion = refl

grProofArchitectureAggregationConservativeGRRouteRows :
  GRProofArchitectureAggregationTest.conservativeGRRouteRows
    canonicalGRProofArchitectureAggregationTest
  ≡
  "angular ledger=13 nonzero / 51 zero"
  ∷ "bracket_le=8 via r_max=4M and bracket_le=2*r_max"
  ∷ "theta-shell/cot-bound required for angular cot slots"
  ∷ "C_shell=8 Γ background shell bound"
  ∷ "h_dΓ_tight=11/2"
  ∷ "derivTermBound_44"
  ∷ "productTermBound via 176<=640"
  ∷ "fail-closed/no promotion"
  ∷ []
grProofArchitectureAggregationConservativeGRRouteRows = refl

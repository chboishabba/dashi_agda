module DASHI.Physics.Closure.ClaySprintSixtyNineYMTemporalFaceFactorizationWorkplanReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSixtyEightYMTemporalSupportNonCreationReceipt
  as Sprint68YM

------------------------------------------------------------------------
-- Sprint 69 YM temporal-face factorization workplan receipt.
--
-- This receipt consumes Sprint 68's closed support-range node and assigns the
-- next proof work into six narrow lanes.  It deliberately does not claim the
-- analytic factorization theorem.  The point is to keep the shortest YM path
-- to Clay normalized: support non-creation is an input; temporal-face
-- factorization is the next open theorem surface.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint69YMWorkerLane : Set where
  supportNonCreationIntegrator :
    Sprint69YMWorkerLane
  temporalFacePOUBuilder :
    Sprint69YMWorkerLane
  slabActionAdditivityAuditor :
    Sprint69YMWorkerLane
  entropyTransferAuditor :
    Sprint69YMWorkerLane
  allDiameterWeightedKPAuditor :
    Sprint69YMWorkerLane
  balabanOSMassGapBoundaryAuditor :
    Sprint69YMWorkerLane

canonicalSprint69YMWorkerLanes :
  List Sprint69YMWorkerLane
canonicalSprint69YMWorkerLanes =
  supportNonCreationIntegrator
  ∷ temporalFacePOUBuilder
  ∷ slabActionAdditivityAuditor
  ∷ entropyTransferAuditor
  ∷ allDiameterWeightedKPAuditor
  ∷ balabanOSMassGapBoundaryAuditor
  ∷ []

data Sprint69YMClosedInput : Set where
  sprint68TemporalSupportNonCreationInput :
    Sprint69YMClosedInput
  nearestNeighbourKernelRange :
    Sprint69YMClosedInput
  l2SpatialEntropyArithmetic :
    Sprint69YMClosedInput

canonicalSprint69YMClosedInputs :
  List Sprint69YMClosedInput
canonicalSprint69YMClosedInputs =
  sprint68TemporalSupportNonCreationInput
  ∷ nearestNeighbourKernelRange
  ∷ l2SpatialEntropyArithmetic
  ∷ []

data Sprint69YMLeakageDiagnostic : Set where
  productCutoffFactorizationWithLeakageRecorded :
    Sprint69YMLeakageDiagnostic
  boundaryCorrectionSmallRecorded :
    Sprint69YMLeakageDiagnostic
  safeLeakageBound10785Recorded :
    Sprint69YMLeakageDiagnostic
  weightedKPConvergesConditionalArithmeticRecorded :
    Sprint69YMLeakageDiagnostic
  closedPassFailNumericalExamplesRecorded :
    Sprint69YMLeakageDiagnostic

canonicalSprint69YMLeakageDiagnostics :
  List Sprint69YMLeakageDiagnostic
canonicalSprint69YMLeakageDiagnostics =
  productCutoffFactorizationWithLeakageRecorded
  ∷ boundaryCorrectionSmallRecorded
  ∷ safeLeakageBound10785Recorded
  ∷ weightedKPConvergesConditionalArithmeticRecorded
  ∷ closedPassFailNumericalExamplesRecorded
  ∷ []

data Sprint69YMOpenGate : Set where
  gateTemporalFaceFactorization :
    Sprint69YMOpenGate
  gateTemporalFaceFactorizationFromSupportNonCreation :
    Sprint69YMOpenGate
  gateAnisotropicPartitionOfUnity :
    Sprint69YMOpenGate
  gateAnisotropicBalabanPartitionIdentity :
    Sprint69YMOpenGate
  gateTemporalFaceMeasureProduct :
    Sprint69YMOpenGate
  gateProductCutoffFactorizationWithLeakage :
    Sprint69YMOpenGate
  gateTemporalMeasureFactorizationWithLeakage :
    Sprint69YMOpenGate
  gateBoundaryCorrectionSmall :
    Sprint69YMOpenGate
  gateLinkVariableDisjointnessForTemporalFaces :
    Sprint69YMOpenGate
  gateBalabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
    Sprint69YMOpenGate
  gateLeakageControlledWeightedKPCloses :
    Sprint69YMOpenGate
  gateWeightedKPConverges :
    Sprint69YMOpenGate
  gateSlabActionAdditivity :
    Sprint69YMOpenGate
  gateTemporalQuotientEntropyHalvingL2 :
    Sprint69YMOpenGate
  gateAnisotropicL2WeightedKPCloses :
    Sprint69YMOpenGate
  gateEntropyCountTransfer :
    Sprint69YMOpenGate
  gateAllDiameterWeightedKP :
    Sprint69YMOpenGate
  gateBalabanSmallFieldSurvival :
    Sprint69YMOpenGate
  gateSmallFieldBoundsSurviveAnisotropicBlocking :
    Sprint69YMOpenGate
  gateTransferMatrixCompatibility :
    Sprint69YMOpenGate
  gateTemporalTransferMatrixCompatibleWithSpatialBlocking :
    Sprint69YMOpenGate
  gateLatticeMassGapFromAnisotropicKP :
    Sprint69YMOpenGate
  gateContinuumMassGapTransfer :
    Sprint69YMOpenGate
  gateOSWightmanReconstruction :
    Sprint69YMOpenGate
  gateMassGapSurvival :
    Sprint69YMOpenGate

canonicalSprint69YMOpenGates :
  List Sprint69YMOpenGate
canonicalSprint69YMOpenGates =
  gateTemporalFaceFactorization
  ∷ gateTemporalFaceFactorizationFromSupportNonCreation
  ∷ gateAnisotropicPartitionOfUnity
  ∷ gateAnisotropicBalabanPartitionIdentity
  ∷ gateTemporalFaceMeasureProduct
  ∷ gateProductCutoffFactorizationWithLeakage
  ∷ gateTemporalMeasureFactorizationWithLeakage
  ∷ gateBoundaryCorrectionSmall
  ∷ gateLinkVariableDisjointnessForTemporalFaces
  ∷ gateLeakageControlledWeightedKPCloses
  ∷ gateBalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
  ∷ gateWeightedKPConverges
  ∷ gateSlabActionAdditivity
  ∷ gateTemporalQuotientEntropyHalvingL2
  ∷ gateAnisotropicL2WeightedKPCloses
  ∷ gateEntropyCountTransfer
  ∷ gateAllDiameterWeightedKP
  ∷ gateBalabanSmallFieldSurvival
  ∷ gateSmallFieldBoundsSurviveAnisotropicBlocking
  ∷ gateTransferMatrixCompatibility
  ∷ gateTemporalTransferMatrixCompatibleWithSpatialBlocking
  ∷ gateLatticeMassGapFromAnisotropicKP
  ∷ gateContinuumMassGapTransfer
  ∷ gateOSWightmanReconstruction
  ∷ gateMassGapSurvival
  ∷ []

data Sprint69YMRouteDecision : Set where
  shortestRouteIsYM :
    Sprint69YMRouteDecision
  nextTheoremIsTemporalFaceFactorization :
    Sprint69YMRouteDecision
  supportNonCreationIsInputNotFactorization :
    Sprint69YMRouteDecision
  etaFourKPArithmeticIsConditional :
    Sprint69YMRouteDecision
  spatialD3Controls4DOnlyAfterTemporalFactorization :
    Sprint69YMRouteDecision
  l2D4SpacetimeCountBlockedWithoutFactorization :
    Sprint69YMRouteDecision
  leakageBudgetIsLoadBearing :
    Sprint69YMRouteDecision
  safeLeakageBoundAvoidsThresholdEquality :
    Sprint69YMRouteDecision
  perFaceLeakageBudgetIsTight :
    Sprint69YMRouteDecision
  boundaryCorrectionSmallIsNextAnalyticHinge :
    Sprint69YMRouteDecision
  noYangMillsPromotion :
    Sprint69YMRouteDecision

canonicalSprint69YMRouteDecisions :
  List Sprint69YMRouteDecision
canonicalSprint69YMRouteDecisions =
  shortestRouteIsYM
  ∷ nextTheoremIsTemporalFaceFactorization
  ∷ supportNonCreationIsInputNotFactorization
  ∷ etaFourKPArithmeticIsConditional
  ∷ spatialD3Controls4DOnlyAfterTemporalFactorization
  ∷ l2D4SpacetimeCountBlockedWithoutFactorization
  ∷ leakageBudgetIsLoadBearing
  ∷ safeLeakageBoundAvoidsThresholdEquality
  ∷ perFaceLeakageBudgetIsTight
  ∷ boundaryCorrectionSmallIsNextAnalyticHinge
  ∷ noYangMillsPromotion
  ∷ []

data Sprint69YMPromotion : Set where

sprint69YMPromotionImpossibleHere :
  Sprint69YMPromotion →
  ⊥
sprint69YMPromotionImpossibleHere ()

sprint69YMWorkerAssignment : String
sprint69YMWorkerAssignment =
  "Six lanes: integrate Sprint 68 support non-creation; construct temporal-face POU; audit slab action additivity; transfer eta=4 into weighted KP; lift to all diameters; keep Balaban/OS/mass-gap boundary false until those theorems exist."

sprint69YMTheoremTarget : String
sprint69YMTheoremTarget =
  "TemporalFaceFactorizationFromSupportNonCreation: support non-creation is combinatorial; Sprint 69 must prove the analytic/measure-theoretic step that top-face and bottom-face large-field sectors factor from the spatial slab integral in the anisotropic Balaban partition."

sprint69YMLemmaLadder : String
sprint69YMLemmaLadder =
  "Ordered lemma ladder: TemporalFacesDisjointForAdmissiblePolymers; NoTemporalCrossCoupling; ProductCutoffFactorizationWithLeakage; LocalGaugeActionDecomposition; MixedPlaquettesAreTransferMatrixNotCorrection; LinkVariableDisjointnessForTemporalFaces; TemporalMeasureFactorizationWithLeakage; BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix; LeakageControlledWeightedKPCloses; AllDiameterWeightedKP; SmallFieldBoundsSurviveAnisotropicBlocking; TemporalTransferMatrixCompatibleWithSpatialBlocking; LatticeMassGapFromAnisotropicKP; ContinuumMassGapTransfer; OSWightmanReconstruction; MassGapSurvival."

sprint69YMConditionalKPBoundary : String
sprint69YMConditionalKPBoundary =
  "The arithmetic eta=4, q=0.23178189475262734, eta*q=0.9271275790105094<1 makes the ideal weighted KP geometric tail summable, but it is usable only after temporal-face factorization, entropy-count transfer, and a strict leakage bound are proved."

sprint69YMLeakageBudget : String
sprint69YMLeakageBudget =
  "Leakage budget: etaSpatial*q=0.9271275790105094, margin=0.07287242098949065, exact threshold leakageFactor=1/(4q)=1.078600208471055, safe formal target leakageFactor<=1.0785. If three independent faces spend leakage multiplicatively, the per-face budget is 0.025542115281578237 = 2.5542115281578237 percent, so the practical theorem target is <=2.5 percent per face."

sprint69YMLeakageExamples : String
sprint69YMLeakageExamples =
  "Leakage examples: (1.025)^3 * 4q = 0.998414998 survives; (1.026)^3 * 4q = 1.001340040 fails; (1.03)^3 * 4q = 1.013097338 fails."

sprint69YMBoundaryCorrectionTarget : String
sprint69YMBoundaryCorrectionTarget =
  "Corrected bookkeeping: mixed spatial-temporal plaquettes touching a temporal face are transfer-matrix face action, not residual correction. The remaining analytic hinge is link-variable disjointness plus TemporalMeasureFactorizationWithLeakage, followed by BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix."

sprint69YMD3D4Boundary : String
sprint69YMD3D4Boundary =
  "The L=2,d=3 spatial-slab row eta=4 closes KP arithmetic, but the L=2,d=4 spacetime row eta=8 remains blocked. Therefore 4D YM may consume d=3 only after temporal transfer-matrix factorization quotients out the temporal face count."

sprint69YMBoundary : String
sprint69YMBoundary =
  "Sprint 69 assigns the shortest in-repo YM path to the exact temporal-face factorization ladder with constant tracking. Later Sprint 70/71 bookkeeping records mixed plaquettes as transfer-matrix face action, not residual correction. This receipt still does not prove temporal-face factorization, product cutoff factorization with leakage, link-variable disjointness, temporal measure factorization with leakage, Balaban/transfer-matrix compatibility, anisotropic Balaban partition identity, temporal quotient entropy halving, all-diameter weighted KP, small-field bound survival, lattice mass gap, continuum transfer, or Clay/YM promotion."

record ClaySprintSixtyNineYMTemporalFaceFactorizationWorkplanReceipt : Set₁ where
  field
    sprint68YMNoPromotion :
      Sprint68YM.clayYangMillsPromoted ≡ false

    sprint68TemporalSupportNonCreation :
      Bool
    sprint68TemporalSupportNonCreationIsTrue :
      sprint68TemporalSupportNonCreation ≡ true

    supportNonCreationIsOnlyInput :
      Bool
    supportNonCreationIsOnlyInputIsTrue :
      supportNonCreationIsOnlyInput ≡ true

    temporalFacesDisjointForAdmissiblePolymers :
      Bool
    temporalFacesDisjointForAdmissiblePolymersIsTrue :
      temporalFacesDisjointForAdmissiblePolymers ≡ true

    temporalFaceFactorizationProved :
      Bool
    temporalFaceFactorizationProvedIsFalse :
      temporalFaceFactorizationProved ≡ false

    temporalFaceFactorizationFromSupportNonCreationProved :
      Bool
    temporalFaceFactorizationFromSupportNonCreationProvedIsFalse :
      temporalFaceFactorizationFromSupportNonCreationProved ≡ false

    noTemporalCrossCouplingProved :
      Bool
    noTemporalCrossCouplingProvedIsFalse :
      noTemporalCrossCouplingProved ≡ false

    productCutoffFactorizationProved :
      Bool
    productCutoffFactorizationProvedIsFalse :
      productCutoffFactorizationProved ≡ false

    productCutoffFactorizationWithLeakageProved :
      Bool
    productCutoffFactorizationWithLeakageProvedIsFalse :
      productCutoffFactorizationWithLeakageProved ≡ false

    localGaugeActionDecompositionProved :
      Bool
    localGaugeActionDecompositionProvedIsFalse :
      localGaugeActionDecompositionProved ≡ false

    boundaryCorrectionSmallProved :
      Bool
    boundaryCorrectionSmallProvedIsFalse :
      boundaryCorrectionSmallProved ≡ false

    temporalMeasureFactorizationWithLeakageProved :
      Bool
    temporalMeasureFactorizationWithLeakageProvedIsFalse :
      temporalMeasureFactorizationWithLeakageProved ≡ false

    anisotropicPartitionOfUnityProved :
      Bool
    anisotropicPartitionOfUnityProvedIsFalse :
      anisotropicPartitionOfUnityProved ≡ false

    slabActionAdditivityProved :
      Bool
    slabActionAdditivityProvedIsFalse :
      slabActionAdditivityProved ≡ false

    entropyCountTransferredToWeightedKP :
      Bool
    entropyCountTransferredToWeightedKPIsFalse :
      entropyCountTransferredToWeightedKP ≡ false

    etaFourArithmetic :
      Scalar
    etaFourArithmeticIsCanonical :
      etaFourArithmetic ≡ "4 * 0.23178189475262734 = 0.9271275790105094 < 1"

    weightedKPConvergesDiagnostic :
      Scalar
    weightedKPConvergesDiagnosticIsCanonical :
      weightedKPConvergesDiagnostic ≡ "ideal weighted KP geometric ratio eta*q = 0.9271275790105094 < 1"

    weightedKPConvergesConditionally :
      Bool
    weightedKPConvergesConditionallyIsTrue :
      weightedKPConvergesConditionally ≡ true

    etaSpatial :
      Scalar
    etaSpatialIsFour :
      etaSpatial ≡ "4"

    etaSpatialTimesQ :
      Scalar
    etaSpatialTimesQIsCanonical :
      etaSpatialTimesQ ≡ "0.9271275790105094"

    kpMargin :
      Scalar
    kpMarginIsCanonical :
      kpMargin ≡ "0.07287242098949065"

    leakageMaxAllowed :
      Scalar
    leakageMaxAllowedIsCanonical :
      leakageMaxAllowed ≡ "1.078600208471055"

    leakageSafeFormalBound :
      Scalar
    leakageSafeFormalBoundIsCanonical :
      leakageSafeFormalBound ≡ "1.0785"

    leakageSafeFormalBoundProduct :
      Scalar
    leakageSafeFormalBoundProductIsCanonical :
      leakageSafeFormalBoundProduct ≡ "1.0785 * 4q = 0.9999070939628344 < 1"

    perFaceLeakageBudget :
      Scalar
    perFaceLeakageBudgetIsCanonical :
      perFaceLeakageBudget ≡ "0.025542115281578237"

    perFaceLeakageBudgetPct :
      Scalar
    perFaceLeakageBudgetPctIsCanonical :
      perFaceLeakageBudgetPct ≡ "2.5542115281578237%"

    practicalPerFaceLeakageTargetPct :
      Scalar
    practicalPerFaceLeakageTargetPctIsCanonical :
      practicalPerFaceLeakageTargetPct ≡ "2.5%"

    leakageTwoPointFivePctExample :
      Scalar
    leakageTwoPointFivePctExampleIsCanonical :
      leakageTwoPointFivePctExample ≡ "(1.025)^3 * 4q = 0.998414998"

    leakageTwoPointSixPctExample :
      Scalar
    leakageTwoPointSixPctExampleIsCanonical :
      leakageTwoPointSixPctExample ≡ "(1.026)^3 * 4q = 1.001340040"

    leakageThreePctExample :
      Scalar
    leakageThreePctExampleIsCanonical :
      leakageThreePctExample ≡ "(1.03)^3 * 4q = 1.013097338"

    qHeadroomBeforeEtaFourFails :
      Scalar
    qHeadroomBeforeEtaFourFailsIsCanonical :
      qHeadroomBeforeEtaFourFails ≡ "0.018218105247372662"

    leakageBoundProved :
      Bool
    leakageBoundProvedIsFalse :
      leakageBoundProved ≡ false

    leakageSafeBoundProved :
      Bool
    leakageSafeBoundProvedIsFalse :
      leakageSafeBoundProved ≡ false

    leakageControlledWeightedKPCloses :
      Bool
    leakageControlledWeightedKPClosesIsFalse :
      leakageControlledWeightedKPCloses ≡ false

    l2D3SpatialSlabEtaQ :
      Scalar
    l2D3SpatialSlabEtaQIsCanonical :
      l2D3SpatialSlabEtaQ ≡ "0.9271275790105094"

    l2D4SpacetimeEtaQ :
      Scalar
    l2D4SpacetimeEtaQIsCanonical :
      l2D4SpacetimeEtaQ ≡ "1.85425516"

    d3SpatialRowTransferredTo4D :
      Bool
    d3SpatialRowTransferredTo4DIsFalse :
      d3SpatialRowTransferredTo4D ≡ false

    temporalQuotientEntropyHalvingL2 :
      Bool
    temporalQuotientEntropyHalvingL2IsFalse :
      temporalQuotientEntropyHalvingL2 ≡ false

    anisotropicL2WeightedKPCloses :
      Bool
    anisotropicL2WeightedKPClosesIsFalse :
      anisotropicL2WeightedKPCloses ≡ false

    etaFourArithmeticPromotedToKP :
      Bool
    etaFourArithmeticPromotedToKPIsFalse :
      etaFourArithmeticPromotedToKP ≡ false

    allDiameterWeightedKP :
      Bool
    allDiameterWeightedKPIsFalse :
      allDiameterWeightedKP ≡ false

    balabanRGTransfer :
      Bool
    balabanRGTransferIsFalse :
      balabanRGTransfer ≡ false

    osWightmanReconstruction :
      Bool
    osWightmanReconstructionIsFalse :
      osWightmanReconstruction ≡ false

    massGapSurvival :
      Bool
    massGapSurvivalIsFalse :
      massGapSurvival ≡ false

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    workerLanes :
      List Sprint69YMWorkerLane
    workerLanesAreCanonical :
      workerLanes ≡ canonicalSprint69YMWorkerLanes

    closedInputs :
      List Sprint69YMClosedInput
    closedInputsAreCanonical :
      closedInputs ≡ canonicalSprint69YMClosedInputs

    leakageDiagnostics :
      List Sprint69YMLeakageDiagnostic
    leakageDiagnosticsAreCanonical :
      leakageDiagnostics ≡ canonicalSprint69YMLeakageDiagnostics

    openGates :
      List Sprint69YMOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint69YMOpenGates

    routeDecisions :
      List Sprint69YMRouteDecision
    routeDecisionsAreCanonical :
      routeDecisions ≡ canonicalSprint69YMRouteDecisions

    workerAssignment :
      String
    workerAssignmentIsCanonical :
      workerAssignment ≡ sprint69YMWorkerAssignment

    theoremTarget :
      String
    theoremTargetIsCanonical :
      theoremTarget ≡ sprint69YMTheoremTarget

    conditionalKPBoundary :
      String
    conditionalKPBoundaryIsCanonical :
      conditionalKPBoundary ≡ sprint69YMConditionalKPBoundary

    leakageBudget :
      String
    leakageBudgetIsCanonical :
      leakageBudget ≡ sprint69YMLeakageBudget

    leakageExamples :
      String
    leakageExamplesIsCanonical :
      leakageExamples ≡ sprint69YMLeakageExamples

    boundaryCorrectionTarget :
      String
    boundaryCorrectionTargetIsCanonical :
      boundaryCorrectionTarget ≡ sprint69YMBoundaryCorrectionTarget

    lemmaLadder :
      String
    lemmaLadderIsCanonical :
      lemmaLadder ≡ sprint69YMLemmaLadder

    d3D4Boundary :
      String
    d3D4BoundaryIsCanonical :
      d3D4Boundary ≡ sprint69YMD3D4Boundary

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint69YMBoundary

    promotions :
      List Sprint69YMPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint69YMPromotion → ⊥

canonicalSprint69YMTemporalFaceFactorizationWorkplanReceipt :
  ClaySprintSixtyNineYMTemporalFaceFactorizationWorkplanReceipt
canonicalSprint69YMTemporalFaceFactorizationWorkplanReceipt =
  record
    { sprint68YMNoPromotion = refl
    ; sprint68TemporalSupportNonCreation = true
    ; sprint68TemporalSupportNonCreationIsTrue = refl
    ; supportNonCreationIsOnlyInput = true
    ; supportNonCreationIsOnlyInputIsTrue = refl
    ; temporalFacesDisjointForAdmissiblePolymers = true
    ; temporalFacesDisjointForAdmissiblePolymersIsTrue = refl
    ; temporalFaceFactorizationProved = false
    ; temporalFaceFactorizationProvedIsFalse = refl
    ; temporalFaceFactorizationFromSupportNonCreationProved = false
    ; temporalFaceFactorizationFromSupportNonCreationProvedIsFalse = refl
    ; noTemporalCrossCouplingProved = false
    ; noTemporalCrossCouplingProvedIsFalse = refl
    ; productCutoffFactorizationProved = false
    ; productCutoffFactorizationProvedIsFalse = refl
    ; productCutoffFactorizationWithLeakageProved = false
    ; productCutoffFactorizationWithLeakageProvedIsFalse = refl
    ; localGaugeActionDecompositionProved = false
    ; localGaugeActionDecompositionProvedIsFalse = refl
    ; boundaryCorrectionSmallProved = false
    ; boundaryCorrectionSmallProvedIsFalse = refl
    ; temporalMeasureFactorizationWithLeakageProved = false
    ; temporalMeasureFactorizationWithLeakageProvedIsFalse = refl
    ; anisotropicPartitionOfUnityProved = false
    ; anisotropicPartitionOfUnityProvedIsFalse = refl
    ; slabActionAdditivityProved = false
    ; slabActionAdditivityProvedIsFalse = refl
    ; entropyCountTransferredToWeightedKP = false
    ; entropyCountTransferredToWeightedKPIsFalse = refl
    ; etaFourArithmetic = "4 * 0.23178189475262734 = 0.9271275790105094 < 1"
    ; etaFourArithmeticIsCanonical = refl
    ; weightedKPConvergesDiagnostic = "ideal weighted KP geometric ratio eta*q = 0.9271275790105094 < 1"
    ; weightedKPConvergesDiagnosticIsCanonical = refl
    ; weightedKPConvergesConditionally = true
    ; weightedKPConvergesConditionallyIsTrue = refl
    ; etaSpatial = "4"
    ; etaSpatialIsFour = refl
    ; etaSpatialTimesQ = "0.9271275790105094"
    ; etaSpatialTimesQIsCanonical = refl
    ; kpMargin = "0.07287242098949065"
    ; kpMarginIsCanonical = refl
    ; leakageMaxAllowed = "1.078600208471055"
    ; leakageMaxAllowedIsCanonical = refl
    ; leakageSafeFormalBound = "1.0785"
    ; leakageSafeFormalBoundIsCanonical = refl
    ; leakageSafeFormalBoundProduct = "1.0785 * 4q = 0.9999070939628344 < 1"
    ; leakageSafeFormalBoundProductIsCanonical = refl
    ; perFaceLeakageBudget = "0.025542115281578237"
    ; perFaceLeakageBudgetIsCanonical = refl
    ; perFaceLeakageBudgetPct = "2.5542115281578237%"
    ; perFaceLeakageBudgetPctIsCanonical = refl
    ; practicalPerFaceLeakageTargetPct = "2.5%"
    ; practicalPerFaceLeakageTargetPctIsCanonical = refl
    ; leakageTwoPointFivePctExample = "(1.025)^3 * 4q = 0.998414998"
    ; leakageTwoPointFivePctExampleIsCanonical = refl
    ; leakageTwoPointSixPctExample = "(1.026)^3 * 4q = 1.001340040"
    ; leakageTwoPointSixPctExampleIsCanonical = refl
    ; leakageThreePctExample = "(1.03)^3 * 4q = 1.013097338"
    ; leakageThreePctExampleIsCanonical = refl
    ; qHeadroomBeforeEtaFourFails = "0.018218105247372662"
    ; qHeadroomBeforeEtaFourFailsIsCanonical = refl
    ; leakageBoundProved = false
    ; leakageBoundProvedIsFalse = refl
    ; leakageSafeBoundProved = false
    ; leakageSafeBoundProvedIsFalse = refl
    ; leakageControlledWeightedKPCloses = false
    ; leakageControlledWeightedKPClosesIsFalse = refl
    ; l2D3SpatialSlabEtaQ = "0.9271275790105094"
    ; l2D3SpatialSlabEtaQIsCanonical = refl
    ; l2D4SpacetimeEtaQ = "1.85425516"
    ; l2D4SpacetimeEtaQIsCanonical = refl
    ; d3SpatialRowTransferredTo4D = false
    ; d3SpatialRowTransferredTo4DIsFalse = refl
    ; temporalQuotientEntropyHalvingL2 = false
    ; temporalQuotientEntropyHalvingL2IsFalse = refl
    ; anisotropicL2WeightedKPCloses = false
    ; anisotropicL2WeightedKPClosesIsFalse = refl
    ; etaFourArithmeticPromotedToKP = false
    ; etaFourArithmeticPromotedToKPIsFalse = refl
    ; allDiameterWeightedKP = false
    ; allDiameterWeightedKPIsFalse = refl
    ; balabanRGTransfer = false
    ; balabanRGTransferIsFalse = refl
    ; osWightmanReconstruction = false
    ; osWightmanReconstructionIsFalse = refl
    ; massGapSurvival = false
    ; massGapSurvivalIsFalse = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; workerLanes = canonicalSprint69YMWorkerLanes
    ; workerLanesAreCanonical = refl
    ; closedInputs = canonicalSprint69YMClosedInputs
    ; closedInputsAreCanonical = refl
    ; leakageDiagnostics = canonicalSprint69YMLeakageDiagnostics
    ; leakageDiagnosticsAreCanonical = refl
    ; openGates = canonicalSprint69YMOpenGates
    ; openGatesAreCanonical = refl
    ; routeDecisions = canonicalSprint69YMRouteDecisions
    ; routeDecisionsAreCanonical = refl
    ; workerAssignment = sprint69YMWorkerAssignment
    ; workerAssignmentIsCanonical = refl
    ; theoremTarget = sprint69YMTheoremTarget
    ; theoremTargetIsCanonical = refl
    ; conditionalKPBoundary = sprint69YMConditionalKPBoundary
    ; conditionalKPBoundaryIsCanonical = refl
    ; leakageBudget = sprint69YMLeakageBudget
    ; leakageBudgetIsCanonical = refl
    ; leakageExamples = sprint69YMLeakageExamples
    ; leakageExamplesIsCanonical = refl
    ; boundaryCorrectionTarget = sprint69YMBoundaryCorrectionTarget
    ; boundaryCorrectionTargetIsCanonical = refl
    ; lemmaLadder = sprint69YMLemmaLadder
    ; lemmaLadderIsCanonical = refl
    ; d3D4Boundary = sprint69YMD3D4Boundary
    ; d3D4BoundaryIsCanonical = refl
    ; boundary = sprint69YMBoundary
    ; boundaryIsCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint69YMPromotionImpossibleHere
    }

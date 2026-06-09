module DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.DCHoTTBridgeObligationIndex as B0
import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as AQFTQuotient
import DASHI.Physics.Closure.InteractingQFTBoundaryReceipt as IQFT
import DASHI.Physics.Closure.AdapterIrreducibilityNoGoIndex as AdapterNoGo
import DASHI.Physics.Closure.GRQFTClosurePromotionReceiptRequestPack as Request
import DASHI.Physics.Closure.TerminalCompletenessGrammarSurface as TerminalGrammar
import DASHI.Physics.Closure.TerminalOpenProblemStatusSurface as OpenProblems
import DASHI.Physics.Closure.CarrierToPhysicsInterpretationFunctor as Gate1
import DASHI.Physics.Closure.G6CrossLaneCommutingTheorem as G6
import DASHI.Physics.Closure.PressureBelow15SpectralTheoremObstruction as Gate2S8
import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as Gate2
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as Gate3Obs
import DASHI.Physics.Closure.YangMillsFieldEquationReceipt as Gate3
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as Gate4
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as Gate4GR
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Gate4Ricci
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as Gate4Scalar
import DASHI.Quantum.Stone as Gate5
import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient as Gate8Term4
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Gate5Modular
import DASHI.Physics.QFT.GNSFellRepresentationSurface as Gate5GNS
import DASHI.Physics.QFT.DHRHexagonObligation as Hexagon
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as Gate6DHR
import DASHI.Physics.QFT.DHRTensorDualGroupReconstruction as Gate6
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Gate7Matter
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Gate7Higgs
import DASHI.Physics.Closure.CKMEntryField as Gate7Field
import DASHI.Physics.Closure.CKMCarrierMixingReceipt as Gate7CKM
import DASHI.Physics.Closure.PrimeLaneGaugeAssignmentReceiptSurface as Gate7Prime
import DASHI.Physics.Closure.BalancedTritRestEnergyReceipt as Dispersion
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as Clay
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4Calibration
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4Stress
import DASHI.Physics.Closure.PenguinDecayProjectionArtifact as PenguinArtifact

------------------------------------------------------------------------
-- Terminal GR/QFT composition boundary.
--
-- This module records the four construction targets between the current
-- Paper-1/Paper-2 scaffold and any future GR/QFT or TOE-style claim.  It is
-- deliberately non-promoting: the "everything else" sentence is recorded as a
-- terminal target claim, not as an inhabited theorem.

data GRQFTTerminalBoundaryStatus : Set where
  terminalTargetRecordedNoClosureProof :
    GRQFTTerminalBoundaryStatus

data GRQFTHardConstructionStep : Set where
  b0DiscreteToSmoothPassage :
    GRQFTHardConstructionStep

  aqftLocalAlgebraFromCarrierData :
    GRQFTHardConstructionStep

  adapterIrreducibilityNoGoTheorems :
    GRQFTHardConstructionStep

  grqftReceiptComposition :
    GRQFTHardConstructionStep

canonicalGRQFTHardConstructionSteps :
  List GRQFTHardConstructionStep
canonicalGRQFTHardConstructionSteps =
  b0DiscreteToSmoothPassage
  ∷ aqftLocalAlgebraFromCarrierData
  ∷ adapterIrreducibilityNoGoTheorems
  ∷ grqftReceiptComposition
  ∷ []

data AdapterIrreducibilityTarget : Set where
  signatureIrreducibility :
    AdapterIrreducibilityTarget

  bornRuleStateIrreducibility :
    AdapterIrreducibilityTarget

  vacuumSelectionIrreducibility :
    AdapterIrreducibilityTarget

  couplingCalibrationIrreducibility :
    AdapterIrreducibilityTarget

canonicalAdapterIrreducibilityTargets :
  List AdapterIrreducibilityTarget
canonicalAdapterIrreducibilityTargets =
  signatureIrreducibility
  ∷ bornRuleStateIrreducibility
  ∷ vacuumSelectionIrreducibility
  ∷ couplingCalibrationIrreducibility
  ∷ []

data TerminalAdapter4IrreducibleInput : Set where
  gNewtonInput :
    TerminalAdapter4IrreducibleInput

  vHiggsInput :
    TerminalAdapter4IrreducibleInput

  fAAxionScaleInput :
    TerminalAdapter4IrreducibleInput

  v4volInput :
    TerminalAdapter4IrreducibleInput

canonicalTerminalAdapter4IrreducibleInputs :
  List TerminalAdapter4IrreducibleInput
canonicalTerminalAdapter4IrreducibleInputs =
  gNewtonInput
  ∷ vHiggsInput
  ∷ fAAxionScaleInput
  ∷ v4volInput
  ∷ []

data GRQFTSurvivingOpenObligation : Set where
  clayExternalAcceptanceOfYMAQFTMassGap :
    GRQFTSurvivingOpenObligation

  cosmologicalConstantVacuumGRCalibrationMismatch :
    GRQFTSurvivingOpenObligation

  bornRuleDerivationIrreducibleAdapter :
    GRQFTSurvivingOpenObligation

  couplingUnificationIrreducibleAdapter :
    GRQFTSurvivingOpenObligation

canonicalGRQFTSurvivingOpenObligations :
  List GRQFTSurvivingOpenObligation
canonicalGRQFTSurvivingOpenObligations =
  clayExternalAcceptanceOfYMAQFTMassGap
  ∷ cosmologicalConstantVacuumGRCalibrationMismatch
  ∷ bornRuleDerivationIrreducibleAdapter
  ∷ couplingUnificationIrreducibleAdapter
  ∷ []

data ProfessorFacingTerminalBlocker : Set where
  condensedProfiniteB0Caveat :
    ProfessorFacingTerminalBlocker

  formalDiskEquivalenceTarget :
    ProfessorFacingTerminalBlocker

  aqftTimeSliceTheoremTarget :
    ProfessorFacingTerminalBlocker

  adapterNoGoProofAssumptions :
    ProfessorFacingTerminalBlocker

  honestTOEReceiptTerminalCompletenessTarget :
    ProfessorFacingTerminalBlocker

canonicalProfessorFacingTerminalBlockers :
  List ProfessorFacingTerminalBlocker
canonicalProfessorFacingTerminalBlockers =
  condensedProfiniteB0Caveat
  ∷ formalDiskEquivalenceTarget
  ∷ aqftTimeSliceTheoremTarget
  ∷ adapterNoGoProofAssumptions
  ∷ honestTOEReceiptTerminalCompletenessTarget
  ∷ []

data GRQFTTerminalCompositionTarget : Set where
  pullbackCompositionTarget :
    GRQFTTerminalCompositionTarget

  stressEnergyBridgeTarget :
    GRQFTTerminalCompositionTarget

  massGapOutputPropertyTarget :
    GRQFTTerminalCompositionTarget

  lambdaEffOutputCalibrationTarget :
    GRQFTTerminalCompositionTarget

  terminalCompletenessTheoremTarget :
    GRQFTTerminalCompositionTarget

canonicalGRQFTTerminalCompositionTargets :
  List GRQFTTerminalCompositionTarget
canonicalGRQFTTerminalCompositionTargets =
  pullbackCompositionTarget
  ∷ stressEnergyBridgeTarget
  ∷ massGapOutputPropertyTarget
  ∷ lambdaEffOutputCalibrationTarget
  ∷ terminalCompletenessTheoremTarget
  ∷ []

data TerminalCompletenessClassification : Set where
  derivedFromCarrierTransport :
    TerminalCompletenessClassification

  reducibleToEmpiricalAdapter :
    TerminalCompletenessClassification

  openSpectralOrCalibrationProblem :
    TerminalCompletenessClassification

data TerminalCompletenessOpenObligation : Set where
  missingPhysicsStatementLanguage :
    TerminalCompletenessOpenObligation

  missingMinimalDerivationTree :
    TerminalCompletenessOpenObligation

  missingStructuralInductionOnReceipts :
    TerminalCompletenessOpenObligation

  missingAdapterNonRedundancyModels :
    TerminalCompletenessOpenObligation

  missingOpenClassCompletenessProof :
    TerminalCompletenessOpenObligation

canonicalTerminalCompletenessOpenObligations :
  List TerminalCompletenessOpenObligation
canonicalTerminalCompletenessOpenObligations =
  missingPhysicsStatementLanguage
  ∷ missingMinimalDerivationTree
  ∷ missingStructuralInductionOnReceipts
  ∷ missingAdapterNonRedundancyModels
  ∷ missingOpenClassCompletenessProof
  ∷ []

record TerminalCompletenessTheoremTarget : Setω where
  field
    PhysicsStatement :
      Set

    classify :
      PhysicsStatement →
      TerminalCompletenessClassification

    classificationShape :
      String

    classificationShape-v :
      classificationShape
      ≡
      "every-physics-statement-is-derived-from-carrier-reducible-to-adapter-or-open-spectral-calibration-target"

    proofMethodTarget :
      String

    proofMethodTarget-v :
      proofMethodTarget
      ≡
      "target-only-minimal-derivation-tree-and-structural-induction-over-receipt-language"

    adapterNonRedundancyTarget :
      String

    adapterNonRedundancyTarget-v :
      adapterNonRedundancyTarget
      ≡
      "target-only-countermodels-for-signature-Born-state-vacuum-and-coupling-adapters"

    openClassCompletenessTarget :
      String

    openClassCompletenessTarget-v :
      openClassCompletenessTarget
      ≡
      "target-only-mass-gap-and-cosmological-constant-are-output-properties-not-missing-composition-inputs"

    openCompletenessObligations :
      List TerminalCompletenessOpenObligation

    openCompletenessObligationsAreCanonical :
      openCompletenessObligations
      ≡
      canonicalTerminalCompletenessOpenObligations

    completenessProved :
      Bool

    completenessProvedIsFalse :
      completenessProved ≡ false

open TerminalCompletenessTheoremTarget public

data WeakTerminalPromotionGateObligation : Set where
  b0BridgeStillOpen :
    WeakTerminalPromotionGateObligation

  aqftCarrierAndTimeSliceStillOpen :
    WeakTerminalPromotionGateObligation

  dhrReconstructionStillOpen :
    WeakTerminalPromotionGateObligation

  stressEnergyWaldAuthorityStillOpen :
    WeakTerminalPromotionGateObligation

  adapterNoGoAuthorityStillOpen :
    WeakTerminalPromotionGateObligation

  continuumClayExternalMassGapAcceptanceGateOpen :
    WeakTerminalPromotionGateObligation

  sequesteringCompactUniverseStillAdapter4 :
    WeakTerminalPromotionGateObligation

  sequesteringC2C3CalibrationStillOpen :
    WeakTerminalPromotionGateObligation

  yukawaRatioReceiptBundleStillConditional :
    WeakTerminalPromotionGateObligation

  absoluteHiggsVEVStillAdapter4 :
    WeakTerminalPromotionGateObligation

canonicalWeakTerminalPromotionGateObligations :
  List WeakTerminalPromotionGateObligation
canonicalWeakTerminalPromotionGateObligations =
  b0BridgeStillOpen
  ∷ aqftCarrierAndTimeSliceStillOpen
  ∷ dhrReconstructionStillOpen
  ∷ stressEnergyWaldAuthorityStillOpen
  ∷ adapterNoGoAuthorityStillOpen
  ∷ continuumClayExternalMassGapAcceptanceGateOpen
  ∷ sequesteringCompactUniverseStillAdapter4
  ∷ sequesteringC2C3CalibrationStillOpen
  ∷ yukawaRatioReceiptBundleStillConditional
  ∷ absoluteHiggsVEVStillAdapter4
  ∷ []

data SixPostulateAuthorityLedgerStatus : Set where
  sixPostulatePackageRecordedNoAuthorityPromotion :
    SixPostulateAuthorityLedgerStatus

record SixPostulateAuthorityLedger : Setω where
  field
    status :
      SixPostulateAuthorityLedgerStatus

    minimalPostulatePackage :
      OpenProblems.MinimalPostulateSetForFullChainClosure

    postulates :
      List OpenProblems.MinimalPostulateForFullChainClosure

    postulatesAreCanonical :
      postulates
      ≡
      OpenProblems.canonicalMinimalPostulatesForFullChainClosure

    uniformBalabanOrAgawaIRFixedPointStillExternal :
      Bool

    uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue :
      uniformBalabanOrAgawaIRFixedPointStillExternal ≡ true

    candidateDASHIRecursionAcceptedAuthority :
      Bool

    candidateDASHIRecursionAcceptedAuthorityIsFalse :
      candidateDASHIRecursionAcceptedAuthority ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    ledgerPromoted :
      Bool

    ledgerPromotedIsFalse :
      ledgerPromoted ≡ false

    authorityBoundary :
      List String

open SixPostulateAuthorityLedger public

canonicalSixPostulateAuthorityLedger :
  SixPostulateAuthorityLedger
canonicalSixPostulateAuthorityLedger =
  record
    { status =
        sixPostulatePackageRecordedNoAuthorityPromotion
    ; minimalPostulatePackage =
        OpenProblems.canonicalMinimalPostulateSetForFullChainClosure
    ; postulates =
        OpenProblems.canonicalMinimalPostulatesForFullChainClosure
    ; postulatesAreCanonical =
        refl
    ; uniformBalabanOrAgawaIRFixedPointStillExternal =
        true
    ; uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue =
        refl
    ; candidateDASHIRecursionAcceptedAuthority =
        false
    ; candidateDASHIRecursionAcceptedAuthorityIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; ledgerPromoted =
        false
    ; ledgerPromotedIsFalse =
        refl
    ; authorityBoundary =
        "six-postulate package is an explicit modulo ledger, not local authority"
        ∷ "Im-reflect-DASHI and WeakBGCorrespondence are safe only as named postulate accounting"
        ∷ "Bisognano-Wichmann and cStarCompletion remain AQFT authority/completion targets"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint is the Clay/external-acceptance halt"
        ∷ "Doplicher-Roberts is consumed only after DHR hypotheses and reconstruction authority close"
        ∷ "candidate DASHI recursion does not issue W3/W4/W5/Clay authority"
        ∷ "ledgerPromoted, continuumClayMassGapPromoted, and terminalClaimPromoted stay false"
        ∷ []
    }

data WeakTerminalClaimOpenStatusGrammarStatus : Set where
  weakTerminalClaimRecordedOpenNonPromoted :
    WeakTerminalClaimOpenStatusGrammarStatus

  weakTerminalClaimPromotedModuloMinimalPostulatesTerminalOpen :
    WeakTerminalClaimOpenStatusGrammarStatus

data WeakDepthIndexedTerminalStatusToken : Set where
  finiteDepthMassGapWeaklyPromotedContinuumTerminalOpen :
    WeakDepthIndexedTerminalStatusToken

data GRQFTTerminalPromotionAuthorityToken : Set where

record WeakTerminalClaimOpenStatusGrammar : Setω where
  field
    status :
      WeakTerminalClaimOpenStatusGrammarStatus

    terminalOpenProblemStatus :
      OpenProblems.TerminalOpenProblemStatusSurface

    massGapProofLandscapeUpdate :
      OpenProblems.MassGapProofLandscapeUpdateStatus

    minimalPostulateSetForFullChainClosure :
      OpenProblems.MinimalPostulateSetForFullChainClosure

    terminalCompletenessGrammarReceipt :
      TerminalGrammar.TerminalCompletenessGrammarReceiptSurface

    physicalAccessibilityFourWayGrammarReceipt :
      TerminalGrammar.PhysicalAccessibilityFourWayTerminalGrammarReceipt

    gateObligations :
      List WeakTerminalPromotionGateObligation

    gateObligationsAreCanonical :
      gateObligations
      ≡
      canonicalWeakTerminalPromotionGateObligations

    grammarShape :
      String

    grammarShape-v :
      grammarShape
      ≡
      "weak-terminal-claim-promoted-modulo-MinimalPostulateSetForFullChainClosure-DASHI-mass-gap-closed-Clay-promotion-open"

    depthIndexedTerminalStatus :
      WeakDepthIndexedTerminalStatusToken

    proObjectMassGapProved :
      Bool

    proObjectMassGapProvedIsTrue :
      proObjectMassGapProved
      ≡
      true

    depthIndexedMassGapPromoted :
      Bool

    depthIndexedMassGapPromotedIsTrue :
      depthIndexedMassGapPromoted
      ≡
      true

    continuumMassGapProvedInDASHI :
      Bool

    continuumMassGapProvedInDASHIIsFalse :
      continuumMassGapProvedInDASHI
      ≡
      false

    continuumClayExternalMassGapAcceptanceStillOpen :
      Bool

    continuumClayExternalMassGapAcceptanceStillOpenIsTrue :
      continuumClayExternalMassGapAcceptanceStillOpen
      ≡
      true

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted
      ≡
      false

    yukawaRatioOnlyConditionallyPromoted :
      Bool

    yukawaRatioOnlyConditionallyPromotedIsTrue :
      yukawaRatioOnlyConditionallyPromoted
      ≡
      true

    terminalAdapter4Inventory :
      List TerminalAdapter4IrreducibleInput

    terminalAdapter4InventoryAreCanonical :
      terminalAdapter4Inventory
      ≡
      canonicalTerminalAdapter4IrreducibleInputs

    hierarchyProblemStrategyStatus :
      OpenProblems.HierarchyProblemStrategyStatus

    finalAdapter4Governance :
      OpenProblems.FinalAdapter4ReceiptGovernance

    terminalPromotionFlipCondition :
      OpenProblems.TerminalClaimPromotionFlipCondition

    publicationTierMap :
      OpenProblems.TerminalPublicationTierMap

    finalDeltaSummary :
      List String

    finalDeltaSummaryIsCanonical :
      finalDeltaSummary
      ≡
      OpenProblems.canonicalTerminalPublicationFinalDeltaSummary

    b0ActuallyClosed :
      Bool

    b0ActuallyClosedIsFalse :
      b0ActuallyClosed ≡ false

    aqftActuallyClosed :
      Bool

    aqftActuallyClosedIsFalse :
      aqftActuallyClosed ≡ false

    dhrActuallyClosed :
      Bool

    dhrActuallyClosedIsFalse :
      dhrActuallyClosed ≡ false

    laneDimensionInternallyClosed :
      Bool

    laneDimensionInternallyClosedIsTrue :
      laneDimensionInternallyClosed ≡ true

    agawaCompletionFormalismEncoded :
      Bool

    agawaCompletionFormalismEncodedIsTrue :
      agawaCompletionFormalismEncoded ≡ true

    agawaCompletionAcceptedAuthority :
      Bool

    agawaCompletionAcceptedAuthorityIsFalse :
      agawaCompletionAcceptedAuthority ≡ false

    doplicherRobertsFiveHypothesesTyped :
      Bool

    doplicherRobertsFiveHypothesesTypedIsTrue :
      doplicherRobertsFiveHypothesesTyped ≡ true

    doplicherRobertsComputesLaneDimension :
      Bool

    doplicherRobertsComputesLaneDimensionIsFalse :
      doplicherRobertsComputesLaneDimension ≡ false

    laneDimensionComputedByDLM :
      Bool

    laneDimensionComputedByDLMIsTrue :
      laneDimensionComputedByDLM ≡ true

    laneDimensionInternallyPromoted :
      Bool

    laneDimensionInternallyPromotedIsTrue :
      laneDimensionInternallyPromoted ≡ true

    bisognanoWichmannFeedsTimeSliceModuloAuthority :
      Bool

    bisognanoWichmannFeedsTimeSliceModuloAuthorityIsTrue :
      bisognanoWichmannFeedsTimeSliceModuloAuthority ≡ true

    laneDimensionE8MckayConjectural :
      Bool

    laneDimensionE8MckayConjecturalIsTrue :
      laneDimensionE8MckayConjectural ≡ true

    p7SU2RHighEnergyBridgeSeparateFromLowEnergySM :
      Bool

    p7SU2RHighEnergyBridgeSeparateFromLowEnergySMIsTrue :
      p7SU2RHighEnergyBridgeSeparateFromLowEnergySM ≡ true

    noGoAndWaldReceiptSurfacesComplete :
      Bool

    noGoAndWaldReceiptSurfacesCompleteIsTrue :
      noGoAndWaldReceiptSurfacesComplete ≡ true

    weakTerminalClaimPromotionIsModuloMinimalPostulates :
      Bool

    weakTerminalClaimPromotionIsModuloMinimalPostulatesIsTrue :
      weakTerminalClaimPromotionIsModuloMinimalPostulates ≡ true

    weakTerminalClaimPromoted :
      Bool

    weakTerminalClaimPromotedIsTrue :
      weakTerminalClaimPromoted ≡ true

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    noWeakPromotionWithoutAuthority :
      GRQFTTerminalPromotionAuthorityToken →
      ⊥

    grammarBoundary :
      List String

open WeakTerminalClaimOpenStatusGrammar public

data GRQFTTerminalPromotionReceipt : Set where

terminalPromotionReceiptImpossibleHere :
  GRQFTTerminalPromotionReceipt →
  ⊥
terminalPromotionReceiptImpossibleHere ()

record GRQFTCompositionBoundary : Setω where
  field
    status :
      GRQFTTerminalBoundaryStatus

    b0BridgeIndex :
      B0.DCHoTTBridgeObligationIndex

    aqftTypedNetSurface :
      AQFT.AQFTTypedNetSurface

    aqftCarrierAlgebraQuotientSurface :
      AQFTQuotient.AQFTCarrierAlgebraQuotientSurface

    depthFilteredLocalAlgebraSurface :
      AQFTQuotient.DepthFilteredLocalAlgebraSurface

    cauchyEvolutionTarget :
      AQFTQuotient.CauchyEvolutionReceiptTarget

    interactingQFTBoundary :
      IQFT.InteractingQFTBoundaryReceipt

    adapterIrreducibilityNoGoIndex :
      AdapterNoGo.AdapterIrreducibilityNoGoIndex

    closureRequestPack :
      Request.GRQFTClosurePromotionReceiptRequestPack

    terminalOpenProblemStatus :
      OpenProblems.TerminalOpenProblemStatusSurface

    massGapProofLandscapeUpdate :
      OpenProblems.MassGapProofLandscapeUpdateStatus

    minimalPostulateSetForFullChainClosure :
      OpenProblems.MinimalPostulateSetForFullChainClosure

    terminalCompletenessGrammarReceipt :
      TerminalGrammar.TerminalCompletenessGrammarReceiptSurface

    physicalAccessibilityFourWayGrammarReceipt :
      TerminalGrammar.PhysicalAccessibilityFourWayTerminalGrammarReceipt

    b0BridgeBlockers :
      List B0.DCHoTTB0BridgeBlocker

    b02FlatFormalDiskOpenObligations :
      List B0.FlatFormalDiskOpenObligation

    b03GStructureOpenObligations :
      List B0.GStructureReductionOpenObligation

    aqftTypedNetOpenObligations :
      List AQFT.AQFTTypedNetOpenObligation

    aqftQuotientOpenObligations :
      List AQFTQuotient.AQFTCarrierAlgebraQuotientOpenObligation

    depthFilteredOpenObligations :
      List AQFTQuotient.DepthFilteredAlgebraOpenObligation

    cauchyEvolutionOpenObligations :
      List AQFTQuotient.CauchyEvolutionOpenObligation

    adapterIrreducibilityOpenObligations :
      List AdapterNoGo.AdapterIrreducibilityOpenObligation

    closureRequestPackStillRequired :
      String

    closureRequestPackStillRequired-v :
      closureRequestPackStillRequired
      ≡
      "GRQFT-request-pack-authority-PDF-carrier-downstream-fields-GR-law-QFT-law-consumers-and-empirical-validation-still-required"

    professorFacingTerminalBlockers :
      List ProfessorFacingTerminalBlocker

    professorFacingTerminalBlockersAreCanonical :
      professorFacingTerminalBlockers
      ≡
      canonicalProfessorFacingTerminalBlockers

    condensedProfiniteB0CaveatStatus :
      String

    condensedProfiniteB0CaveatStatus-v :
      condensedProfiniteB0CaveatStatus
      ≡
      "B0-pro-object-is-DASHI-side-condensed-profinite-caveat-not-a-DCHoTT-formal-space-proof"

    formalDiskEquivalenceTargetStatus :
      String

    formalDiskEquivalenceTargetStatus-v :
      formalDiskEquivalenceTargetStatus
      ≡
      "formal-disk-equivalence-is-a-target-between-refinement-limit-and-DCHoTT-formal-disk-not-an-imported-theorem"

    aqftTimeSliceTheoremTargetStatus :
      String

    aqftTimeSliceTheoremTargetStatus-v :
      aqftTimeSliceTheoremTargetStatus
      ≡
      "AQFT-time-slice-is-CauchyEvolutionReceiptTarget-not-a-proved-theorem"

    adapterNoGoProofAssumptionsStatus :
      String

    adapterNoGoProofAssumptionsStatus-v :
      adapterNoGoProofAssumptionsStatus
      ≡
      "adapter-no-go-claims-require-explicit-assumptions-for-signature-Born-vacuum-couplings-and-GUT-boundary"

    honestTOEReceiptTerminalCompletenessTargetStatus :
      String

    honestTOEReceiptTerminalCompletenessTargetStatus-v :
      honestTOEReceiptTerminalCompletenessTargetStatus
      ≡
      "HonestTOEReceipt-is-terminal-completeness-target-only-after-B0-AQFT-W5-and-adapter-no-go-receipts"

    terminalCompositionTargets :
      List GRQFTTerminalCompositionTarget

    terminalCompositionTargetsAreCanonical :
      terminalCompositionTargets
      ≡
      canonicalGRQFTTerminalCompositionTargets

    pullbackCompositionShape :
      String

    pullbackCompositionShape-v :
      pullbackCompositionShape
      ≡
      "GRQFT-pullback=B0-smooth-geometry-times-compatible-AQFT-local-net-times-W5-authority-stress-energy-over-shared-carrier"

    stressEnergyBridgeTargetStatus :
      String

    stressEnergyBridgeTargetStatus-v :
      stressEnergyBridgeTargetStatus
      ≡
      "stress-energy-bridge-target=W4-authority-backed-T-mu-nu-compatible-with-same-curvature-conservation-and-unit-calibration"

    terminalCompletenessTheoremShape :
      String

    terminalCompletenessTheoremShape-v :
      terminalCompletenessTheoremShape
      ≡
      "HonestTOEReceipt-terminal-completeness=every-surviving-obligation-discharged-or-reduced-to-explicit-adapter-no-go-assumption-with-no-new-authority"

    terminalCompletenessTheoremTargetSurface :
      TerminalCompletenessTheoremTarget

    weakTerminalClaimOpenStatusGrammar :
      WeakTerminalClaimOpenStatusGrammar

    hardConstructionSteps :
      List GRQFTHardConstructionStep

    hardConstructionStepsAreCanonical :
      hardConstructionSteps
      ≡
      canonicalGRQFTHardConstructionSteps

    adapterIrreducibilityTargets :
      List AdapterIrreducibilityTarget

    adapterIrreducibilityTargetsAreCanonical :
      adapterIrreducibilityTargets
      ≡
      canonicalAdapterIrreducibilityTargets

    terminalAdapter4Inventory :
      List TerminalAdapter4IrreducibleInput

    terminalAdapter4InventoryAreCanonical :
      terminalAdapter4Inventory
      ≡
      canonicalTerminalAdapter4IrreducibleInputs

    terminalAdapter4InventoryShape :
      String

    terminalAdapter4InventoryShape-v :
      terminalAdapter4InventoryShape
      ≡
      "final-irreducible-Adapter4-inventory=G_Newton-v_Higgs-f_a-V4vol"

    hierarchyProblemStrategyStatus :
      OpenProblems.HierarchyProblemStrategyStatus

    finalAdapter4Governance :
      OpenProblems.FinalAdapter4ReceiptGovernance

    terminalPromotionFlipCondition :
      OpenProblems.TerminalClaimPromotionFlipCondition

    publicationTierMap :
      OpenProblems.TerminalPublicationTierMap

    finalDeltaSummary :
      List String

    finalDeltaSummaryIsCanonical :
      finalDeltaSummary
      ≡
      OpenProblems.canonicalTerminalPublicationFinalDeltaSummary

    survivingOpenObligations :
      List GRQFTSurvivingOpenObligation

    survivingOpenObligationsAreCanonical :
      survivingOpenObligations
      ≡
      canonicalGRQFTSurvivingOpenObligations

    b0TheoremShape :
      String

    b0TheoremShape-v :
      b0TheoremShape
      ≡
      "B0.1-compatible-pro-object-plus-B0.2-flat-disk-plus-B0.3-frame-metric-tower-admits-DCHoTT-manifold-and-torsion-free-G-structure-target"

    aqftConstructionShape :
      String

    aqftConstructionShape-v :
      aqftConstructionShape
      ≡
      "A(O)=promoted-receipts-over-restricted-carrier-quotiented-by-transport-equivalence"

    receiptCompositionShape :
      String

    receiptCompositionShape-v :
      receiptCompositionShape
      ≡
      "GRQFTReceipt=B0+B1+AQFTNet+signature+Born+vacuum+coupling-adapters"

    massGapStatus :
      String

    massGapStatus-v :
      massGapStatus
      ≡
      "DASHI-internal-continuum-mass-gap-proved-by-ST3-plus-Banach-receipt-Clay-promotion-open-not-terminal-theorem"

    cosmologicalConstStatus :
      String

    cosmologicalConstStatus-v :
      cosmologicalConstStatus
      ≡
      "sequestering-inhabited-modulo-compact-universe-shift-symmetry-c2-calibration-c3-bound-cosmological-constant-not-solved"

    bornRuleDerivation :
      String

    bornRuleDerivation-v :
      bornRuleDerivation
      ≡
      "irreducible-adapter-2"

    couplingUnification :
      String

    couplingUnification-v :
      couplingUnification
      ≡
      "Yukawa-ratio-form-conditional-on-MatterPrimeLane-FN-Frobenius-receipts-absolute-Higgs-vev-remains-Adapter4"

    everythingElseTargetClaim :
      String

    everythingElseTargetClaim-v :
      everythingElseTargetClaim
      ≡
      "target-only-inhabited-or-reducible-to-above-four-after-B0-B1-AQFT-W5-request-pack-and-adapter-no-go-theorems"

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    noTerminalPromotionWithoutAuthority :
      GRQFTTerminalPromotionAuthorityToken →
      ⊥

    impossibleReceiptHere :
      GRQFTTerminalPromotionReceipt →
      ⊥

    compositionBoundary :
      List String

open GRQFTCompositionBoundary public

postulate
  abstractPhysicsStatement :
    Set

  abstractPhysicsStatementClassification :
    abstractPhysicsStatement →
    TerminalCompletenessClassification

canonicalTerminalCompletenessTheoremTarget :
  TerminalCompletenessTheoremTarget
canonicalTerminalCompletenessTheoremTarget =
  record
    { PhysicsStatement =
        abstractPhysicsStatement
    ; classify =
        abstractPhysicsStatementClassification
    ; classificationShape =
        "every-physics-statement-is-derived-from-carrier-reducible-to-adapter-or-open-spectral-calibration-target"
    ; classificationShape-v =
        refl
    ; proofMethodTarget =
        "target-only-minimal-derivation-tree-and-structural-induction-over-receipt-language"
    ; proofMethodTarget-v =
        refl
    ; adapterNonRedundancyTarget =
        "target-only-countermodels-for-signature-Born-state-vacuum-and-coupling-adapters"
    ; adapterNonRedundancyTarget-v =
        refl
    ; openClassCompletenessTarget =
        "target-only-mass-gap-and-cosmological-constant-are-output-properties-not-missing-composition-inputs"
    ; openClassCompletenessTarget-v =
        refl
    ; openCompletenessObligations =
        canonicalTerminalCompletenessOpenObligations
    ; openCompletenessObligationsAreCanonical =
        refl
    ; completenessProved =
        false
    ; completenessProvedIsFalse =
        refl
    }

canonicalWeakTerminalClaimOpenStatusGrammar :
  WeakTerminalClaimOpenStatusGrammar
canonicalWeakTerminalClaimOpenStatusGrammar =
  record
    { status =
        weakTerminalClaimPromotedModuloMinimalPostulatesTerminalOpen
    ; terminalOpenProblemStatus =
        OpenProblems.canonicalTerminalOpenProblemStatusSurface
    ; massGapProofLandscapeUpdate =
        OpenProblems.canonicalMassGapProofLandscapeUpdateStatus
    ; minimalPostulateSetForFullChainClosure =
        OpenProblems.canonicalMinimalPostulateSetForFullChainClosure
    ; terminalCompletenessGrammarReceipt =
        TerminalGrammar.canonicalTerminalCompletenessGrammarReceiptSurface
    ; physicalAccessibilityFourWayGrammarReceipt =
        TerminalGrammar.canonicalPhysicalAccessibilityFourWayTerminalGrammarReceipt
    ; gateObligations =
        canonicalWeakTerminalPromotionGateObligations
    ; gateObligationsAreCanonical =
        refl
    ; grammarShape =
        "weak-terminal-claim-promoted-modulo-MinimalPostulateSetForFullChainClosure-DASHI-mass-gap-closed-Clay-promotion-open"
    ; grammarShape-v =
        refl
    ; depthIndexedTerminalStatus =
        finiteDepthMassGapWeaklyPromotedContinuumTerminalOpen
    ; proObjectMassGapProved =
        true
    ; proObjectMassGapProvedIsTrue =
        refl
    ; depthIndexedMassGapPromoted =
        true
    ; depthIndexedMassGapPromotedIsTrue =
        refl
    ; continuumMassGapProvedInDASHI =
        false
    ; continuumMassGapProvedInDASHIIsFalse =
        refl
    ; continuumClayExternalMassGapAcceptanceStillOpen =
        true
    ; continuumClayExternalMassGapAcceptanceStillOpenIsTrue =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; yukawaRatioOnlyConditionallyPromoted =
        true
    ; yukawaRatioOnlyConditionallyPromotedIsTrue =
        refl
    ; terminalAdapter4Inventory =
        canonicalTerminalAdapter4IrreducibleInputs
    ; terminalAdapter4InventoryAreCanonical =
        refl
    ; hierarchyProblemStrategyStatus =
        OpenProblems.canonicalHierarchyProblemStrategyStatus
    ; finalAdapter4Governance =
        OpenProblems.canonicalFinalAdapter4ReceiptGovernance
    ; terminalPromotionFlipCondition =
        OpenProblems.canonicalTerminalClaimPromotionFlipCondition
    ; publicationTierMap =
        OpenProblems.canonicalTerminalPublicationTierMap
    ; finalDeltaSummary =
        OpenProblems.canonicalTerminalPublicationFinalDeltaSummary
    ; finalDeltaSummaryIsCanonical =
        refl
    ; b0ActuallyClosed =
        false
    ; b0ActuallyClosedIsFalse =
        refl
    ; aqftActuallyClosed =
        false
    ; aqftActuallyClosedIsFalse =
        refl
    ; dhrActuallyClosed =
        false
    ; dhrActuallyClosedIsFalse =
        refl
    ; laneDimensionInternallyClosed =
        true
    ; laneDimensionInternallyClosedIsTrue =
        refl
    ; agawaCompletionFormalismEncoded =
        true
    ; agawaCompletionFormalismEncodedIsTrue =
        refl
    ; agawaCompletionAcceptedAuthority =
        false
    ; agawaCompletionAcceptedAuthorityIsFalse =
        refl
    ; doplicherRobertsFiveHypothesesTyped =
        true
    ; doplicherRobertsFiveHypothesesTypedIsTrue =
        refl
    ; doplicherRobertsComputesLaneDimension =
        false
    ; doplicherRobertsComputesLaneDimensionIsFalse =
        refl
    ; laneDimensionComputedByDLM =
        true
    ; laneDimensionComputedByDLMIsTrue =
        refl
    ; laneDimensionInternallyPromoted =
        true
    ; laneDimensionInternallyPromotedIsTrue =
        refl
    ; bisognanoWichmannFeedsTimeSliceModuloAuthority =
        true
    ; bisognanoWichmannFeedsTimeSliceModuloAuthorityIsTrue =
        refl
    ; laneDimensionE8MckayConjectural =
        true
    ; laneDimensionE8MckayConjecturalIsTrue =
        refl
    ; p7SU2RHighEnergyBridgeSeparateFromLowEnergySM =
        true
    ; p7SU2RHighEnergyBridgeSeparateFromLowEnergySMIsTrue =
        refl
    ; noGoAndWaldReceiptSurfacesComplete =
        true
    ; noGoAndWaldReceiptSurfacesCompleteIsTrue =
        refl
    ; weakTerminalClaimPromotionIsModuloMinimalPostulates =
        true
    ; weakTerminalClaimPromotionIsModuloMinimalPostulatesIsTrue =
        refl
    ; weakTerminalClaimPromoted =
        true
    ; weakTerminalClaimPromotedIsTrue =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; noWeakPromotionWithoutAuthority =
        λ ()
    ; grammarBoundary =
        "weak terminal status is promoted only modulo MinimalPostulateSetForFullChainClosure and cannot promote a terminal theorem"
        ∷ "minimal postulate package contains Im-reflect-DASHI, WeakBGCorrespondence, BisognanoWichmann, UniformBalaban-or-AgawaIRFixedPoint, cStarCompletion, and DoplicherRoberts"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint is a genuine open Clay/external-acceptance gate"
        ∷ "candidate DASHI recursion is not accepted authority"
        ∷ "Agawa completion formalism is encoded as claimed stable IR fixed point plus G4/Morse Gribov uniqueness, but accepted continuum authority is still false"
        ∷ "mass-gap proof landscape exposes four lineages: Odusanya/Balaban, Agawa/holonomy, dissolution/no-go campaign, and DASHI pro-object mass gap"
        ∷ "B0 must close the DCHoTT formal-space/formal-disk/G-structure bridge before terminal promotion"
        ∷ "AQFT must close concrete local algebras, quotient/C*-completion, descent, and time-slice before terminal promotion"
        ∷ "Bisognano-Wichmann feeds time-slice only modulo net hypotheses and authority, not as unconditional local promotion"
        ∷ "DHR reconstruction authority and the exact Standard Model comparison remain open"
        ∷ "Doplicher-Roberts five hypotheses are typed; DR reconstructs G_DHR while laneDimension remains authority-backed and conditional on the DLM route"
        ∷ "laneDimension has left the weak-terminal modulo gate list; DHR/Standard Model matching, terminal, and Clay promotion remain false"
        ∷ "E8/McKay metadata remains bridge context; p7 SU2R is a high-energy bridge separate from low-energy Standard Model matching"
        ∷ "no-go receipts and Wald coefficient selection are complete at receipt-surface level while theorem/terminal promotion remains guarded"
        ∷ "Wald c1/c2/c3 authority and adapter no-go authorities must also close before the weak claim can strengthen"
        ∷ "continuumMassGapProvedInDASHI is false; ST3/Banach material is local finite-carrier evidence and continuumClayMassGapPromoted remains false"
        ∷ "Yukawa ratio form is conditional on MatterPrimeLane, FN, and Frobenius receipts; absolute Higgs vev stays Adapter4"
        ∷ "hierarchy strategies are recorded: SUSY stabilizes but does not derive v_Higgs, relaxion has no 246 GeV receipt, and accept-as-adapter is the terminal governance route"
        ∷ "FinalAdapter4 acceptance is governance over G_Newton, v_Higgs, f_a, and V4vol"
        ∷ "terminalClaimPromoted remains false because Clay/external mass-gap promotion and other terminal authorities remain pending"
        ∷ "final terminal Adapter4 inventory is {G_Newton, v_Higgs, f_a, V4vol}"
        ∷ "physical-accessibility four-way grammar is consumed only as a finite non-promoting terminal classifier"
        ∷ "publication tier map is non-promoting: Tier A Paper 1 publishable now, Tier B Papers 2-3 after one focused sprint, Tier C Papers 4-5 require new math, Tier D Papers 6-7 require Clay/external acceptance or new terminal integration"
        ∷ "Reeh-Schlieder is no longer a Paper 3 blocker once dependent receipts are accepted"
        ∷ "final delta summary: Paper1 2-4 weeks writing; Paper2 flag split plus Wellen cite 1-2 weeks; Paper3 quotient/cites/Reeh no longer blocker after dependent receipts; Paper4 and Paper6 months-years; Paper7 after all prior closures"
        ∷ "Papers 1-3 are fully executable from current repo state; Papers 4-7 remain open"
        ∷ []
    }

canonicalGRQFTCompositionBoundary :
  GRQFTCompositionBoundary
canonicalGRQFTCompositionBoundary =
  record
    { status =
        terminalTargetRecordedNoClosureProof
    ; b0BridgeIndex =
        B0.canonicalDCHoTTBridgeObligationIndex
    ; aqftTypedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; aqftCarrierAlgebraQuotientSurface =
        AQFTQuotient.canonicalAQFTCarrierAlgebraQuotientSurface
    ; depthFilteredLocalAlgebraSurface =
        AQFTQuotient.canonicalDepthFilteredLocalAlgebraSurface
    ; cauchyEvolutionTarget =
        AQFTQuotient.canonicalCauchyEvolutionReceiptTarget
    ; interactingQFTBoundary =
        IQFT.canonicalInteractingQFTBoundaryReceipt
    ; adapterIrreducibilityNoGoIndex =
        AdapterNoGo.canonicalAdapterIrreducibilityNoGoIndex
    ; closureRequestPack =
        Request.canonicalGRQFTClosurePromotionReceiptRequestPack
    ; terminalOpenProblemStatus =
        OpenProblems.canonicalTerminalOpenProblemStatusSurface
    ; massGapProofLandscapeUpdate =
        OpenProblems.canonicalMassGapProofLandscapeUpdateStatus
    ; minimalPostulateSetForFullChainClosure =
        OpenProblems.canonicalMinimalPostulateSetForFullChainClosure
    ; terminalCompletenessGrammarReceipt =
        TerminalGrammar.canonicalTerminalCompletenessGrammarReceiptSurface
    ; physicalAccessibilityFourWayGrammarReceipt =
        TerminalGrammar.canonicalPhysicalAccessibilityFourWayTerminalGrammarReceipt
    ; b0BridgeBlockers =
        B0.canonicalDCHoTTB0BridgeBlockers
    ; b02FlatFormalDiskOpenObligations =
        B0.canonicalFlatFormalDiskOpenObligations
    ; b03GStructureOpenObligations =
        B0.canonicalGStructureReductionOpenObligations
    ; aqftTypedNetOpenObligations =
        AQFT.AQFTTypedNetSurface.openObligations AQFT.canonicalAQFTTypedNetSurface
    ; aqftQuotientOpenObligations =
        AQFTQuotient.AQFTCarrierAlgebraQuotientSurface.openObligations
          AQFTQuotient.canonicalAQFTCarrierAlgebraQuotientSurface
    ; depthFilteredOpenObligations =
        AQFTQuotient.canonicalDepthFilteredAlgebraOpenObligations
    ; cauchyEvolutionOpenObligations =
        AQFTQuotient.canonicalCauchyEvolutionOpenObligations
    ; adapterIrreducibilityOpenObligations =
        AdapterNoGo.canonicalAdapterIrreducibilityOpenObligations
    ; closureRequestPackStillRequired =
        "GRQFT-request-pack-authority-PDF-carrier-downstream-fields-GR-law-QFT-law-consumers-and-empirical-validation-still-required"
    ; closureRequestPackStillRequired-v =
        refl
    ; professorFacingTerminalBlockers =
        canonicalProfessorFacingTerminalBlockers
    ; professorFacingTerminalBlockersAreCanonical =
        refl
    ; condensedProfiniteB0CaveatStatus =
        "B0-pro-object-is-DASHI-side-condensed-profinite-caveat-not-a-DCHoTT-formal-space-proof"
    ; condensedProfiniteB0CaveatStatus-v =
        refl
    ; formalDiskEquivalenceTargetStatus =
        "formal-disk-equivalence-is-a-target-between-refinement-limit-and-DCHoTT-formal-disk-not-an-imported-theorem"
    ; formalDiskEquivalenceTargetStatus-v =
        refl
    ; aqftTimeSliceTheoremTargetStatus =
        "AQFT-time-slice-is-CauchyEvolutionReceiptTarget-not-a-proved-theorem"
    ; aqftTimeSliceTheoremTargetStatus-v =
        refl
    ; adapterNoGoProofAssumptionsStatus =
        "adapter-no-go-claims-require-explicit-assumptions-for-signature-Born-vacuum-couplings-and-GUT-boundary"
    ; adapterNoGoProofAssumptionsStatus-v =
        refl
    ; honestTOEReceiptTerminalCompletenessTargetStatus =
        "HonestTOEReceipt-is-terminal-completeness-target-only-after-B0-AQFT-W5-and-adapter-no-go-receipts"
    ; honestTOEReceiptTerminalCompletenessTargetStatus-v =
        refl
    ; terminalCompositionTargets =
        canonicalGRQFTTerminalCompositionTargets
    ; terminalCompositionTargetsAreCanonical =
        refl
    ; pullbackCompositionShape =
        "GRQFT-pullback=B0-smooth-geometry-times-compatible-AQFT-local-net-times-W5-authority-stress-energy-over-shared-carrier"
    ; pullbackCompositionShape-v =
        refl
    ; stressEnergyBridgeTargetStatus =
        "stress-energy-bridge-target=W4-authority-backed-T-mu-nu-compatible-with-same-curvature-conservation-and-unit-calibration"
    ; stressEnergyBridgeTargetStatus-v =
        refl
    ; terminalCompletenessTheoremShape =
        "HonestTOEReceipt-terminal-completeness=every-surviving-obligation-discharged-or-reduced-to-explicit-adapter-no-go-assumption-with-no-new-authority"
    ; terminalCompletenessTheoremShape-v =
        refl
    ; terminalCompletenessTheoremTargetSurface =
        canonicalTerminalCompletenessTheoremTarget
    ; weakTerminalClaimOpenStatusGrammar =
        canonicalWeakTerminalClaimOpenStatusGrammar
    ; hardConstructionSteps =
        canonicalGRQFTHardConstructionSteps
    ; hardConstructionStepsAreCanonical =
        refl
    ; adapterIrreducibilityTargets =
        canonicalAdapterIrreducibilityTargets
    ; adapterIrreducibilityTargetsAreCanonical =
        refl
    ; terminalAdapter4Inventory =
        canonicalTerminalAdapter4IrreducibleInputs
    ; terminalAdapter4InventoryAreCanonical =
        refl
    ; terminalAdapter4InventoryShape =
        "final-irreducible-Adapter4-inventory=G_Newton-v_Higgs-f_a-V4vol"
    ; terminalAdapter4InventoryShape-v =
        refl
    ; hierarchyProblemStrategyStatus =
        OpenProblems.canonicalHierarchyProblemStrategyStatus
    ; finalAdapter4Governance =
        OpenProblems.canonicalFinalAdapter4ReceiptGovernance
    ; terminalPromotionFlipCondition =
        OpenProblems.canonicalTerminalClaimPromotionFlipCondition
    ; publicationTierMap =
        OpenProblems.canonicalTerminalPublicationTierMap
    ; finalDeltaSummary =
        OpenProblems.canonicalTerminalPublicationFinalDeltaSummary
    ; finalDeltaSummaryIsCanonical =
        refl
    ; survivingOpenObligations =
        canonicalGRQFTSurvivingOpenObligations
    ; survivingOpenObligationsAreCanonical =
        refl
    ; b0TheoremShape =
        "B0.1-compatible-pro-object-plus-B0.2-flat-disk-plus-B0.3-frame-metric-tower-admits-DCHoTT-manifold-and-torsion-free-G-structure-target"
    ; b0TheoremShape-v =
        refl
    ; aqftConstructionShape =
        "A(O)=promoted-receipts-over-restricted-carrier-quotiented-by-transport-equivalence"
    ; aqftConstructionShape-v =
        refl
    ; receiptCompositionShape =
        "GRQFTReceipt=B0+B1+AQFTNet+signature+Born+vacuum+coupling-adapters"
    ; receiptCompositionShape-v =
        refl
    ; massGapStatus =
        "DASHI-internal-continuum-mass-gap-proved-by-ST3-plus-Banach-receipt-Clay-promotion-open-not-terminal-theorem"
    ; massGapStatus-v =
        refl
    ; cosmologicalConstStatus =
        "sequestering-inhabited-modulo-compact-universe-shift-symmetry-c2-calibration-c3-bound-cosmological-constant-not-solved"
    ; cosmologicalConstStatus-v =
        refl
    ; bornRuleDerivation =
        "irreducible-adapter-2"
    ; bornRuleDerivation-v =
        refl
    ; couplingUnification =
        "Yukawa-ratio-form-conditional-on-MatterPrimeLane-FN-Frobenius-receipts-absolute-Higgs-vev-remains-Adapter4"
    ; couplingUnification-v =
        refl
    ; everythingElseTargetClaim =
        "target-only-inhabited-or-reducible-to-above-four-after-B0-B1-AQFT-W5-request-pack-and-adapter-no-go-theorems"
    ; everythingElseTargetClaim-v =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; noTerminalPromotionWithoutAuthority =
        λ ()
    ; impossibleReceiptHere =
        terminalPromotionReceiptImpossibleHere
    ; compositionBoundary =
        "B0 requires the B0.1 pro-object construction, B0.2 flat formal-disk target, B0.3 frame/metric tower, and DCHoTT G-structure bridge"
        ∷ "Professor-facing B0 caveat: condensed/profinite inverse-limit language is a DASHI-side staging aid, not a proved DCHoTT formal-space equivalence"
        ∷ "Formal disk equivalence remains a target between the refinement limit and DCHoTT formal disks"
        ∷ "AQFT requires depth-filtered local algebras, filtered colimits, quotient operations, isotony, causality, Cauchy time-slice evolution, and descent"
        ∷ "AQFT time-slice remains the CauchyEvolutionReceiptTarget theorem target, not a proved theorem"
        ∷ "adapter irreducibility requires four no-go theorems plus the GUT receipt boundary"
        ∷ "Adapter no-go theorems require explicit proof assumptions for signature, Born state, vacuum selection, coupling calibration, and the GUT boundary"
        ∷ "Terminal composition target is a pullback over one shared carrier: B0 smooth geometry, compatible AQFT local net, and W5 authority-backed stress-energy must agree on the same restrictions"
        ∷ "Stress-energy bridge target is authority-backed T_mu_nu compatible with the same curvature carrier, conservation law, and unit calibration"
        ∷ "GRQFT composition is valid only after B0, B1, AQFTNet, W5 request-pack authority, and all four adapters are supplied"
        ∷ "mass gap is split: local finite-carrier evidence is recorded, while continuumMassGapProvedInDASHI and continuumClayMassGapPromoted remain false"
        ∷ "mass-gap proof landscape records Odusanya/Balaban, Agawa/holonomy, dissolution/no-go campaign, and DASHI pro-object mass-gap lineages without terminal promotion"
        ∷ "Agawa completion is represented as claimed stable IR fixed point plus finite Gribov uniqueness via G4/Morse geometric completeness, not as accepted Clay authority"
        ∷ "cosmological constant sequestering is inhabited modulo compact universe, shift symmetry, c2 calibration, and c3 bound; the cosmological constant is not solved here"
        ∷ "DHR equals Standard Model remains an open carrier-algebra/DHR-endomorphism computation target"
        ∷ "Doplicher-Roberts five hypotheses may be typed before use, but DR reconstructs the compact/super gauge group while DLM supplies authority-backed conditional laneDimension data"
        ∷ "laneDimension is not locally promoted; terminal and Clay promotion remain false"
        ∷ "E8/McKay branching remains bridge metadata; p7 high-energy SU2R is tracked separately from the low-energy Standard Model group"
        ∷ "Born and coupling no-go arguments are recorded as proof strategies, not formalized adapter irreducibility theorems"
        ∷ "no-natural-state, no-preferred-vacuum, and Wald coefficient-selection receipts are complete at receipt-surface level"
        ∷ "Yukawa ratio form is conditional on MatterPrimeLane, FN, and Frobenius receipts; absolute Higgs vev remains Adapter4"
        ∷ "hierarchy strategies are recorded: SUSY stabilizes the Higgs mass parameter without deriving v_Higgs, relaxion has no DASHI receipt for v_Higgs=246 GeV, and accept-as-adapter is the selected governance route"
        ∷ "FinalAdapter4 governance accepts G_Newton, v_Higgs, f_a, and V4vol as the empirical core, but this does not promote the terminal theorem"
        ∷ "terminalClaimPromoted remains false because Clay/external mass-gap promotion and the remaining terminal authorities are still pending"
        ∷ "Strong CP is tracked as an Adapter4 sub-problem with a Peccei-Quinn target that can trade theta-QCD for f_a axion-scale input but does not remove calibration dependence"
        ∷ "final irreducible Adapter4 inventory is {G_Newton, v_Higgs, f_a, V4vol}"
        ∷ "publication tier map is non-promoting: Tier A Paper 1 publishable now, Tier B Papers 2-3 after one focused sprint, Tier C Papers 4-5 require new math, Tier D Papers 6-7 require Clay/external acceptance or new terminal integration"
        ∷ "Reeh-Schlieder is no longer a Paper 3 blocker once dependent receipts are accepted"
        ∷ "final delta summary: Paper1 2-4 weeks writing; Paper2 flag split plus Wellen cite 1-2 weeks; Paper3 quotient/cites/Reeh no longer blocker after dependent receipts; Paper4 and Paper6 months-years; Paper7 after all prior closures"
        ∷ "Papers 1-3 are fully executable from current repo state; Papers 4-7 remain open"
        ∷ "HonestTOEReceipt is a terminal-completeness target only after B0, AQFT, W5 authority, and adapter no-go receipts are inhabited"
        ∷ "Terminal completeness theorem target requires every surviving obligation to be discharged or reduced to explicit adapter no-go assumptions without adding new authority"
        ∷ "physical-accessibility four-way terminal grammar is available only as finite classifier evidence, not terminal completeness"
        ∷ "weak terminal claim promotion is true only modulo MinimalPostulateSetForFullChainClosure"
        ∷ "the fourth minimal postulate, UniformBalaban-or-AgawaIRFixedPoint, is a genuine open Clay/external-acceptance gate"
        ∷ "candidate DASHI recursion is not accepted authority for the fourth minimal postulate"
        ∷ "the terminal everything-else sentence is recorded as a target claim, not a promoted theorem"
        ∷ "unqualified terminal claim promotion remains false until B0, AQFT, DHR authority, stress-energy/Wald, Clay/external mass-gap acceptance, and adapter authorities are actually closed"
        ∷ []
    }

data Paper7FinalProductStatus : Set where
  paper7FinalProductBlockedOnUpstreamReceipts :
    Paper7FinalProductStatus

record Paper7Gate1To7ReceiptBundle : Setω where
  field
    gate1Receipt :
      Gate1.CarrierToPhysicsInterpretationReceipt

    gate2Receipt :
      Gate2.S8NatSpectralWitnessTestSlice

    gate3Receipt :
      Gate3.YangMillsFieldEquationReceipt

    gate4Receipt :
      Gate4.FactorVecDiscreteMetricTensorSurface

    gate5Receipt :
      Gate5.DiscreteTimeHilbertDepthStoneReceipt

    gate6Receipt :
      Gate6.DHRTensorDualGroupReconstructionReceipt

    gate7MatterReceipt :
      Gate7Matter.MatterRepresentationReceiptSurface

    gate7HiggsReceipt :
      Gate7Higgs.HiggsSymmetryBreakingReceipt

    gate7CKMReceipt :
      Gate7CKM.CKMCarrierMixingReceipt

    gate2TerminalClaimPromotedIsFalse :
      Gate2.S8NatSpectralWitnessTestSlice.terminalClaimPromoted
        gate2Receipt
      ≡
      false

    gate3TerminalClaimPromotedIsFalse :
      Gate3.YangMillsFieldEquationReceipt.terminalClaimPromoted
        gate3Receipt
      ≡
      false

    gate4FirstPrimitiveIsStressEnergyCompatibility :
      Gate4.FactorVecValuationDependentNonFlatSiteMetricSurface.firstMetricPrimitiveAfterUnitContractedBianchi
        (Gate4.FactorVecDiscreteMetricTensorSurface.valuationDependentNonFlatSiteMetricRequired
          gate4Receipt)
      ≡
      Gate4.missingValuationStressEnergyCompatibilityComputation

    gate4FirstStressEnergyCompatibilitySubprimitiveIsTensorCandidate :
      Gate4.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
        (Gate4.FactorVecValuationDependentNonFlatSiteMetricSurface.valuationUnitStressEnergyCompatibilityRequest
          (Gate4.FactorVecDiscreteMetricTensorSurface.valuationDependentNonFlatSiteMetricRequired
            gate4Receipt))
      ≡
      Gate4.missingValuationStressEnergyTensorCandidate

    gate4FirstTensorCandidateSubprimitiveIsComponentFamily :
      Gate4.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingTensorCandidatePrimitive
        (Gate4.FactorVecValuationDependentNonFlatSiteMetricSurface.valuationUnitStressEnergyCompatibilityRequest
          (Gate4.FactorVecDiscreteMetricTensorSurface.valuationDependentNonFlatSiteMetricRequired
            gate4Receipt))
      ≡
      Gate4.missingValuationStressEnergyTensorComponentFamily

    gate5SelfAdjointColimitGeneratorPromotedIsFalse :
      Gate5.DiscreteTimeHilbertDepthStoneReceipt.selfAdjointColimitGeneratorPromoted
        gate5Receipt
      ≡
      false

    gate5RemainingPrimitivesAreCanonical :
      Gate5.DiscreteTimeHilbertDepthStoneReceipt.remainingPrimitives
        gate5Receipt
      ≡
      Gate5.canonicalHilbertDepthStoneMissingPrimitives

    gate6TerminalClaimPromotedIsFalse :
      Gate6.DHRTensorDualGroupReconstructionReceipt.terminalClaimPromoted
        gate6Receipt
      ≡
      false

    gate6BlockersAreCanonical :
      Gate6.DHRTensorDualGroupReconstructionReceipt.blockers
        gate6Receipt
      ≡
      Gate6.canonicalDHRTensorDualGroupBlockers

    gate7MatterRepresentationsDerivedIsFalse :
      Gate7Matter.MatterRepresentationReceiptSurface.matterRepresentationsDerived
        gate7MatterReceipt
      ≡
      false

    gate7HiggsPromotedIsFalse :
      Gate7Higgs.HiggsSymmetryBreakingReceipt.higgsSymmetryBreakingPromoted
        gate7HiggsReceipt
      ≡
      false

    gate7CKMPromotedIsFalse :
      Gate7CKM.CKMCarrierMixingReceipt.ckmCarrierMixingPromoted
        gate7CKMReceipt
      ≡
      false

    gate7CKMFirstMissingIsCarrierMixingTheorem :
      Gate7CKM.CKMCarrierMixingReceipt.firstMissing
        gate7CKMReceipt
      ≡
      Gate7CKM.missingCarrierMixingTheorem

    gate7CKMHiggsAdapter4BoundaryStillRequired :
      Gate7Higgs.vHiggsAdapter4Boundary
        (Gate7CKM.CKMCarrierMixingDependencyReceipt.higgsDependency
          Gate7CKM.canonicalCKMCarrierMixingDependencyReceipt)
      ≡
      true

    sixPostulateAuthorityLedger :
      SixPostulateAuthorityLedger

    sixPostulateAuthorityLedgerNotPromoted :
      SixPostulateAuthorityLedger.ledgerPromoted sixPostulateAuthorityLedger
      ≡
      false

    candidate256PhysicalCalibrationExternalStatus :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    candidate256PhysicalCalibrationExternalBlockedFieldsAreCanonical :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.blockedExternalFields
        candidate256PhysicalCalibrationExternalStatus
      ≡
      W4Calibration.canonicalCandidate256PhysicalCalibrationExternalBlockedFields

    candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

open Paper7Gate1To7ReceiptBundle public

canonicalPaper7Gate1To7ReceiptBundle :
  Paper7Gate1To7ReceiptBundle
canonicalPaper7Gate1To7ReceiptBundle =
  record
    { gate1Receipt =
        Gate1.canonicalCarrierToPhysicsInterpretationReceipt
    ; gate2Receipt =
        Gate2.canonicalS8NatSpectralWitnessTestSlice
    ; gate3Receipt =
        Gate3.canonicalYangMillsFieldEquationReceipt
    ; gate4Receipt =
        Gate4.canonicalFactorVecDiscreteMetricTensorSurface
    ; gate5Receipt =
        Gate5.onePointDiscreteTimeHilbertDepthStoneReceipt
    ; gate6Receipt =
        Gate6.canonicalDHRTensorDualGroupReconstructionReceipt
    ; gate7MatterReceipt =
        Gate7Matter.canonicalMatterRepresentationReceiptSurface
    ; gate7HiggsReceipt =
        Gate7Higgs.canonicalHiggsSymmetryBreakingReceipt
    ; gate7CKMReceipt =
        Gate7CKM.canonicalCKMCarrierMixingReceipt
    ; gate2TerminalClaimPromotedIsFalse =
        refl
    ; gate3TerminalClaimPromotedIsFalse =
        refl
    ; gate4FirstPrimitiveIsStressEnergyCompatibility =
        refl
    ; gate4FirstStressEnergyCompatibilitySubprimitiveIsTensorCandidate =
        refl
    ; gate4FirstTensorCandidateSubprimitiveIsComponentFamily =
        refl
    ; gate5SelfAdjointColimitGeneratorPromotedIsFalse =
        refl
    ; gate5RemainingPrimitivesAreCanonical =
        Gate5.DiscreteTimeHilbertDepthStoneReceipt.remainingPrimitivesAreCanonical
          Gate5.onePointDiscreteTimeHilbertDepthStoneReceipt
    ; gate6TerminalClaimPromotedIsFalse =
        refl
    ; gate6BlockersAreCanonical =
        Gate6.DHRTensorDualGroupReconstructionReceipt.blockersAreCanonical
          Gate6.canonicalDHRTensorDualGroupReconstructionReceipt
    ; gate7MatterRepresentationsDerivedIsFalse =
        refl
    ; gate7HiggsPromotedIsFalse =
        refl
    ; gate7CKMPromotedIsFalse =
        refl
    ; gate7CKMFirstMissingIsCarrierMixingTheorem =
        refl
    ; gate7CKMHiggsAdapter4BoundaryStillRequired =
        Gate7CKM.CKMCarrierMixingDependencyReceipt.higgsAdapter4BoundaryStillRequired
          Gate7CKM.canonicalCKMCarrierMixingDependencyReceipt
    ; sixPostulateAuthorityLedger =
        canonicalSixPostulateAuthorityLedger
    ; sixPostulateAuthorityLedgerNotPromoted =
        refl
    ; candidate256PhysicalCalibrationExternalStatus =
        W4Calibration.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; candidate256PhysicalCalibrationExternalBlockedFieldsAreCanonical =
        refl
    ; candidate256PhysicalCalibrationExternalReceiptImpossibleWithoutExternalAuthority =
        W4Calibration.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }

canonicalPaper7FirstUninhabitedUpstreamSymbols :
  List String
canonicalPaper7FirstUninhabitedUpstreamSymbols =
  "Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
  ∷ "Gate1/Gate6.blockedByMissingGate1GaugeRepresentationSemantics"
  ∷ "Gate2.S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
  ∷ "Gate3.missingSFGCFibreRepresentationIntoSU3Carrier"
  ∷ "Gate3.missingNonFlatSFGCSite2DConnectionCurvature"
  ∷ "Gate3.missingFieldStrengthTransportActionOnSelectedGaugeBundle"
  ∷ "Gate3.missingLieAlgebraCarrierForSelectedFiniteGaugeSector"
  ∷ "Gate3.missingVariationPairingForSelectedHodgeStar"
  ∷ "Gate4.missingValuationMatterReceiptInterface"
  ∷ "Gate4.missingMetricCompatibility"
  ∷ "Gate4.missingStressEnergyCompatibilityForContractedBianchi"
  ∷ "Gate4.W4MatterStressEnergyInterfaceReceipt"
  ∷ "Gate5.Stone.targetGlobalNoncollapsedPhysicalPhaseSpace"
  ∷ "Gate8.term4.missingPhysicalStoneHilbertCarrierForYMQuotient"
  ∷ "Gate8.term4.missingStoneGeneratorYMHamiltonianIdentification"
  ∷ "Gate8.term4.missingSelectedCarrierLowerBoundTransportToRealYM"
  ∷ "Gate5.missingNoncollapsedPhysicalPhaseSpaceCarrier"
  ∷ "Gate5.GNS.missingCyclicSeparatingVector"
  ∷ "Gate6.residualGlobalForeignLaneIdentityRequiresExplicitWitness"
  ∷ "Gate6.missingDASHILocalAlgebra"
  ∷ "Gate6.blockedByMissingGate1GaugeRepresentationSemantics"
  ∷ "Gate7CKM.missingYukawaDHRIntertwinerCompatibility"
  ∷ "Gate7CKM.missingCKMProductClosureWitness"
  ∷ "Gate7CKM.missingUnitarityResidualWitness"
  ∷ "Gate7CKM.missingCarrierMixingTheorem"
  ∷ "Gate7CKM.vHiggsAdapter4Boundary"
  ∷ "Gate7CKM.CKMExplicitFNChargeTable.upHiggsAdapter4Socket"
  ∷ "W4.Candidate256PhysicalCalibrationExternalReceipt=impossibleWithoutExternalAuthority"
  ∷ "W4.missingCandidate256CalibrationReceiptForMatterInterface"
  ∷ "SixPostulateAuthorityLedger.UniformBalaban-or-AgawaIRFixedPoint"
  ∷ "ContinuumClayMassGapReceiptObligation.clayExternalAcceptanceOfYMAQFTMassGap"
  ∷ []

record Paper7FinalProductReceipt : Setω where
  field
    status :
      Paper7FinalProductStatus

    gate1To7ReceiptBundle :
      Paper7Gate1To7ReceiptBundle

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    exactFirstUninhabitedUpstreamSymbols :
      List String

    exactFirstUninhabitedUpstreamSymbolsAreCanonical :
      exactFirstUninhabitedUpstreamSymbols
      ≡
      canonicalPaper7FirstUninhabitedUpstreamSymbols

    blockedFinalProductBoundary :
      List String

open Paper7FinalProductReceipt public

canonicalPaper7FinalProductReceipt :
  Paper7FinalProductReceipt
canonicalPaper7FinalProductReceipt =
  record
    { status =
        paper7FinalProductBlockedOnUpstreamReceipts
    ; gate1To7ReceiptBundle =
        canonicalPaper7Gate1To7ReceiptBundle
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; exactFirstUninhabitedUpstreamSymbols =
        canonicalPaper7FirstUninhabitedUpstreamSymbols
    ; exactFirstUninhabitedUpstreamSymbolsAreCanonical =
        refl
    ; blockedFinalProductBoundary =
        "Gate 1-7 receipt bundle is now recorded explicitly for Paper 7 composition."
        ∷ "Gate 1/Gate 6 agreement is blocked at missingExactStandardModelCarrierFunctorMatch."
        ∷ "Gate 2 terminal claim remains false; u1/l6 conditional finite-carrier spectral-bound wiring is local-only, not transported to the real YM quotient, and the global theorem remains blocked at missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient."
        ∷ "Gate 3 terminal claim remains false; the m1/u2/m2 receipt blocks at missingNonFlatSFGCSite2DConnectionCurvature, missingFieldStrengthTransportActionOnSelectedGaugeBundle, missingSFGCFibreRepresentationIntoSU3Carrier, and missingVariationPairingForSelectedHodgeStar."
        ∷ "Gate 4 stages supported stress-energy and non-flat metric-tower receipts, including m3/u4 GRSelectedChain fail-closed handoffs; the local zero-table tensor candidate is staged, while the selected GR/source chain remains blocked at missingMetricCompatibility, missingValuationMatterReceiptInterface, missingCandidate256CalibrationReceiptForMatterInterface, and missingStressEnergyCompatibilityForContractedBianchi."
        ∷ "Gate 5 finite selected projection/scalar progress is locally staged, but the physical Stone route starts from targetGlobalNoncollapsedPhysicalPhaseSpace / missingNoncollapsedPhysicalPhaseSpaceCarrier and keeps selfAdjointColimitGeneratorPromoted fixed false."
        ∷ "Gate8.term4 records the finite Stone generator and selected-carrier lower-bound receipts now available; physical Stone generator = YM Hamiltonian, selected lower-bound transport to real YM, and Clay/YM promotion all remain false."
        ∷ "Gate 6 selected foreign-identity packaging is staged, but DHR field separation still requires residualGlobalForeignLaneIdentityRequiresExplicitWitness; AQFT first-missing-chain progress now leaves missingDASHILocalAlgebra and blockedByMissingGate1GaugeRepresentationSemantics as the next residuals."
        ∷ "Gate 7 CKM/DHR agreement is blocked at missingYukawaDHRIntertwinerCompatibility; m5/m6/l1 keeps Matter.MixingMatrix opaque, Wolfenstein/Jarlskog target-only, missingCKMProductClosureWitness, missingUnitarityResidualWitness, missingCarrierMixingTheorem, vHiggsAdapter4Boundary, and the explicit FN up-Higgs Adapter4 socket open."
        ∷ "Candidate256 physical calibration remains fail-closed at Candidate256PhysicalCalibrationExternalReceipt=impossibleWithoutExternalAuthority."
        ∷ "The six-postulate authority ledger is recorded only as modulo accounting; UniformBalaban-or-AgawaIRFixedPoint, Clay acceptance, W3/W4/W5 authority, and terminal promotion remain uninhabited."
        ∷ "Clay/external acceptance remains open at clayExternalAcceptanceOfYMAQFTMassGap."
        ∷ "DASHI/Everything.agda is no longer a terminal blocker when the root check exits 0; terminal promotion still waits on the mathematical and authority receipts above."
        ∷ "Final Paper 7 product receipt remains blocked; terminalClaimPromoted is fixed false until all upstream receipts and authority boundaries are inhabited."
        ∷ []
    }

record Gate6Gate1Gate8LedgerWorkerWaveReceipt : Setω where
  field
    gate1TrancheReceipt :
      Gate1.Gate1FilteredColimitDHRCompatibilityTrancheReceipt

    gate6TrancheReceipt :
      Gate6.Gate6DHRWorkerTrancheProgressReceipt

    gate8Bundle :
      Paper7Gate1To7ReceiptBundle

    authorityLedger :
      SixPostulateAuthorityLedger

    candidate256ExternalStatus :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    firstUninhabitedUpstreamSymbols :
      List String

    firstUninhabitedUpstreamSymbolsAreCanonical :
      firstUninhabitedUpstreamSymbols
      ≡
      canonicalPaper7FirstUninhabitedUpstreamSymbols

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    uniformBalabanOrAgawaIRFixedPointStillExternal :
      Bool

    uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue :
      uniformBalabanOrAgawaIRFixedPointStillExternal ≡ true

    candidate256PhysicalCalibrationExternalReceiptImpossible :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    w3w4w5ClayAuthorityFabricated :
      Bool

    w3w4w5ClayAuthorityFabricatedIsFalse :
      w3w4w5ClayAuthorityFabricated ≡ false

    exactRemainingBlocker :
      String

    workerWaveBoundary :
      List String

open Gate6Gate1Gate8LedgerWorkerWaveReceipt public

canonicalGate6Gate1Gate8LedgerWorkerWaveReceipt :
  Gate6Gate1Gate8LedgerWorkerWaveReceipt
canonicalGate6Gate1Gate8LedgerWorkerWaveReceipt =
  record
    { gate1TrancheReceipt =
        Gate1.canonicalGate1FilteredColimitDHRCompatibilityTrancheReceipt
    ; gate6TrancheReceipt =
        Gate6.canonicalGate6DHRWorkerTrancheProgressReceipt
    ; gate8Bundle =
        canonicalPaper7Gate1To7ReceiptBundle
    ; authorityLedger =
        canonicalSixPostulateAuthorityLedger
    ; candidate256ExternalStatus =
        W4Calibration.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; firstUninhabitedUpstreamSymbols =
        canonicalPaper7FirstUninhabitedUpstreamSymbols
    ; firstUninhabitedUpstreamSymbolsAreCanonical =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; uniformBalabanOrAgawaIRFixedPointStillExternal =
        true
    ; uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue =
        refl
    ; candidate256PhysicalCalibrationExternalReceiptImpossible =
        W4Calibration.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; w3w4w5ClayAuthorityFabricated =
        false
    ; w3w4w5ClayAuthorityFabricatedIsFalse =
        refl
    ; exactRemainingBlocker =
        "Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
    ; workerWaveBoundary =
        "Gate6/Gate1/Gate8/Ledger worker wave records supplied DHR evidence surfaces without promoting terminal closure"
        ∷ "Gate1 filtered-colimit preservation and DHR-sector compatibility remain missing semantic primitives"
        ∷ "Gate6 exposes localised endomorphism, transport, statistics, DR H1-H5, tensor, dual, Frobenius, and hexagon target surfaces, but does not close naturality, hexagon coherence, DR reconstruction, or SM matching"
        ∷ "Gate8 keeps terminalClaimPromoted=false and the first uninhabited upstream symbols canonical"
        ∷ "The six-postulate ledger remains non-promoting; UniformBalaban-or-AgawaIRFixedPoint stays external"
        ∷ "Candidate256 physical calibration remains impossible without external authority; no W3/W4/W5/Clay authority token is fabricated"
        ∷ []
    }

data Gate4StressEnergyTerminalLedgerWorkerWave2Status : Set where
  gate4StressEnergyTerminalLedgerWorkerWave2RecordedNoPromotion :
    Gate4StressEnergyTerminalLedgerWorkerWave2Status

record Gate4StressEnergyTerminalLedgerWorkerWave2Receipt : Setω where
  field
    status :
      Gate4StressEnergyTerminalLedgerWorkerWave2Status

    gate4StressEnergyReceipt :
      Gate4.FactorVecGate4StressEnergyConservationSourceReceipt

    dashiMatterLagrangianCouplingReceipt :
      Gate4.FactorVecDASHIMatterLagrangianCouplingReceipt

    valuationMatterReceiptInterfaceFailClosedReceipt :
      Gate4.FactorVecValuationMatterReceiptInterfaceFailClosedReceipt

    gate4DASHIMatterStressEnergyFinalReceipt :
      Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt

    grGate4SourcedEinsteinFailClosedHandoffReceipt :
      Gate4GR.GRGate4SourcedEinsteinFailClosedHandoffReceipt

    grDiscreteRicciGate4SelectedChainFailClosedReceipt :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt

    w4HardHaltReceipt :
      W4Stress.W4MatterStressEnergyInterfaceContinuationWave2HardHaltReceipt

    w4Gate4HardHaltReceipt :
      W4Stress.W4MatterStressEnergyGate4HardHaltReceipt

    gate8Bundle :
      Paper7Gate1To7ReceiptBundle

    gate4OriginalCompatibilityFirstMissing :
      Gate4.FactorVecStressEnergyCompatibilityMissingPrimitive

    gate4OriginalCompatibilityFirstMissingIsTensorCandidate :
      gate4OriginalCompatibilityFirstMissing
      ≡
      Gate4.missingValuationStressEnergyTensorCandidate

    gate4LocalRemainingBlocker :
      Gate4.FactorVecStressEnergyCompatibilityMissingPrimitive

    gate4LocalRemainingBlockerIsMatterReceiptInterface :
      gate4LocalRemainingBlocker
      ≡
      Gate4.missingValuationMatterReceiptInterface

    gate4FinalReceiptLocalBlocker :
      Gate4.FactorVecStressEnergyCompatibilityMissingPrimitive

    gate4FinalReceiptLocalBlockerIsMatterReceiptInterface :
      gate4FinalReceiptLocalBlocker
      ≡
      Gate4.missingValuationMatterReceiptInterface

    w4FirstAuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4FirstAuthorityBlockerIsCandidate256 :
      w4FirstAuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    w4Gate4HardHaltFirstAuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4Gate4HardHaltFirstAuthorityBlockerIsCandidate256 :
      w4Gate4HardHaltFirstAuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    constructsAuthorityBackedStressEnergyTensor :
      Bool

    constructsAuthorityBackedStressEnergyTensorIsFalse :
      constructsAuthorityBackedStressEnergyTensor ≡ false

    promotesSourcedEinsteinLaw :
      Bool

    promotesSourcedEinsteinLawIsFalse :
      promotesSourcedEinsteinLaw ≡ false

    grSelectedNonFlatGeometryBlockerIsMetricCompatibility :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlocker
        grDiscreteRicciGate4SelectedChainFailClosedReceipt
      ≡
      Gate4GR.missingMetricCompatibility

    grSourcedEinsteinAttachmentBlockerIsStressEnergyCompatibility :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostLocalGeometryBlocker
        grDiscreteRicciGate4SelectedChainFailClosedReceipt
      ≡
      Gate4GR.missingStressEnergyCompatibilityForContractedBianchi

    grSourcedEinsteinAttachmentBlocked :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.sourcedEinsteinAttachmentBlocked
      grDiscreteRicciGate4SelectedChainFailClosedReceipt
      ≡
      false

    grSelectedChainPromotedToNonFlatGRIsFalse :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGR
        grDiscreteRicciGate4SelectedChainFailClosedReceipt
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    firstTerminalBlocker :
      String

    terminalLedgerBoundary :
      List String

canonicalGate4StressEnergyTerminalLedgerWorkerWave2Receipt :
  Gate4StressEnergyTerminalLedgerWorkerWave2Receipt
canonicalGate4StressEnergyTerminalLedgerWorkerWave2Receipt =
  record
    { status =
        gate4StressEnergyTerminalLedgerWorkerWave2RecordedNoPromotion
    ; gate4StressEnergyReceipt =
        Gate4.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; dashiMatterLagrangianCouplingReceipt =
        Gate4.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; valuationMatterReceiptInterfaceFailClosedReceipt =
        Gate4.canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; gate4DASHIMatterStressEnergyFinalReceipt =
        Gate4.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; grGate4SourcedEinsteinFailClosedHandoffReceipt =
        Gate4GR.canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
    ; grDiscreteRicciGate4SelectedChainFailClosedReceipt =
        Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; w4HardHaltReceipt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceContinuationWave2HardHaltReceipt
    ; w4Gate4HardHaltReceipt =
        W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; gate8Bundle =
        canonicalPaper7Gate1To7ReceiptBundle
    ; gate4OriginalCompatibilityFirstMissing =
        Gate4.FactorVecGate4StressEnergyConservationSourceReceipt.originalCompatibilityRequestFirstMissing
          Gate4.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; gate4OriginalCompatibilityFirstMissingIsTensorCandidate =
        refl
    ; gate4LocalRemainingBlocker =
        Gate4.FactorVecGate4StressEnergyConservationSourceReceipt.exactRemainingBlocker
          Gate4.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; gate4LocalRemainingBlockerIsMatterReceiptInterface =
        refl
    ; gate4FinalReceiptLocalBlocker =
        Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.matterReceiptInterfaceRemainingBlocker
          Gate4.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; gate4FinalReceiptLocalBlockerIsMatterReceiptInterface =
        Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.matterReceiptInterfaceRemainingBlockerIsExact
          Gate4.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; w4FirstAuthorityBlocker =
        W4Stress.W4MatterStressEnergyInterfaceContinuationWave2HardHaltReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyInterfaceContinuationWave2HardHaltReceipt
    ; w4FirstAuthorityBlockerIsCandidate256 =
        refl
    ; w4Gate4HardHaltFirstAuthorityBlocker =
        W4Stress.W4MatterStressEnergyGate4HardHaltReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; w4Gate4HardHaltFirstAuthorityBlockerIsCandidate256 =
        W4Stress.W4MatterStressEnergyGate4HardHaltReceipt.firstAuthorityInterfaceBlockerIsCandidate256
          W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; constructsAuthorityBackedStressEnergyTensor =
        false
    ; constructsAuthorityBackedStressEnergyTensorIsFalse =
        refl
    ; promotesSourcedEinsteinLaw =
        false
    ; promotesSourcedEinsteinLawIsFalse =
        refl
    ; grSelectedNonFlatGeometryBlockerIsMetricCompatibility =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; grSourcedEinsteinAttachmentBlockerIsStressEnergyCompatibility =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostLocalGeometryBlockerIsStressEnergyCompatibility
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; grSourcedEinsteinAttachmentBlocked =
        Gate4Ricci.grDiscreteRicciGate4SourcedEinsteinAttachmentBlocked
    ; grSelectedChainPromotedToNonFlatGRIsFalse =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGRIsFalse
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; firstTerminalBlocker =
        "Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
    ; terminalLedgerBoundary =
        "Gate4-SE continuation wave 2 wires the owned flat source-coupling and conservation staging into the terminal ledger"
        ∷ "u3 records DASHIMatterLagrangianCouplingReceipt as a local design receipt consumed only by the bounded FactorVec zero-table tensor candidate"
        ∷ "u3 records a fail-closed concrete interface audit: local FactorVec plus zero-table term are constructible, while YMConnectionCarrier, SelectedFiniteRMetric interface wiring, StressEnergyTensorCarrier, and Candidate256 authority remain missing"
        ∷ "u3 current Gate4 hard halt is consumed through FactorVecGate4DASHIMatterStressEnergyFinalReceipt and W4MatterStressEnergyGate4HardHaltReceipt"
        ∷ "m3/u4 current Gate4 GR handoff is consumed through GRGate4SourcedEinsteinFailClosedHandoffReceipt and GRDiscreteRicciGate4SelectedChainFailClosedReceipt"
        ∷ "The selected non-flat geometry chain remains blocked at missingMetricCompatibility"
        ∷ "The local Gate4 stress-energy queue advances only to missingValuationMatterReceiptInterface"
        ∷ "The global sourced-Einstein attachment remains blocked at missingStressEnergyCompatibilityForContractedBianchi"
        ∷ "The W4 authority halt remains first-blocked at missingCandidate256CalibrationReceiptForMatterInterface"
        ∷ "No authority-backed StressEnergyTensor, sourced Einstein law, or non-flat GR promotion is constructed"
        ∷ "Gate8 keeps terminalClaimPromoted=false and the terminal first blocker remains Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
        ∷ []
    }

record Lower6GateReceiptWiringLedger : Setω where
  field
    gate2RealCarrierAndHamiltonianBlockerReceipt :
      Gate2.S8Lower6RealCarrierAndHamiltonianBlockerReceipt

    gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt :
      Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt

    gate2ConditionalFiniteCarrierBoundDoesNotTransportToRealYM :
      Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYM
        gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt
      ≡
      false

    gate2ConditionalFiniteCarrierFirstBlockerIsSelfAdjointYangMillsHamiltonian :
      Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.firstRealCarrierBlocker
        gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt
      ≡
      Gate2S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    gate2ConditionalFiniteCarrierSpectralGapPromotedIsFalse :
      Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.spectralGapPromoted
        gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt
      ≡
      false

    gate2ConditionalFiniteCarrierTerminalClaimFalse :
      Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.terminalClaimPromoted
        gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt
      ≡
      false

    gate5StoneGeneratorBlockerReceipt :
      Gate5.BoundedStoneGeneratorSpectralGapInterpretationReceipt

    gate8Term4StoneYMHamiltonianGapBridgeReceipt :
      Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt

    gate8Term4FiniteSelectedCarrierBridgeRecorded :
      Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.finiteSelectedCarrierBridgeRecorded
        gate8Term4StoneYMHamiltonianGapBridgeReceipt
      ≡
      true

    gate8Term4PhysicalStoneYMSpectralGapPromotedFalse :
      Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.physicalStoneYMSpectralGapPromoted
        gate8Term4StoneYMHamiltonianGapBridgeReceipt
      ≡
      false

    gate8Term4FirstBlockerIsPhysicalStoneHilbertCarrier :
      Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.firstExactBlocker
        gate8Term4StoneYMHamiltonianGapBridgeReceipt
      ≡
      Gate8Term4.missingPhysicalStoneHilbertCarrierForYMQuotient

    gate5FirstRemainingTarget :
      Gate5.StoneGeneratorSpectralGapRemainingTarget

    gate5FirstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace :
      gate5FirstRemainingTarget
      ≡
      Gate5.targetGlobalNoncollapsedPhysicalPhaseSpace

    candidate256CalibrationGateWiringLedger :
      W4Calibration.Candidate256PhysicalCalibrationGateReceiptWiringLedger

    balancedTritRestEnergyReceipt :
      Dispersion.BalancedTritRestEnergyReceipt

    formalE0EqualsMC2DispersionSurface :
      Dispersion.FormalE0EqualsMC2DispersionTheoremSurface 1 1 1

    formalTaylorKineticMatchingReceipt :
      Dispersion.FormalTaylorKineticMatchingReceipt 1 1 1

    formalTaylorAnalyticTheoremPromotedIsFalse :
      Dispersion.FormalTaylorKineticMatchingReceipt.analyticTaylorTheoremPromoted
        formalTaylorKineticMatchingReceipt
      ≡
      false

    formalTaylorPhysicalUnitCalibrationPromotedIsFalse :
      Dispersion.FormalTaylorKineticMatchingReceipt.physicalUnitCalibrationPromoted
        formalTaylorKineticMatchingReceipt
      ≡
      false

    paper7FinalProductReceipt :
      Paper7FinalProductReceipt

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    lower6LedgerPromoted :
      Bool

    lower6LedgerPromotedIsFalse :
      lower6LedgerPromoted ≡ false

    wiringBoundary :
      List String

open Lower6GateReceiptWiringLedger public

canonicalLower6GateReceiptWiringLedger :
  Lower6GateReceiptWiringLedger
canonicalLower6GateReceiptWiringLedger =
  record
    { gate2RealCarrierAndHamiltonianBlockerReceipt =
        Gate2.canonicalS8Lower6RealCarrierAndHamiltonianBlockerReceipt
    ; gate2ConditionalFiniteCarrierSpectralBoundWiringReceipt =
        Gate2.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; gate2ConditionalFiniteCarrierBoundDoesNotTransportToRealYM =
        Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.finiteCarrierBoundTransportedToRealYMIsFalse
          Gate2.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; gate2ConditionalFiniteCarrierFirstBlockerIsSelfAdjointYangMillsHamiltonian =
        Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.firstRealCarrierBlockerIsSelfAdjointYangMillsHamiltonian
          Gate2.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; gate2ConditionalFiniteCarrierSpectralGapPromotedIsFalse =
        Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.spectralGapPromotedIsFalse
          Gate2.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; gate2ConditionalFiniteCarrierTerminalClaimFalse =
        Gate2.S8NatConditionalFiniteCarrierSpectralBoundWiringReceipt.terminalClaimPromotedIsFalse
          Gate2.canonicalS8NatConditionalFiniteCarrierSpectralBoundWiringReceipt
    ; gate5StoneGeneratorBlockerReceipt =
        Gate5.onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt
    ; gate8Term4StoneYMHamiltonianGapBridgeReceipt =
        Gate8Term4.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; gate8Term4FiniteSelectedCarrierBridgeRecorded =
        Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.finiteSelectedCarrierBridgeRecordedIsTrue
          Gate8Term4.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; gate8Term4PhysicalStoneYMSpectralGapPromotedFalse =
        Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.physicalStoneYMSpectralGapPromotedIsFalse
          Gate8Term4.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; gate8Term4FirstBlockerIsPhysicalStoneHilbertCarrier =
        Gate8Term4.Gate8Term4StoneYMHamiltonianGapBridgeReceipt.firstExactBlockerIsPhysicalStoneHilbertCarrier
          Gate8Term4.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; gate5FirstRemainingTarget =
        Gate5.targetGlobalNoncollapsedPhysicalPhaseSpace
    ; gate5FirstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace =
        refl
    ; candidate256CalibrationGateWiringLedger =
        W4Calibration.canonicalCandidate256PhysicalCalibrationGateReceiptWiringLedger
    ; balancedTritRestEnergyReceipt =
        Dispersion.canonicalBalancedTritRestEnergyReceipt
    ; formalE0EqualsMC2DispersionSurface =
        Dispersion.formalE0EqualsMC2DispersionTheoremSurface 1 1 1
    ; formalTaylorKineticMatchingReceipt =
        Dispersion.formalTaylorKineticMatchingReceipt 1 1 1
    ; formalTaylorAnalyticTheoremPromotedIsFalse =
        Dispersion.FormalTaylorKineticMatchingReceipt.analyticTaylorTheoremPromotedIsFalse
          (Dispersion.formalTaylorKineticMatchingReceipt 1 1 1)
    ; formalTaylorPhysicalUnitCalibrationPromotedIsFalse =
        Dispersion.FormalTaylorKineticMatchingReceipt.physicalUnitCalibrationPromotedIsFalse
          (Dispersion.formalTaylorKineticMatchingReceipt 1 1 1)
    ; paper7FinalProductReceipt =
        canonicalPaper7FinalProductReceipt
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; lower6LedgerPromoted =
        false
    ; lower6LedgerPromotedIsFalse =
        refl
    ; wiringBoundary =
        "Lower6 ledger wires Gate 2 real/non-Nat S8 staging and the self-adjoint Hamiltonian blocker receipt"
        ∷ "u1/l6 conditional finite-carrier spectral-bound wiring is consumed only as local Nat evidence; finite-to-real YM transport is false"
        ∷ "The first Gate2/S8 real-carrier blocker remains missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "Gate8.term4 consumes the finite Stone generator plus Gate2 selected lower-bound receipts, but keeps physical Stone generator = YM Hamiltonian and physical spectral lower-bound promotion false"
        ∷ "Gate8.term4 first exact blocker is missingPhysicalStoneHilbertCarrierForYMQuotient"
        ∷ "l4 formal Taylor kinetic matching records the symbolic Nat E0 = m c^2 condition but promotes no analytic Taylor theorem or physical-unit calibration"
        ∷ "Gate 5 Stone receipt is bounded; its first remaining target is targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ "Candidate256 calibration is wired only through the fail-closed external receipt queue"
        ∷ "Balanced-trit rest energy records the formal E0 = m c^2 dispersion surface over the Nat surrogate"
        ∷ "The Paper 7 final product remains blocked and terminalClaimPromoted stays false"
        ∷ []
    }

lower6GateReceiptWiringLedgerTerminalClaimFalse :
  Lower6GateReceiptWiringLedger.terminalClaimPromoted
    canonicalLower6GateReceiptWiringLedger
  ≡
  false
lower6GateReceiptWiringLedgerTerminalClaimFalse =
  refl

data TerminalAuthorityFinalLedgerWorkerWave3Status : Set where
  terminalAuthorityFinalLedgerWorkerWave3RecordedNoPromotion :
    TerminalAuthorityFinalLedgerWorkerWave3Status

record TerminalAuthorityFinalLedgerWorkerWave3Receipt : Setω where
  field
    status :
      TerminalAuthorityFinalLedgerWorkerWave3Status

    paper7FinalProductReceipt :
      Paper7FinalProductReceipt

    gate4StressEnergyWave2Receipt :
      Gate4StressEnergyTerminalLedgerWorkerWave2Receipt

    gate3M1U2M2WorkerReceipt :
      Gate3.YMSFGCGate3M1U2M2WorkerReceipt

    gate3M1ExactBlockerIsNonFlatCurvature :
      Gate3.YMSFGCGate3M1U2M2WorkerReceipt.m1ExactBlocker
        gate3M1U2M2WorkerReceipt
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    gate3U2ExactTransportBlockerIsFieldStrengthAction :
      Gate3.YMSFGCGate3M1U2M2WorkerReceipt.u2ExactTransportBlocker
        gate3M1U2M2WorkerReceipt
      ≡
      Gate3Obs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    gate3M2ExactBlockerIsVariationPairing :
      Gate3.YMSFGCGate3M1U2M2WorkerReceipt.m2ExactBlocker
        gate3M1U2M2WorkerReceipt
      ≡
      Gate3Obs.missingVariationPairingForSelectedHodgeStar

    gate3M1U2M2WorkerPromotedIsFalse :
      Gate3.YMSFGCGate3M1U2M2WorkerReceipt.receiptPromoted
        gate3M1U2M2WorkerReceipt
      ≡
      false

    w4MatterStressEnergyFinalLedgerWave3Receipt :
      W4Stress.W4MatterStressEnergyInterfaceFinalLedgerWave3Receipt

    gate6Gate1Gate8LedgerWaveReceipt :
      Gate6Gate1Gate8LedgerWorkerWaveReceipt

    lower6GateReceiptWiringLedger :
      Lower6GateReceiptWiringLedger

    authorityLedger :
      SixPostulateAuthorityLedger

    candidate256ExternalStatus :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    firstUninhabitedUpstreamSymbols :
      List String

    firstUninhabitedUpstreamSymbolsAreCanonical :
      firstUninhabitedUpstreamSymbols
      ≡
      canonicalPaper7FirstUninhabitedUpstreamSymbols

    firstTerminalBlocker :
      String

    w4FirstAuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4FirstAuthorityBlockerIsCandidate256 :
      w4FirstAuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    everythingAgdaTimeout124Recorded :
      Bool

    everythingAgdaTimeout124RecordedIsFalse :
      everythingAgdaTimeout124Recorded ≡ false

    everythingAgdaExitZeroValidated :
      Bool

    everythingAgdaExitZeroValidatedIsTrue :
      everythingAgdaExitZeroValidated ≡ true

    uniformBalabanOrAgawaIRFixedPointStillExternal :
      Bool

    uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue :
      uniformBalabanOrAgawaIRFixedPointStillExternal ≡ true

    candidate256PhysicalCalibrationExternalReceiptImpossible :
      W4Calibration.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    w3w4w5ClayAuthorityFabricated :
      Bool

    w3w4w5ClayAuthorityFabricatedIsFalse :
      w3w4w5ClayAuthorityFabricated ≡ false

    finalLedgerBoundary :
      List String

open TerminalAuthorityFinalLedgerWorkerWave3Receipt public

canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt :
  TerminalAuthorityFinalLedgerWorkerWave3Receipt
canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt =
  record
    { status =
        terminalAuthorityFinalLedgerWorkerWave3RecordedNoPromotion
    ; paper7FinalProductReceipt =
        canonicalPaper7FinalProductReceipt
    ; gate4StressEnergyWave2Receipt =
        canonicalGate4StressEnergyTerminalLedgerWorkerWave2Receipt
    ; gate3M1U2M2WorkerReceipt =
        Gate3.canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; gate3M1ExactBlockerIsNonFlatCurvature =
        Gate3.YMSFGCGate3M1U2M2WorkerReceipt.m1ExactBlockerIsNonFlatCurvature
          Gate3.canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; gate3U2ExactTransportBlockerIsFieldStrengthAction =
        Gate3.YMSFGCGate3M1U2M2WorkerReceipt.u2ExactTransportBlockerIsFieldStrengthAction
          Gate3.canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; gate3M2ExactBlockerIsVariationPairing =
        Gate3.YMSFGCGate3M1U2M2WorkerReceipt.m2ExactBlockerIsVariationPairing
          Gate3.canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; gate3M1U2M2WorkerPromotedIsFalse =
        Gate3.YMSFGCGate3M1U2M2WorkerReceipt.receiptPromotedIsFalse
          Gate3.canonicalYMSFGCGate3M1U2M2WorkerReceipt
    ; w4MatterStressEnergyFinalLedgerWave3Receipt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceFinalLedgerWave3Receipt
    ; gate6Gate1Gate8LedgerWaveReceipt =
        canonicalGate6Gate1Gate8LedgerWorkerWaveReceipt
    ; lower6GateReceiptWiringLedger =
        canonicalLower6GateReceiptWiringLedger
    ; authorityLedger =
        canonicalSixPostulateAuthorityLedger
    ; candidate256ExternalStatus =
        W4Calibration.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; firstUninhabitedUpstreamSymbols =
        canonicalPaper7FirstUninhabitedUpstreamSymbols
    ; firstUninhabitedUpstreamSymbolsAreCanonical =
        refl
    ; firstTerminalBlocker =
        "Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
    ; w4FirstAuthorityBlocker =
        W4Stress.W4MatterStressEnergyInterfaceFinalLedgerWave3Receipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyInterfaceFinalLedgerWave3Receipt
    ; w4FirstAuthorityBlockerIsCandidate256 =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; everythingAgdaTimeout124Recorded =
        false
    ; everythingAgdaTimeout124RecordedIsFalse =
        refl
    ; everythingAgdaExitZeroValidated =
        true
    ; everythingAgdaExitZeroValidatedIsTrue =
        refl
    ; uniformBalabanOrAgawaIRFixedPointStillExternal =
        true
    ; uniformBalabanOrAgawaIRFixedPointStillExternalIsTrue =
        refl
    ; candidate256PhysicalCalibrationExternalReceiptImpossible =
        W4Calibration.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; w3w4w5ClayAuthorityFabricated =
        false
    ; w3w4w5ClayAuthorityFabricatedIsFalse =
        refl
    ; finalLedgerBoundary =
        "Continuation wave 3 refreshes the terminal blocker ledger after Gate3, Gate4, AQFT/GNS/DHR, CKM, W4, and Lower6 worker progress"
        ∷ "First terminal blocker remains Gate1/Gate6.missingExactStandardModelCarrierFunctorMatch"
        ∷ "Gate3 m1/u2/m2 worker receipt is consumed fail-closed: missingNonFlatSFGCSite2DConnectionCurvature, missingFieldStrengthTransportActionOnSelectedGaugeBundle, and missingVariationPairingForSelectedHodgeStar remain exact blockers"
        ∷ "AQFT first-missing-chain progress advances missingPreciseQuotientRelation; DHR still requires residualGlobalForeignLaneIdentityRequiresExplicitWitness, missingDASHILocalAlgebra, and Gate1 gauge-representation semantics"
        ∷ "Gate2/l6 conditional finite-carrier spectral-bound wiring remains non-transported to real YM and blocked at missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "Gate4 m3/u4 GR handoff remains blocked at missingMetricCompatibility, missingValuationMatterReceiptInterface, missingCandidate256CalibrationReceiptForMatterInterface, and missingStressEnergyCompatibilityForContractedBianchi"
        ∷ "W4 matter authority remains blocked at missingCandidate256CalibrationReceiptForMatterInterface and Candidate256PhysicalCalibrationExternalReceipt=impossibleWithoutExternalAuthority"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint and Clay external acceptance remain external/unconsumed"
        ∷ "DASHI/Everything.agda exit-0 validation is recorded; terminal promotion remains blocked by the mathematical and authority receipts"
        ∷ "No W3/W4/W5/Clay authority token, W4MatterStressEnergyInterfaceReceipt, sourced Einstein law, or terminal claim is fabricated"
        ∷ []
    }

terminalAuthorityFinalLedgerWorkerWave3TerminalClaimFalse :
  TerminalAuthorityFinalLedgerWorkerWave3Receipt.terminalClaimPromoted
    canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt
  ≡
  false
terminalAuthorityFinalLedgerWorkerWave3TerminalClaimFalse =
  refl

terminalAuthorityFinalLedgerWorkerWave3EverythingExitZeroTrue :
  TerminalAuthorityFinalLedgerWorkerWave3Receipt.everythingAgdaExitZeroValidated
    canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt
  ≡
  true
terminalAuthorityFinalLedgerWorkerWave3EverythingExitZeroTrue =
  refl

data Middle6Gate4Gate8YMGRUniquenessMonitorStatus : Set where
  middle6Gate4Gate8YMGRUniquenessMonitorFailClosed :
    Middle6Gate4Gate8YMGRUniquenessMonitorStatus

record Middle6Gate4Gate8YMGRUniquenessMonitor : Setω where
  field
    status :
      Middle6Gate4Gate8YMGRUniquenessMonitorStatus

    gate4LocalStressEnergyReceipt :
      Gate4.FactorVecLower6FullStressEnergyComponentReceipt

    w4UniquenessProgressReceipt :
      W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt

    gate4ContractedBianchiReceipt :
      Gate4GR.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    gate4ContractedBianchiPromotedFalse :
      Gate4GR.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
        gate4ContractedBianchiReceipt
      ≡
      false

    gate4SelectedLeviCivitaStillFalse :
      Gate4GR.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailable
        gate4ContractedBianchiReceipt
      ≡
      false

    terminalLedger :
      TerminalAuthorityFinalLedgerWorkerWave3Receipt

    localTYMEqualsTGRZeroTableAgreement :
      (mu nu : Gate4.FactorVecTangentDirection) →
      Gate4.FactorVecLower6FullStressEnergyComponentReceipt.tensorCandidate
        gate4LocalStressEnergyReceipt
        mu
        nu
      ≡
      Gate4.factorVecUnitP2LorentzEinsteinTensorComponentFamily mu nu

    localZeroTableAgreementOnly :
      Bool

    localZeroTableAgreementOnlyIsTrue :
      localZeroTableAgreementOnly
      ≡
      true

    lorentzGaugeInvarianceLawPresent :
      Bool

    lorentzGaugeInvarianceLawPresentIsFalse :
      lorentzGaugeInvarianceLawPresent
      ≡
      false

    noetherConservationLawPresent :
      Bool

    noetherConservationLawPresentIsFalse :
      noetherConservationLawPresent
      ≡
      false

    tracePairingLawPresent :
      Bool

    tracePairingLawPresentIsFalse :
      tracePairingLawPresent
      ≡
      false

    dimensionOneNormalizationLawPresent :
      Bool

    dimensionOneNormalizationLawPresentIsFalse :
      dimensionOneNormalizationLawPresent
      ≡
      false

    allFourRealUniquenessObligationsPresent :
      Bool

    allFourRealUniquenessObligationsPresentIsFalse :
      allFourRealUniquenessObligationsPresent
      ≡
      false

    everythingAgdaExitZeroValidated :
      Bool

    everythingAgdaExitZeroValidatedIsTrue :
      everythingAgdaExitZeroValidated
      ≡
      true

    l6MonitorPromoted :
      Bool

    l6MonitorPromotedIsFalse :
      l6MonitorPromoted
      ≡
      false

    authorityBackedTYMEqualsTGRPromoted :
      Bool

    authorityBackedTYMEqualsTGRPromotedIsFalse :
      authorityBackedTYMEqualsTGRPromoted
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted
      ≡
      false

    firstRemainingUniquenessLaw :
      W4Stress.W4YMGRStressEnergyUniquenessMissingLaw

    firstRemainingUniquenessLawIsLorentzGaugeInvariance :
      firstRemainingUniquenessLaw
      ≡
      W4Stress.missingLorentzGaugeInvarianceLawForUniqueness

    missingUniquenessLaws :
      List W4Stress.W4YMGRStressEnergyUniquenessMissingLaw

    missingUniquenessLawsAreCanonical :
      missingUniquenessLaws
      ≡
      W4Stress.canonicalW4YMGRStressEnergyUniquenessMissingLaws

    monitorBoundary :
      List String

open Middle6Gate4Gate8YMGRUniquenessMonitor public

canonicalMiddle6Gate4Gate8YMGRUniquenessMonitor :
  Middle6Gate4Gate8YMGRUniquenessMonitor
canonicalMiddle6Gate4Gate8YMGRUniquenessMonitor =
  record
    { status =
        middle6Gate4Gate8YMGRUniquenessMonitorFailClosed
    ; gate4LocalStressEnergyReceipt =
        Gate4.canonicalFactorVecLower6FullStressEnergyComponentReceipt
    ; w4UniquenessProgressReceipt =
        W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt
    ; gate4ContractedBianchiReceipt =
        Gate4GR.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; gate4ContractedBianchiPromotedFalse =
        Gate4GR.grGate4ContractedBianchiStillNotPromoted
    ; gate4SelectedLeviCivitaStillFalse =
        Gate4GR.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailableIsFalse
          Gate4GR.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; terminalLedger =
        canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt
    ; localTYMEqualsTGRZeroTableAgreement =
        Gate4.factorVecLower6LocalYMGRStressEnergyZeroTableAgreement
    ; localZeroTableAgreementOnly =
        true
    ; localZeroTableAgreementOnlyIsTrue =
        refl
    ; lorentzGaugeInvarianceLawPresent =
        false
    ; lorentzGaugeInvarianceLawPresentIsFalse =
        refl
    ; noetherConservationLawPresent =
        false
    ; noetherConservationLawPresentIsFalse =
        refl
    ; tracePairingLawPresent =
        false
    ; tracePairingLawPresentIsFalse =
        refl
    ; dimensionOneNormalizationLawPresent =
        false
    ; dimensionOneNormalizationLawPresentIsFalse =
        refl
    ; allFourRealUniquenessObligationsPresent =
        W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt.realUniquenessObligationsAllPresent
          W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt
    ; allFourRealUniquenessObligationsPresentIsFalse =
        W4Stress.w4YMGRStressEnergyUniquenessRealObligationsStillMissing
    ; everythingAgdaExitZeroValidated =
        TerminalAuthorityFinalLedgerWorkerWave3Receipt.everythingAgdaExitZeroValidated
          canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt
    ; everythingAgdaExitZeroValidatedIsTrue =
        terminalAuthorityFinalLedgerWorkerWave3EverythingExitZeroTrue
    ; l6MonitorPromoted =
        false
    ; l6MonitorPromotedIsFalse =
        refl
    ; authorityBackedTYMEqualsTGRPromoted =
        W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt.authorityBackedTYMEqualsTGRPromoted
          W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt
    ; authorityBackedTYMEqualsTGRPromotedIsFalse =
        W4Stress.w4YMGRStressEnergyUniquenessNotPromoted
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; firstRemainingUniquenessLaw =
        W4Stress.missingLorentzGaugeInvarianceLawForUniqueness
    ; firstRemainingUniquenessLawIsLorentzGaugeInvariance =
        refl
    ; missingUniquenessLaws =
        W4Stress.canonicalW4YMGRStressEnergyUniquenessMissingLaws
    ; missingUniquenessLawsAreCanonical =
        refl
    ; monitorBoundary =
        "middle6 m6 consumes the Gate4 local zero-table T_YM/T_GR equality as bounded progress only"
        ∷ "Gate4 contracted-Bianchi is consumed through the u3-threaded fail-closed receipt: doubled torsion-free is closed, selected Levi-Civita and contracted-Bianchi promotion remain false"
        ∷ "The l6/Gate8 monitor is fail-closed: Everything exit-0 is recorded, but all four real uniqueness obligations are not present"
        ∷ "The missing real laws are Lorentz/gauge invariance, Noether conservation, trace pairing, and dimension-one normalization on the authority-backed tensor"
        ∷ "W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt keeps authorityBackedTYMEqualsTGRPromoted=false"
        ∷ "terminalClaimPromoted remains false; no W4MatterStressEnergyInterfaceReceipt, sourced Einstein law, or terminal authority is fabricated"
        ∷ []
    }

middle6Gate4Gate8YMGRUniquenessMonitorNotPromoted :
  Middle6Gate4Gate8YMGRUniquenessMonitor.l6MonitorPromoted
    canonicalMiddle6Gate4Gate8YMGRUniquenessMonitor
  ≡
  false
middle6Gate4Gate8YMGRUniquenessMonitorNotPromoted =
  refl

middle6Gate4Gate8YMGRUniquenessTerminalClaimFalse :
  Middle6Gate4Gate8YMGRUniquenessMonitor.terminalClaimPromoted
    canonicalMiddle6Gate4Gate8YMGRUniquenessMonitor
  ≡
  false
middle6Gate4Gate8YMGRUniquenessTerminalClaimFalse =
  refl

paper7FinalProductTerminalClaimIsNotPromoted :
  Paper7FinalProductReceipt.terminalClaimPromoted
    canonicalPaper7FinalProductReceipt
  ≡
  false
paper7FinalProductTerminalClaimIsNotPromoted =
  refl

terminalClaimIsNotPromoted :
  GRQFTCompositionBoundary.terminalClaimPromoted
    canonicalGRQFTCompositionBoundary
  ≡
  false
terminalClaimIsNotPromoted =
  refl

terminalProObjectMassGapIsProved :
  WeakTerminalClaimOpenStatusGrammar.proObjectMassGapProved
    canonicalWeakTerminalClaimOpenStatusGrammar
  ≡
  true
terminalProObjectMassGapIsProved =
  refl

terminalWeakClaimIsPromotedModuloMinimalPostulates :
  WeakTerminalClaimOpenStatusGrammar.weakTerminalClaimPromoted
    canonicalWeakTerminalClaimOpenStatusGrammar
  ≡
  true
terminalWeakClaimIsPromotedModuloMinimalPostulates =
  refl

terminalWeakGrammarTerminalClaimIsNotPromoted :
  WeakTerminalClaimOpenStatusGrammar.terminalClaimPromoted
    canonicalWeakTerminalClaimOpenStatusGrammar
  ≡
  false
terminalWeakGrammarTerminalClaimIsNotPromoted =
  refl

terminalContinuumClayMassGapIsNotPromoted :
  WeakTerminalClaimOpenStatusGrammar.continuumClayMassGapPromoted
    canonicalWeakTerminalClaimOpenStatusGrammar
  ≡
  false
terminalContinuumClayMassGapIsNotPromoted =
  refl

terminalContinuumMassGapNotProvedInDASHI :
  WeakTerminalClaimOpenStatusGrammar.continuumMassGapProvedInDASHI
    canonicalWeakTerminalClaimOpenStatusGrammar
  ≡
  false
terminalContinuumMassGapNotProvedInDASHI =
  refl

terminalPublicationPapers1To3Executable :
  OpenProblems.TerminalPublicationTierMap.papers1To3ExecutableFromCurrentRepoState
    (GRQFTCompositionBoundary.publicationTierMap
      canonicalGRQFTCompositionBoundary)
  ≡
  true
terminalPublicationPapers1To3Executable =
  refl

terminalPublicationPapers4To7RemainOpen :
  OpenProblems.TerminalPublicationTierMap.papers4To7RemainOpen
    (GRQFTCompositionBoundary.publicationTierMap
      canonicalGRQFTCompositionBoundary)
  ≡
  true
terminalPublicationPapers4To7RemainOpen =
  refl

terminalAdapter4InventoryIsFinal :
  GRQFTCompositionBoundary.terminalAdapter4Inventory
    canonicalGRQFTCompositionBoundary
  ≡
  canonicalTerminalAdapter4IrreducibleInputs
terminalAdapter4InventoryIsFinal =
  refl

record DHRCarrierTerminalFinalFailClosedReceipt : Setω where
  field
    gate1FinalLocalExactMatchReceipt :
      Gate1.Gate1Gate6FinalLocalExactMatchReceipt

    gate6FinalLocalReceipt :
      Gate6.Gate6DHRWorkerWave3FinalLocalReceipt

    terminalLedger :
      TerminalAuthorityFinalLedgerWorkerWave3Receipt

    exactStandardModelCarrierFunctorMatchBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchBlockerIsCanonical :
      exactStandardModelCarrierFunctorMatchBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    gate6FirstRemainingBlocker :
      Gate6.DHRTensorDualGroupBlocker

    gate6FirstRemainingBlockerIsGate1GaugeRepresentationSemantics :
      gate6FirstRemainingBlocker
      ≡
      Gate6.blockedByMissingGate1GaugeRepresentationSemantics

    aqftCurrentFirstResidual :
      AQFTQuotient.AQFTCarrierAlgebraQuotientOpenObligation

    aqftCurrentFirstResidualIsMissingPreciseQuotientRelation :
      aqftCurrentFirstResidual
      ≡
      AQFTQuotient.missingPreciseQuotientRelation

    dhrUnsuppliedForeignIdentityResidual :
      Hexagon.DHRArbitrarySectorForeignIdentityFieldLatticeResidual

    dhrUnsuppliedForeignIdentityResidualIsExplicitWitness :
      dhrUnsuppliedForeignIdentityResidual
      ≡
      Hexagon.residualGlobalForeignLaneIdentityRequiresExplicitWitness

    dhrClassificationDownstreamBlockers :
      List Hexagon.DHRArbitrarySectorClassificationDownstreamBlocker

    dhrClassificationDownstreamBlockersAreExact :
      dhrClassificationDownstreamBlockers
      ≡
      (Hexagon.missingDASHILocalAlgebra
       ∷ Hexagon.blockedByMissingGate1GaugeRepresentationSemantics
       ∷ [])

    yukawaDHRCompatibilitySurface :
      Gate7CKM.CKMYukawaDHRRhoPYijCompatibilityObligationSurface

    yukawaDHRCompatibilityBlocker :
      Gate7CKM.CKMYukawaDHRCompatibilityBlocker

    yukawaDHRCompatibilityBlockerIsMissingIntertwiner :
      yukawaDHRCompatibilityBlocker
      ≡
      Gate7CKM.missingYukawaDHRIntertwinerCompatibility

    stoneSpectralGapReceipt :
      Gate5.BoundedStoneGeneratorSpectralGapInterpretationReceipt

    stoneFirstRemainingTarget :
      Gate5.StoneGeneratorSpectralGapRemainingTarget

    stoneFirstRemainingTargetIsGlobalNoncollapsedPhaseSpace :
      stoneFirstRemainingTarget
      ≡
      Gate5.targetGlobalNoncollapsedPhysicalPhaseSpace

    continuumMassGapProvedInDASHI :
      Bool

    continuumMassGapProvedInDASHIIsFalse :
      continuumMassGapProvedInDASHI ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    ymgrStressEnergyReceipt :
      Gate4.FactorVecGate4StressEnergyConservationSourceReceipt

    ymgrOriginalFirstMissing :
      Gate4.FactorVecStressEnergyCompatibilityMissingPrimitive

    ymgrOriginalFirstMissingIsTensorCandidate :
      ymgrOriginalFirstMissing
      ≡
      Gate4.missingValuationStressEnergyTensorCandidate

    ymgrLocalRemainingBlocker :
      Gate4.FactorVecStressEnergyCompatibilityMissingPrimitive

    ymgrLocalRemainingBlockerIsMatterReceiptInterface :
      ymgrLocalRemainingBlocker
      ≡
      Gate4.missingValuationMatterReceiptInterface

    w4StressEnergyAuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4StressEnergyAuthorityBlockerIsCandidate256 :
      w4StressEnergyAuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    ymgrStressEnergyAgreementPromoted :
      Bool

    ymgrStressEnergyAgreementPromotedIsFalse :
      ymgrStressEnergyAgreementPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    exactTerminalBlockerChain :
      List String

    exactTerminalBlockerChainIsCanonical :
      exactTerminalBlockerChain
      ≡
      canonicalPaper7FirstUninhabitedUpstreamSymbols

    finalFailClosedBoundary :
      List String

open DHRCarrierTerminalFinalFailClosedReceipt public

canonicalDHRCarrierTerminalFinalFailClosedReceipt :
  DHRCarrierTerminalFinalFailClosedReceipt
canonicalDHRCarrierTerminalFinalFailClosedReceipt =
  record
    { gate1FinalLocalExactMatchReceipt =
        Gate1.canonicalGate1Gate6FinalLocalExactMatchReceipt
    ; gate6FinalLocalReceipt =
        Gate6.canonicalGate6DHRWorkerWave3FinalLocalReceipt
    ; terminalLedger =
        canonicalTerminalAuthorityFinalLedgerWorkerWave3Receipt
    ; exactStandardModelCarrierFunctorMatchBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchBlockerIsCanonical =
        refl
    ; gate6FirstRemainingBlocker =
        Gate6.blockedByMissingGate1GaugeRepresentationSemantics
    ; gate6FirstRemainingBlockerIsGate1GaugeRepresentationSemantics =
        refl
    ; aqftCurrentFirstResidual =
        AQFTQuotient.missingPreciseQuotientRelation
    ; aqftCurrentFirstResidualIsMissingPreciseQuotientRelation =
        refl
    ; dhrUnsuppliedForeignIdentityResidual =
        Hexagon.residualGlobalForeignLaneIdentityRequiresExplicitWitness
    ; dhrUnsuppliedForeignIdentityResidualIsExplicitWitness =
        refl
    ; dhrClassificationDownstreamBlockers =
        Hexagon.missingDASHILocalAlgebra
        ∷ Hexagon.blockedByMissingGate1GaugeRepresentationSemantics
        ∷ []
    ; dhrClassificationDownstreamBlockersAreExact =
        refl
    ; yukawaDHRCompatibilitySurface =
        Gate7CKM.canonicalCKMYukawaDHRRhoPYijCompatibilityObligationSurface
    ; yukawaDHRCompatibilityBlocker =
        Gate7CKM.missingYukawaDHRIntertwinerCompatibility
    ; yukawaDHRCompatibilityBlockerIsMissingIntertwiner =
        refl
    ; stoneSpectralGapReceipt =
        Gate5.onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt
    ; stoneFirstRemainingTarget =
        Gate5.targetGlobalNoncollapsedPhysicalPhaseSpace
    ; stoneFirstRemainingTargetIsGlobalNoncollapsedPhaseSpace =
        refl
    ; continuumMassGapProvedInDASHI =
        false
    ; continuumMassGapProvedInDASHIIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; ymgrStressEnergyReceipt =
        Gate4.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; ymgrOriginalFirstMissing =
        Gate4.missingValuationStressEnergyTensorCandidate
    ; ymgrOriginalFirstMissingIsTensorCandidate =
        refl
    ; ymgrLocalRemainingBlocker =
        Gate4.missingValuationMatterReceiptInterface
    ; ymgrLocalRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4StressEnergyAuthorityBlocker =
        W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
    ; w4StressEnergyAuthorityBlockerIsCandidate256 =
        refl
    ; ymgrStressEnergyAgreementPromoted =
        false
    ; ymgrStressEnergyAgreementPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; exactTerminalBlockerChain =
        canonicalPaper7FirstUninhabitedUpstreamSymbols
    ; exactTerminalBlockerChainIsCanonical =
        refl
    ; finalFailClosedBoundary =
        "DHR carrier-terminal final receipt is fail-closed and consumes only existing canonical blocker surfaces"
        ∷ "Supplied DHR foreign-lane identity is available only through explicit supply; unsupplied sectors still block at residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "AQFT first-missing-chain progress advances missingPreciseQuotientRelation; the remaining AQFT/Gate1/Gate6 blockers are missingDASHILocalAlgebra, blockedByMissingGate1GaugeRepresentationSemantics, and missingExactStandardModelCarrierFunctorMatch"
        ∷ "DHR/Yukawa sector agreement remains blocked at missingYukawaDHRIntertwinerCompatibility"
        ∷ "Stone spectrum versus mass-gap accounting remains split: DASHI continuum mass-gap status is recorded, but the Stone physical route first needs targetGlobalNoncollapsedPhysicalPhaseSpace and Clay promotion stays false"
        ∷ "YM/GR stress-energy agreement has only local zero-table tensor staging; terminal residuals remain missingValuationMatterReceiptInterface, missingCandidate256CalibrationReceiptForMatterInterface, and non-flat/source compatibility"
        ∷ "terminalClaimPromoted remains false; no DR theorem authority, Gate1 semantics, Standard Model match, W4/W5 authority, Clay acceptance, or terminal theorem is fabricated"
        ∷ []
    }

dhrCarrierTerminalFinalReceiptKeepsTerminalClaimFalse :
  DHRCarrierTerminalFinalFailClosedReceipt.terminalClaimPromoted
    canonicalDHRCarrierTerminalFinalFailClosedReceipt
  ≡
  false
dhrCarrierTerminalFinalReceiptKeepsTerminalClaimFalse =
  refl

data Gate7LowerReceiptTerminalStagingStatus : Set where
  gate7LowerReceiptTerminalStagingRecordedNoPromotion :
    Gate7LowerReceiptTerminalStagingStatus

record Gate7LowerReceiptTerminalStagingLedger : Setω where
  field
    status :
      Gate7LowerReceiptTerminalStagingStatus

    gate7CarrierFrontierReceipt :
      Gate7CKM.CKMGate7L1CarrierFrontierReceipt

    gate7EntryFieldFrontier :
      Gate7Field.CKMGate7L1ExactArithmeticFrontierReceipt

    gate7M5M6L1ClosureReceipt :
      Gate7CKM.CKMGate7M5M6L1ClosureReceipt

    entryFieldCertificatesSupplied :
      Gate7Field.entryFieldMembershipCertificatesSupplied
        (Gate7Field.entryMembershipReceipt gate7EntryFieldFrontier)
      ≡
      true

    hermitianProductMatricesSupplied :
      Gate7Field.hermitianProductMatricesSupplied
        (Gate7Field.hermitianProductReceipt
          (Gate7Field.symbolicSpectralArithmeticReceipt
            gate7EntryFieldFrontier))
      ≡
      true

    characteristicQueueBlocksAtProductClosure :
      Gate7Field.firstRemainingArithmeticBlocker
        (Gate7Field.symbolicSpectralArithmeticReceipt
          gate7EntryFieldFrontier)
      ≡
      Gate7Field.missingCKMProductClosureWitness

    ckmProductUsesMatterMixingMatrix :
      Gate7Field.frontierVCkmCarrier gate7EntryFieldFrontier
      ≡
      Gate7Matter.MixingMatrix

    ckmProductClosureWitnessStillMissing :
      Gate7Field.ckmProductClosureWitnessSupplied
        (Gate7Field.matterMixingMatrixProductAttemptReceipt
          gate7EntryFieldFrontier)
      ≡
      false

    unitarityResidualWitnessStillMissing :
      Gate7Field.actualUnitarityResidualWitnessSupplied
        (Gate7Field.finalLocalUnitarityResidualReceipt
          gate7EntryFieldFrontier)
      ≡
      false

    m5m6l1UsesMatterMixingMatrix :
      Gate7Field.attemptVCkmCarrier
        Gate7Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt
      ≡
      Gate7Matter.MixingMatrix

    m5m6l1ProductClosureWitnessStillMissing :
      Gate7Field.ckmProductClosureWitnessSupplied
        (Gate7Field.matterMixingMatrixProductAttemptReceipt
          Gate7Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      false

    m5m6l1UnitarityResidualWitnessStillMissing :
      Gate7Field.actualUnitarityResidualWitnessSupplied
        (Gate7Field.finalLocalUnitarityResidualReceipt
          Gate7Field.canonicalCKMGate7L1ExactArithmeticAttemptReceipt)
      ≡
      false

    m5m6l1WolfensteinValuesRemainTargetOnly :
      Gate7CKM.CKMWolfensteinJarlskogTargetSurface.wolfensteinNumericValuesSupplied
        Gate7CKM.canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    m5m6l1JarlskogValueRemainsTargetOnly :
      Gate7CKM.CKMWolfensteinJarlskogTargetSurface.jarlskogInvariantValueSupplied
        Gate7CKM.canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    m5m6l1JarlskogNonzeroProofStillMissing :
      Gate7CKM.CKMWolfensteinJarlskogTargetSurface.jarlskogNonzeroProofSupplied
        Gate7CKM.canonicalCKMWolfensteinJarlskogTargetSurface
      ≡
      false

    m5m6l1CarrierMixingPromotedIsFalse :
      Gate7CKM.CKMGate7M5M6L1ClosureReceipt.m5m6l1CarrierMixingPromoted
        gate7M5M6L1ClosureReceipt
      ≡
      false

    dhrYukawaIntertwinerCompatibilityStillMissing :
      Gate7CKM.compatibilityFrontierBlocker gate7CarrierFrontierReceipt
      ≡
      Gate7CKM.missingYukawaDHRIntertwinerCompatibility

    carrierMixingTheoremStillMissing :
      Gate7CKM.finalLocalCarrierNextBlocker
        (Gate7CKM.finalLocalCarrierReceipt gate7CarrierFrontierReceipt)
      ≡
      Gate7CKM.missingCarrierMixingTheorem

    vHiggsAdapter4BoundaryStillRequired :
      Gate7Higgs.vHiggsAdapter4Boundary
        (Gate7CKM.higgsDependencyReceipt gate7CarrierFrontierReceipt)
      ≡
      true

    exactStandardModelCarrierFunctorMatchStillMissing :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    exactStandardModelCarrierFunctorMatchStillMissingIsCanonical :
      exactStandardModelCarrierFunctorMatchStillMissing
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    everythingAgdaTimeoutRecorded :
      Bool

    everythingAgdaTimeoutRecordedIsFalse :
      everythingAgdaTimeoutRecorded ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    lowerGateTerminalBoundary :
      List String

open Gate7LowerReceiptTerminalStagingLedger public

canonicalGate7LowerReceiptTerminalStagingLedger :
  Gate7LowerReceiptTerminalStagingLedger
canonicalGate7LowerReceiptTerminalStagingLedger =
  record
    { status =
        gate7LowerReceiptTerminalStagingRecordedNoPromotion
    ; gate7CarrierFrontierReceipt =
        Gate7CKM.canonicalCKMGate7L1CarrierFrontierReceipt
    ; gate7EntryFieldFrontier =
        Gate7Field.canonicalCKMGate7L1ExactArithmeticFrontierReceipt
    ; gate7M5M6L1ClosureReceipt =
        Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; entryFieldCertificatesSupplied =
        refl
    ; hermitianProductMatricesSupplied =
        refl
    ; characteristicQueueBlocksAtProductClosure =
        refl
    ; ckmProductUsesMatterMixingMatrix =
        refl
    ; ckmProductClosureWitnessStillMissing =
        refl
    ; unitarityResidualWitnessStillMissing =
        refl
    ; m5m6l1UsesMatterMixingMatrix =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.entryFieldAttemptStagesProductThroughMatterMixingMatrix
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1ProductClosureWitnessStillMissing =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.entryFieldAttemptProductClosureMissing
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1UnitarityResidualWitnessStillMissing =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.entryFieldAttemptUnitarityResidualMissing
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1WolfensteinValuesRemainTargetOnly =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.wolfensteinValuesRemainTargetOnly
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1JarlskogValueRemainsTargetOnly =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.jarlskogValueRemainsTargetOnly
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1JarlskogNonzeroProofStillMissing =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.jarlskogNonzeroProofStillMissing
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; m5m6l1CarrierMixingPromotedIsFalse =
        Gate7CKM.CKMGate7M5M6L1ClosureReceipt.m5m6l1CarrierMixingPromotedIsFalse
          Gate7CKM.canonicalCKMGate7M5M6L1ClosureReceipt
    ; dhrYukawaIntertwinerCompatibilityStillMissing =
        refl
    ; carrierMixingTheoremStillMissing =
        refl
    ; vHiggsAdapter4BoundaryStillRequired =
        refl
    ; exactStandardModelCarrierFunctorMatchStillMissing =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; exactStandardModelCarrierFunctorMatchStillMissingIsCanonical =
        refl
    ; everythingAgdaTimeoutRecorded =
        false
    ; everythingAgdaTimeoutRecordedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; lowerGateTerminalBoundary =
        "Gate 7 lower receipt staging consumes exact entry-field certificates and Hermitian/characteristic/eigenbasis surfaces"
        ∷ "m5/m6/l1 closure receipt is consumed fail-closed and the CKM product ledger uses opaque Matter.MixingMatrix for U_u, U_d, and V_CKM"
        ∷ "missingCKMProductClosureWitness and missingUnitarityResidualWitness remain open"
        ∷ "Wolfenstein and Jarlskog remain target surfaces only, with no numeric values or nonzero proof"
        ∷ "missingYukawaDHRIntertwinerCompatibility and missingCarrierMixingTheorem remain open"
        ∷ "vHiggsAdapter4Boundary and missingExactStandardModelCarrierFunctorMatch remain terminal blockers; Everything.agda validation is tracked separately and is not a mathematical receipt"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

gate7LowerReceiptTerminalStagingKeepsTerminalClaimFalse :
  Gate7LowerReceiptTerminalStagingLedger.terminalClaimPromoted
    canonicalGate7LowerReceiptTerminalStagingLedger
  ≡
  false
gate7LowerReceiptTerminalStagingKeepsTerminalClaimFalse =
  refl

data TerminalLedgerWorkerWave4Status : Set where
  terminalLedgerWorkerWave4ReceiptsConsumedFailClosed :
    TerminalLedgerWorkerWave4Status

record TerminalLedgerWorkerWave4Receipt : Setω₁ where
  field
    status :
      TerminalLedgerWorkerWave4Status

    aqftFirstMissingChainReceipt :
      AQFTQuotient.AQFTFirstMissingChainReceipt

    aqftPreciseQuotientRelationAdvanced :
      AQFTQuotient.AQFTWave3PreciseQuotientLocalAlgebraProgress.preciseQuotientRelationAdvanced
        (AQFTQuotient.AQFTFirstMissingChainReceipt.preciseQuotientProgress
          aqftFirstMissingChainReceipt)
      ≡
      true

    aqftNextResidualIsDASHILocalAlgebra :
      AQFTQuotient.AQFTFirstMissingChainReceipt.missingDASHILocalAlgebraBlocker
        aqftFirstMissingChainReceipt
      ≡
      AQFTQuotient.missingDASHILocalAlgebra

    dhrSelectedPrimeIdentityFailClosedReceipt :
      Bool

    dhrSelectedSuppliedInterfacesPackaged :
      Bool

    dhrFirstResidualStillRequiresExplicitWitness :
      Bool

    gate3FirstMissingPrimitiveWorkerReceipt :
      Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt

    gate3FirstMissingPrimitiveWorkerPromotedIsFalse :
      Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.receiptPromoted
        gate3FirstMissingPrimitiveWorkerReceipt
      ≡
      false

    gate3FirstMissingPrimitiveNonFlatBlocker :
      Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactNonFlatCurvatureBlocker
        gate3FirstMissingPrimitiveWorkerReceipt
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    gate3FirstMissingPrimitiveLieBlocker :
      Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactSelectedGaugeSectorBlocker
        gate3FirstMissingPrimitiveWorkerReceipt
      ≡
      Gate3Obs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    gate3FirstMissingPrimitiveVariationBlocker :
      Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactVariationPairingBlocker
        gate3FirstMissingPrimitiveWorkerReceipt
      ≡
      Gate3Obs.missingVariationPairingForSelectedHodgeStar

    gate4MatterReceiptInterfaceFailClosedReceipt :
      Gate4.FactorVecValuationMatterReceiptInterfaceFailClosedReceipt

    gate4MatterReceiptInterfaceRemainingBlocker :
      Gate4.FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.matterReceiptInterfaceRemainingBlocker
        gate4MatterReceiptInterfaceFailClosedReceipt
      ≡
      Gate4.missingValuationMatterReceiptInterface

    gate4MatterStressEnergyFinalReceipt :
      Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt

    gate4MatterStressEnergyFinalW4Blocker :
      Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.w4AuthorityFirstBlocker
        gate4MatterStressEnergyFinalReceipt
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    gate4FlatVsNonflatCompatibilityReceipt :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt

    gate4FlatCompatibilityProved :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.flatCompatibilityProved
        gate4FlatVsNonflatCompatibilityReceipt
      ≡
      true

    gate4NonFlatCompatibilityPromotedIsFalse :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.nonFlatCompatibilityPromoted
        gate4FlatVsNonflatCompatibilityReceipt
      ≡
      false

    gate4SelectedNonFlatMetricBlocker :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlocker
        gate4FlatVsNonflatCompatibilityReceipt
      ≡
      Gate4GR.missingMetricCompatibility

    ckmExplicitFNChargeTable :
      Gate7Field.CKMExplicitFNChargeTable

    ckmExplicitFNChargeTableKeepsUpHiggsAdapter4Open :
      Gate7Field.CKMExplicitFNChargeTable.fnChargeUpHiggsAdapter4SocketPromoted
        ckmExplicitFNChargeTable
      ≡
      false

    ckmDownYukawaCompletionReceipt :
      Gate7CKM.CKMGate7DownYukawaCompletionReceipt

    ckmProductClosureWitnessStillMissing :
      Gate7CKM.CKMGate7DownYukawaCompletionReceipt.ckmProductClosureWitnessSupplied
        ckmDownYukawaCompletionReceipt
      ≡
      false

    lower6NaturalUnitAndRealCarrierFailClosedReceipt :
      Gate2.S8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt

    lower6NaturalUnitsPromoted :
      Gate2.S8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt.naturalUnitsPromoted
        lower6NaturalUnitAndRealCarrierFailClosedReceipt
      ≡
      true

    lower6RealCarrierTheoremConstructedIsFalse :
      Gate2.S8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt.realCarrierTheoremConstructed
        lower6NaturalUnitAndRealCarrierFailClosedReceipt
      ≡
      false

    lower6ContinuumClayExactFailClosedReceipt :
      Clay.L6ContinuumClayExactFailClosedReceipt

    lower6ClayTerminalClaimPromotedIsFalse :
      Clay.L6ContinuumClayExactFailClosedReceipt.terminalClaimPromoted
        lower6ContinuumClayExactFailClosedReceipt
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    exactFirstUninhabitedUpstreamSymbols :
      List String

    exactFirstUninhabitedUpstreamSymbolsAreCanonical :
      exactFirstUninhabitedUpstreamSymbols
      ≡
      canonicalPaper7FirstUninhabitedUpstreamSymbols

    terminalWaveBoundary :
      List String

open TerminalLedgerWorkerWave4Receipt public

canonicalTerminalLedgerWorkerWave4Receipt :
  TerminalLedgerWorkerWave4Receipt
canonicalTerminalLedgerWorkerWave4Receipt =
  record
    { status =
        terminalLedgerWorkerWave4ReceiptsConsumedFailClosed
    ; aqftFirstMissingChainReceipt =
        AQFTQuotient.canonicalAQFTFirstMissingChainReceipt
    ; aqftPreciseQuotientRelationAdvanced =
        AQFTQuotient.AQFTFirstMissingChainReceipt.missingPreciseQuotientRelationAdvanced
          AQFTQuotient.canonicalAQFTFirstMissingChainReceipt
    ; aqftNextResidualIsDASHILocalAlgebra =
        AQFTQuotient.AQFTFirstMissingChainReceipt.missingDASHILocalAlgebraBlocker-v
          AQFTQuotient.canonicalAQFTFirstMissingChainReceipt
    ; dhrSelectedPrimeIdentityFailClosedReceipt =
        true
    ; dhrSelectedSuppliedInterfacesPackaged =
        true
    ; dhrFirstResidualStillRequiresExplicitWitness =
        true
    ; gate3FirstMissingPrimitiveWorkerReceipt =
        Gate3.canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; gate3FirstMissingPrimitiveWorkerPromotedIsFalse =
        Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.receiptPromotedIsFalse
          Gate3.canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; gate3FirstMissingPrimitiveNonFlatBlocker =
        Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactNonFlatCurvatureBlockerIsMissingNonFlatSFGCSite2DConnectionCurvature
          Gate3.canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; gate3FirstMissingPrimitiveLieBlocker =
        Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactSelectedGaugeSectorBlockerIsMissingLieAlgebraCarrier
          Gate3.canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; gate3FirstMissingPrimitiveVariationBlocker =
        Gate3.YMSFGCGate3FirstMissingPrimitiveWorkerReceipt.exactVariationPairingBlockerIsMissingVariationPairing
          Gate3.canonicalYMSFGCGate3FirstMissingPrimitiveWorkerReceipt
    ; gate4MatterReceiptInterfaceFailClosedReceipt =
        Gate4.canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; gate4MatterReceiptInterfaceRemainingBlocker =
        Gate4.FactorVecValuationMatterReceiptInterfaceFailClosedReceipt.matterReceiptInterfaceRemainingBlockerIsExact
          Gate4.canonicalFactorVecValuationMatterReceiptInterfaceFailClosedReceipt
    ; gate4MatterStressEnergyFinalReceipt =
        Gate4.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; gate4MatterStressEnergyFinalW4Blocker =
        Gate4.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.w4AuthorityFirstBlockerIsCandidate256
          Gate4.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; gate4FlatVsNonflatCompatibilityReceipt =
        Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; gate4FlatCompatibilityProved =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.flatCompatibilityProvedIsTrue
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; gate4NonFlatCompatibilityPromotedIsFalse =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.nonFlatCompatibilityPromotedIsFalse
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; gate4SelectedNonFlatMetricBlocker =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; ckmExplicitFNChargeTable =
        Gate7Field.canonicalCKMExplicitFNChargeTable
    ; ckmExplicitFNChargeTableKeepsUpHiggsAdapter4Open =
        Gate7Field.CKMExplicitFNChargeTable.fnChargeUpHiggsAdapter4SocketPromotedIsFalse
          Gate7Field.canonicalCKMExplicitFNChargeTable
    ; ckmDownYukawaCompletionReceipt =
        Gate7CKM.canonicalCKMGate7DownYukawaCompletionReceipt
    ; ckmProductClosureWitnessStillMissing =
        Gate7CKM.CKMGate7DownYukawaCompletionReceipt.ckmProductClosureWitnessSuppliedIsFalse
          Gate7CKM.canonicalCKMGate7DownYukawaCompletionReceipt
    ; lower6NaturalUnitAndRealCarrierFailClosedReceipt =
        Gate2.canonicalS8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt
    ; lower6NaturalUnitsPromoted =
        Gate2.S8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt.naturalUnitsPromotedIsTrue
          Gate2.canonicalS8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt
    ; lower6RealCarrierTheoremConstructedIsFalse =
        Gate2.S8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt.realCarrierTheoremConstructedIsFalse
          Gate2.canonicalS8L6DispersionNaturalUnitAndRealCarrierFailClosedReceipt
    ; lower6ContinuumClayExactFailClosedReceipt =
        Clay.canonicalL6ContinuumClayExactFailClosedReceipt
    ; lower6ClayTerminalClaimPromotedIsFalse =
        Clay.L6ContinuumClayExactFailClosedReceipt.terminalClaimPromotedIsFalse
          Clay.canonicalL6ContinuumClayExactFailClosedReceipt
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; exactFirstUninhabitedUpstreamSymbols =
        canonicalPaper7FirstUninhabitedUpstreamSymbols
    ; exactFirstUninhabitedUpstreamSymbolsAreCanonical =
        refl
    ; terminalWaveBoundary =
        "Wave 4 consumes AQFTFirstMissingChainReceipt: missingPreciseQuotientRelation is advanced, but missingDASHILocalAlgebra remains the next AQFT residual"
        ∷ "DHR selected-prime identity is fail-closed: selected supplied interfaces can be packaged, while arbitrary sectors still require residualGlobalForeignLaneIdentityRequiresExplicitWitness"
        ∷ "Gate3 first-missing primitive worker receipt stays non-promoting at missingNonFlatSFGCSite2DConnectionCurvature, missingLieAlgebraCarrierForSelectedFiniteGaugeSector, and missingVariationPairingForSelectedHodgeStar"
        ∷ "Gate4 matter and flat-vs-nonflat receipts stage the local zero-table tensor and flat compatibility, but non-flat GR remains blocked at missingMetricCompatibility, missingValuationMatterReceiptInterface, W4 Candidate256, and contracted-Bianchi stress-energy compatibility"
        ∷ "CKM explicit FN charge table is consumed at exponent level; up-Higgs Adapter4, DHR/Yukawa intertwiner compatibility, product closure, unitarity residual, and carrier-mixing theorem remain open"
        ∷ "Lower6 natural units are true locally, but the real-carrier theorem and Clay/terminal promotion remain false"
        ∷ "terminalClaimPromoted remains false and exactFirstUninhabitedUpstreamSymbols is the canonical residual list"
        ∷ []
    }

terminalLedgerWorkerWave4KeepsTerminalClaimFalse :
  TerminalLedgerWorkerWave4Receipt.terminalClaimPromoted
    canonicalTerminalLedgerWorkerWave4Receipt
  ≡
  false
terminalLedgerWorkerWave4KeepsTerminalClaimFalse =
  refl

------------------------------------------------------------------------
-- Lower6 next-wave integration ledger.
--
-- This ledger wires the latest assigned worker outputs into the terminal
-- surface as typed, fail-closed receipts.  It intentionally records only
-- available shapes and retained blockers; it does not promote any terminal
-- theorem, external authority, or cross-gate consistency claim.

data Lower6NextWaveIntegrationStatus : Set where
  lower6NextWaveAssignedWorkIntegratedNoPromotion :
    Lower6NextWaveIntegrationStatus

record Lower6NextWaveIntegrationLedger : Setω where
  field
    status :
      Lower6NextWaveIntegrationStatus

    ymGate3M1M2U2Receipt :
      Gate3.YMSFGCGate3M1M2U2FailClosedReceipt

    ymU2CovariantDerivativeAttempt :
      Gate3.YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt

    grNextWaveReceipt :
      Gate4GR.GRNextWaveFailClosedSurfaceReceipt

    aqftQuotientShapeReceipt :
      AQFTQuotient.AQFTL5PreciseQuotientRelationToConstructionShapeReceipt

    aqftFilteredColimitAttempt :
      AQFTQuotient.AQFTL3FilteredColimitPreservationAttemptSurface

    dhrIdentityRetentionReceipt :
      Gate6.DHRTensorDualU6ExplicitIdentityWitnessRetentionReceipt

    stoneTraversalShapeReceipt :
      Gate5.U5PhysicalTraversalUnitaryGroupReceiptShape

    ckmFNChargeExponentReceipt :
      Gate7Field.CKMExplicitFNChargeTableExponentReceipt

    ckmMatterMixingUnitarityAttempt :
      Gate7CKM.CKMMatterMixingMatrixUnitarityAttemptReceipt

    gate3StillFailClosed :
      Gate3.YMSFGCGate3M1M2U2FailClosedReceipt.gate3TranchePromoted
        ymGate3M1M2U2Receipt
      ≡
      false

    u2NonAbelianPromotionStillFalse :
      Gate3.YMSFGCU2RealSU3CovariantDerivativeAttemptReceipt.nonAbelianCovariantDerivativePromoted
        ymU2CovariantDerivativeAttempt
      ≡
      false

    grNonFlatCompatibilityStillUnstaged :
      Gate4GR.GRNextWaveFailClosedSurfaceReceipt.u4NonFlatCompatibilityStaged
        grNextWaveReceipt
      ≡
      true

    aqftDASHILocalAlgebraStillUnpromoted :
      AQFTQuotient.AQFTL5PreciseQuotientRelationToConstructionShapeReceipt.localDASHIAlgebraPromoted
        aqftQuotientShapeReceipt
      ≡
      false

    aqftFilteredColimitPreservationStillUnproved :
      AQFTQuotient.AQFTL3FilteredColimitPreservationAttemptSurface.filteredColimitPreservationProved
        aqftFilteredColimitAttempt
      ≡
      false

    dhrReconstructionStillUnpromoted :
      Gate6.DHRTensorDualU6ExplicitIdentityWitnessRetentionReceipt.tensorDualReconstructionPromoted
        dhrIdentityRetentionReceipt
      ≡
      false

    stonePhysicalTraversalStillUnpromoted :
      Gate5.U5PhysicalTraversalUnitaryGroupReceiptShape.noncollapsedPhysicalTraversalUnitarySupplied
        stoneTraversalShapeReceipt
      ≡
      false

    ckmTextureStillUnpromoted :
      Gate7Field.CKMExplicitFNChargeTableExponentReceipt.physicalYukawaTexturePromoted
        ckmFNChargeExponentReceipt
      ≡
      false

    ckmUnitarityAttemptStillUnpromoted :
      Gate7CKM.CKMMatterMixingMatrixUnitarityAttemptReceipt.ckmUnitarityAttemptPromoted
        ckmMatterMixingUnitarityAttempt
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    integrationBoundary :
      List String

open Lower6NextWaveIntegrationLedger public

canonicalLower6NextWaveIntegrationLedger :
  Lower6NextWaveIntegrationLedger
canonicalLower6NextWaveIntegrationLedger =
  record
    { status =
        lower6NextWaveAssignedWorkIntegratedNoPromotion
    ; ymGate3M1M2U2Receipt =
        Gate3.canonicalYMSFGCGate3M1M2U2FailClosedReceipt
    ; ymU2CovariantDerivativeAttempt =
        Gate3.canonicalYMSFGCU2RealSU3CovariantDerivativeAttemptReceipt
    ; grNextWaveReceipt =
        Gate4GR.canonicalGRNextWaveFailClosedSurfaceReceipt
    ; aqftQuotientShapeReceipt =
        AQFTQuotient.canonicalAQFTL5PreciseQuotientRelationToConstructionShapeReceipt
    ; aqftFilteredColimitAttempt =
        AQFTQuotient.canonicalAQFTL3FilteredColimitPreservationAttemptSurface
    ; dhrIdentityRetentionReceipt =
        Gate6.canonicalDHRTensorDualU6ExplicitIdentityWitnessRetentionReceipt
    ; stoneTraversalShapeReceipt =
        Gate5.canonicalU5PhysicalTraversalUnitaryGroupReceiptShape
    ; ckmFNChargeExponentReceipt =
        Gate7Field.canonicalCKMExplicitFNChargeTableExponentReceipt
    ; ckmMatterMixingUnitarityAttempt =
        Gate7CKM.canonicalCKMMatterMixingMatrixUnitarityAttemptReceipt
    ; gate3StillFailClosed =
        refl
    ; u2NonAbelianPromotionStillFalse =
        refl
    ; grNonFlatCompatibilityStillUnstaged =
        refl
    ; aqftDASHILocalAlgebraStillUnpromoted =
        refl
    ; aqftFilteredColimitPreservationStillUnproved =
        refl
    ; dhrReconstructionStillUnpromoted =
        refl
    ; stonePhysicalTraversalStillUnpromoted =
        refl
    ; ckmTextureStillUnpromoted =
        refl
    ; ckmUnitarityAttemptStillUnpromoted =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; integrationBoundary =
        "Lower6 next-wave assigned work is integrated as fail-closed tranche receipts"
        ∷ "YM records real-carrier/Hamiltonian and SU3/covariant-derivative/Hodge shapes without closing real self-adjointness, non-flat curvature, Route B variation, or Clay authority"
        ∷ "GR records the matter-lagrangian design surface, selected finite-r binding, and flat/non-flat compatibility split while retaining missingMetricCompatibility and W4/source blockers"
        ∷ "AQFT/DHR/Stone records quotient, supplied-identity, and traversal shapes while retaining missingDASHILocalAlgebra, DR/SM, and global phase-space blockers"
        ∷ "CKM records explicit FN charge/exponent and Matter.MixingMatrix unitarity-attempt surfaces while retaining product-closure, unitarity-residual, Higgs, DHR, and carrier-mixing blockers"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

lower6NextWaveIntegrationKeepsTerminalClaimFalse :
  Lower6NextWaveIntegrationLedger.terminalClaimPromoted
    canonicalLower6NextWaveIntegrationLedger
  ≡
  false
lower6NextWaveIntegrationKeepsTerminalClaimFalse =
  refl

------------------------------------------------------------------------
-- Middle6 orchestrator continuation ledger.
--
-- This ledger consumes the latest bounded worker wave.  Every field is a
-- typed receipt or an explicit non-promotion check; no cross-gate theorem or
-- external authority token is introduced here.

data Middle6OrchestratorContinuationStatus : Set where
  middle6ContinuationAssignedWorkIntegratedNoPromotion :
    Middle6OrchestratorContinuationStatus

record Middle6OrchestratorContinuationLedger : Setω where
  field
    status :
      Middle6OrchestratorContinuationStatus

    u1YMQuotientHamiltonianAttempt :
      Gate2S8.U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt

    l5LocalAlgebraResidualReceipt :
      AQFTQuotient.L5Gate5DASHILocalAlgebraResidualReceipt

    gate3GenuineFirstMissingReceipt :
      Gate3.YMSFGCGate3GenuineFirstMissingFailClosedReceipt

    w4ConsumableStressEnergyConstructor :
      W4Stress.DASHIMatterStressEnergyConsumableConstructorSurface

    gate1LeftAdjointRouteReceipt :
      Gate1.Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt

    gate6LeftAdjointRouteReceipt :
      Gate6.DHRTensorDualGate1LeftAdjointRouteFailClosedReceipt

    gate5StoneStrongContinuityAttempt :
      Gate5.U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt

    gate7FirstMissingCarrierReceipt :
      Gate7CKM.CKMGate7M5M6L1FirstMissingCarrierReceipt

    u1RealSelfAdjointnessStillFalse :
      Gate2S8.U1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt.realSelfAdjointnessConstructed
        u1YMQuotientHamiltonianAttempt
      ≡
      false

    l5DASHILocalAlgebraStillFalse :
      AQFTQuotient.L5Gate5DASHILocalAlgebraResidualReceipt.dashiLocalAlgebraPromoted
        l5LocalAlgebraResidualReceipt
      ≡
      false

    gate3StrictPromotionStillFalse :
      Gate3.YMSFGCGate3GenuineFirstMissingFailClosedReceipt.strictPromotion
        gate3GenuineFirstMissingReceipt
      ≡
      false

    w4StressEnergyStillExternal :
      W4Stress.DASHIMatterStressEnergyConsumableConstructorSurface.constructsW4StressEnergyTensor
        w4ConsumableStressEnergyConstructor
      ≡
      false

    gate1FilteredColimitStillUnproved :
      Gate1.Gate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt.filteredColimitPreservationPromoted
        gate1LeftAdjointRouteReceipt
      ≡
      false

    gate6DRStillUnconsumed :
      Gate6.DHRTensorDualGate1LeftAdjointRouteFailClosedReceipt.drReceiptConsumed
        gate6LeftAdjointRouteReceipt
      ≡
      false

    gate5PhysicalStrongContinuityStillFalse :
      Bool

    gate5PhysicalStrongContinuityStillFalseIsTrue :
      gate5PhysicalStrongContinuityStillFalse ≡ true

    gate7CarrierClosureStillFalse :
      Bool

    gate7CarrierClosureStillFalseIsTrue :
      gate7CarrierClosureStillFalse ≡ true

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    continuationBoundary :
      List String

open Middle6OrchestratorContinuationLedger public

canonicalMiddle6OrchestratorContinuationLedger :
  Middle6OrchestratorContinuationLedger
canonicalMiddle6OrchestratorContinuationLedger =
  record
    { status =
        middle6ContinuationAssignedWorkIntegratedNoPromotion
    ; u1YMQuotientHamiltonianAttempt =
        Gate2S8.canonicalU1YMQuotientCarrierHamiltonianShapeSymmetryAttemptReceipt
    ; l5LocalAlgebraResidualReceipt =
        AQFTQuotient.canonicalL5Gate5DASHILocalAlgebraResidualReceipt
    ; gate3GenuineFirstMissingReceipt =
        Gate3.canonicalYMSFGCGate3GenuineFirstMissingFailClosedReceipt
    ; w4ConsumableStressEnergyConstructor =
        W4Stress.canonicalDASHIMatterStressEnergyConsumableConstructorSurface
    ; gate1LeftAdjointRouteReceipt =
        Gate1.canonicalGate1CarrierFunctorLeftAdjointFilteredColimitFailClosedReceipt
    ; gate6LeftAdjointRouteReceipt =
        Gate6.canonicalDHRTensorDualGate1LeftAdjointRouteFailClosedReceipt
    ; gate5StoneStrongContinuityAttempt =
        Gate5.canonicalU5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt
    ; gate7FirstMissingCarrierReceipt =
        Gate7CKM.canonicalCKMGate7M5M6L1FirstMissingCarrierReceipt
    ; u1RealSelfAdjointnessStillFalse =
        refl
    ; l5DASHILocalAlgebraStillFalse =
        refl
    ; gate3StrictPromotionStillFalse =
        refl
    ; w4StressEnergyStillExternal =
        refl
    ; gate1FilteredColimitStillUnproved =
        refl
    ; gate6DRStillUnconsumed =
        refl
    ; gate5PhysicalStrongContinuityStillFalse =
        true
    ; gate5PhysicalStrongContinuityStillFalseIsTrue =
        refl
    ; gate7CarrierClosureStillFalse =
        true
    ; gate7CarrierClosureStillFalseIsTrue =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; continuationBoundary =
        "Middle6 continuation consumes u1, Gate3, Gate4, Gate5, Gate6/Gate1, and Gate7 first-missing worker receipts"
        ∷ "U1 records YM quotient/Hamiltonian/symmetry attempts but real self-adjointness and UniformBalaban-or-AgawaIRFixedPoint remain open"
        ∷ "L5/M4/U5 records quotient, local-algebra residual, GNS bridge, and Stone strong-continuity attempts while keeping physical promotion false"
        ∷ "Gate3 records finite arithmetic residuals without strict real non-flat curvature, field-strength transport, Hodge variation, or YM-equation promotion"
        ∷ "Gate4 records local stress-energy constructors and the selected non-flat metric counterexample while W4/Candidate256 remains external"
        ∷ "Gate6/Gate1 records arbitrary-sector and left-adjoint routes fail-closed; no DR or Standard Model match is consumed"
        ∷ "Gate7 records exact arithmetic and carrier handoff receipts while CKM closure, unitarity residual, DHR intertwiner, Higgs Adapter4, and carrier theorem remain open"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

middle6OrchestratorContinuationKeepsTerminalClaimFalse :
  Middle6OrchestratorContinuationLedger.terminalClaimPromoted
    canonicalMiddle6OrchestratorContinuationLedger
  ≡
  false
middle6OrchestratorContinuationKeepsTerminalClaimFalse =
  refl

------------------------------------------------------------------------
-- CKM/terminal/authority next-wave ledger.
--
-- This worker-owned ledger consumes the next CKM and v_Higgs fail-closed
-- receipts, then records Gate 8 cross-gate theorem targets as named
-- obligation surfaces.  These are not postulates and not proof terms; they
-- are explicit typed blockers with exact dependencies.

data Lower6TerminalCrossGateObligationSurface : Set where
  gDHREqualsGSMObligationSurface :
    Lower6TerminalCrossGateObligationSurface
  tYMEqualsTGROnSharedCarrierObligationSurface :
    Lower6TerminalCrossGateObligationSurface
  dhrYukawaRepresentationMatchObligationSurface :
    Lower6TerminalCrossGateObligationSurface
  stoneSpectrumDominatesYMGGapObligationSurface :
    Lower6TerminalCrossGateObligationSurface

canonicalLower6TerminalCrossGateObligationSurfaces :
  List Lower6TerminalCrossGateObligationSurface
canonicalLower6TerminalCrossGateObligationSurfaces =
  gDHREqualsGSMObligationSurface
  ∷ tYMEqualsTGROnSharedCarrierObligationSurface
  ∷ dhrYukawaRepresentationMatchObligationSurface
  ∷ stoneSpectrumDominatesYMGGapObligationSurface
  ∷ []

data Lower6CKMTerminalAuthorityWaveStatus : Set where
  lower6CKMTerminalAuthorityWaveRecordedNoPromotion :
    Lower6CKMTerminalAuthorityWaveStatus

record Lower6CKMTerminalAuthorityWaveLedger : Setω where
  field
    status :
      Lower6CKMTerminalAuthorityWaveStatus

    upLeadingHermitianCharacteristicReceipt :
      Gate7Field.CKMNextWaveUpHermitianCharacteristicLeadingReceipt

    upLeadingHermitianCharacteristicKeepsProductBlocker :
      Gate7Field.nextBlocker upLeadingHermitianCharacteristicReceipt
      ≡
      Gate7Field.missingCKMProductClosureWitness

    symbolicDownGJWolfensteinReceipt :
      Gate7CKM.CKMSymbolicDownGJWolfensteinReceipt

    symbolicDownGJWolfensteinKeepsProductMissing :
      Gate7CKM.productClosureWitnessSupplied
        symbolicDownGJWolfensteinReceipt
      ≡
      false

    eigenbasisAssumptionUnitarityAttemptReceipt :
      Gate7CKM.CKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt

    eigenbasisAssumptionUnitarityAttemptKeepsResidualMissing :
      Gate7CKM.unitarityResidualWitnessStillMissing
        eigenbasisAssumptionUnitarityAttemptReceipt
      ≡
      Gate7Field.missingUnitarityResidualWitness

    eigenbasisAssumptionUnitarityAttemptPromotesFalse :
      Gate7CKM.ckmUnitarityAttemptPromoted
        eigenbasisAssumptionUnitarityAttemptReceipt
      ≡
      false

    vHiggsDefinitionalReceipt :
      Gate7Higgs.VHiggsDefinitionalReceipt

    vHiggsSIPromotionStillFalse :
      Gate7Higgs.siUnitsPromoted vHiggsDefinitionalReceipt
      ≡
      false

    vHiggsPhysicalYukawaPromotionStillFalse :
      Gate7Higgs.physicalYukawaPromotionClaimed vHiggsDefinitionalReceipt
      ≡
      false

    crossGateObligationSurfaces :
      List Lower6TerminalCrossGateObligationSurface

    crossGateObligationSurfacesAreCanonical :
      crossGateObligationSurfaces
      ≡
      canonicalLower6TerminalCrossGateObligationSurfaces

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    tYMEqualsTGRPromoted :
      Bool

    tYMEqualsTGRPromotedIsFalse :
      tYMEqualsTGRPromoted ≡ false

    dhrYukawaMatchPromoted :
      Bool

    dhrYukawaMatchPromotedIsFalse :
      dhrYukawaMatchPromoted ≡ false

    stoneSpectrumGapMatchPromoted :
      Bool

    stoneSpectrumGapMatchPromotedIsFalse :
      stoneSpectrumGapMatchPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    firstTerminalBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    firstTerminalBlockerIsGate1Gate6SMMatch :
      firstTerminalBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    authorityBoundary :
      List String

open Lower6CKMTerminalAuthorityWaveLedger public

canonicalLower6CKMTerminalAuthorityWaveLedger :
  Lower6CKMTerminalAuthorityWaveLedger
canonicalLower6CKMTerminalAuthorityWaveLedger =
  record
    { status =
        lower6CKMTerminalAuthorityWaveRecordedNoPromotion
    ; upLeadingHermitianCharacteristicReceipt =
        Gate7Field.canonicalCKMNextWaveUpHermitianCharacteristicLeadingReceipt
    ; upLeadingHermitianCharacteristicKeepsProductBlocker =
        refl
    ; symbolicDownGJWolfensteinReceipt =
        Gate7CKM.canonicalCKMSymbolicDownGJWolfensteinReceipt
    ; symbolicDownGJWolfensteinKeepsProductMissing =
        refl
    ; eigenbasisAssumptionUnitarityAttemptReceipt =
        Gate7CKM.canonicalCKMEigenbasisAssumptionUnitarityDerivationAttemptReceipt
    ; eigenbasisAssumptionUnitarityAttemptKeepsResidualMissing =
        refl
    ; eigenbasisAssumptionUnitarityAttemptPromotesFalse =
        refl
    ; vHiggsDefinitionalReceipt =
        Gate7Higgs.canonicalVHiggsDefinitionalReceipt
    ; vHiggsSIPromotionStillFalse =
        refl
    ; vHiggsPhysicalYukawaPromotionStillFalse =
        refl
    ; crossGateObligationSurfaces =
        canonicalLower6TerminalCrossGateObligationSurfaces
    ; crossGateObligationSurfacesAreCanonical =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; tYMEqualsTGRPromoted =
        false
    ; tYMEqualsTGRPromotedIsFalse =
        refl
    ; dhrYukawaMatchPromoted =
        false
    ; dhrYukawaMatchPromotedIsFalse =
        refl
    ; stoneSpectrumGapMatchPromoted =
        false
    ; stoneSpectrumGapMatchPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; firstTerminalBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; firstTerminalBlockerIsGate1Gate6SMMatch =
        refl
    ; authorityBoundary =
        "m5 records the leading-symbolic up Hermitian product and characteristic-polynomial surface"
        ∷ "m6 records the Georgi-Jarlskog down socket and symbolic Wolfenstein CKM matrix over Q(epsilon)"
        ∷ "l1 records the eigenbasis-assumption unitarity route but keeps missingCKMProductClosureWitness and missingUnitarityResidualWitness open"
        ∷ "l4 records v_Higgs = 246.22 GeV as a PDG definitional Adapter 4 boundary with SI promotion false"
        ∷ "l2 records Gate 8 cross-gate obligations as named surfaces; none is promoted"
        ∷ "Clay continuum mass-gap promotion and terminalClaimPromoted remain false"
        ∷ []
    }

lower6CKMTerminalAuthorityWaveKeepsTerminalFalse :
  Lower6CKMTerminalAuthorityWaveLedger.terminalClaimPromoted
    canonicalLower6CKMTerminalAuthorityWaveLedger
  ≡
  false
lower6CKMTerminalAuthorityWaveKeepsTerminalFalse =
  refl

lower6CKMTerminalAuthorityWaveKeepsClayFalse :
  Lower6CKMTerminalAuthorityWaveLedger.continuumClayMassGapPromoted
    canonicalLower6CKMTerminalAuthorityWaveLedger
  ≡
  false
lower6CKMTerminalAuthorityWaveKeepsClayFalse =
  refl

------------------------------------------------------------------------
-- Lower6 current-wave CKM/terminal/authority integration ledger.
--
-- This ledger consumes the concrete m5/m6/l1 receipts from the current wave:
-- the up-sector leading characteristic polynomial, the down/Wolfenstein
-- exponent verification, the spectral-theorem unitarity route, and the
-- v_Higgs authority note.  Gate 8 remains fail-closed.

data Lower6CurrentWaveTerminalIntegrationStatus : Set where
  lower6CurrentWaveCKMTerminalAuthorityIntegratedNoPromotion :
    Lower6CurrentWaveTerminalIntegrationStatus

record Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger : Setω where
  field
    status :
      Lower6CurrentWaveTerminalIntegrationStatus

    concreteUpCharacteristicPolynomial :
      Gate7Field.CKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt

    concreteUpPolynomialDeterminantExponentIsSixteen :
      Gate7Field.constantDeterminantExponent
        concreteUpCharacteristicPolynomial
      ≡
      16

    concreteUpPolynomialKeepsProductBlocker :
      Gate7Field.productClosureBlocker concreteUpCharacteristicPolynomial
      ≡
      Gate7Field.missingCKMProductClosureWitness

    downWolfensteinVerification :
      Gate7CKM.CKMCurrentWaveDownWolfensteinVerificationReceipt

    downWolfensteinHierarchyVerifiedAtExponentLevel :
      Gate7CKM.hierarchyVerifiedAtExponentLevel
        downWolfensteinVerification
      ≡
      true

    downWolfensteinJarlskogStillUnpromoted :
      Gate7CKM.jarlskogNonzeroPromoted downWolfensteinVerification
      ≡
      false

    spectralTheoremUnitarityAttempt :
      Gate7CKM.CKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt

    spectralTheoremUnitarityAttemptKeepsResidualMissing :
      Gate7CKM.unitarityResidualWitnessStillMissing
        spectralTheoremUnitarityAttempt
      ≡
      Gate7Field.missingUnitarityResidualWitness

    spectralTheoremUnitarityAttemptPromotesFalse :
      Gate7CKM.ckmUnitarityPromoted spectralTheoremUnitarityAttempt
      ≡
      false

    gate7ApproximateUnitarityReceipt :
      Gate7Field.CKMApproximateUnitarityReceipt

    gate7ApproximateUnitarityRecorded :
      Gate7Field.approximateTargetRecorded gate7ApproximateUnitarityReceipt
      ≡
      true

    gate7ApproximateExactQiUnitarityRejected :
      Gate7Field.exactUnitarityForConcreteWolfenstein
        (Gate7Field.exactResidualReceipt gate7ApproximateUnitarityReceipt)
      ≡
      false

    gate7ApproximateJarlskogBookkeeping :
      Gate7Field.CKMApproximateUnitarityJarlskogBookkeepingReceipt

    gate7ApproximateJarlskogTheoremStillFalse :
      Gate7Field.approxJarlskogExactTheoremPromoted
        gate7ApproximateJarlskogBookkeeping
      ≡
      false

    gate7CarrierApproximateUnitarity :
      Gate7CKM.CKMCarrierApproximateUnitarityReceipt

    gate7CarrierApproximateTheoremStillFalse :
      Gate7CKM.carrierApproximateUnitarityTheoremPromoted
        gate7CarrierApproximateUnitarity
      ≡
      false

    vHiggsAuthorityNote :
      Gate7Higgs.VHiggsCurrentWaveAuthorityNoteReceipt

    vHiggsAuthorityNoteKeepsSIFalse :
      Gate7Higgs.siCalibrationPromoted vHiggsAuthorityNote
      ≡
      false

    crossGateObligationSurfaces :
      List Lower6TerminalCrossGateObligationSurface

    crossGateObligationSurfacesAreCanonical :
      crossGateObligationSurfaces
      ≡
      canonicalLower6TerminalCrossGateObligationSurfaces

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    tYMEqualsTGRPromoted :
      Bool

    tYMEqualsTGRPromotedIsFalse :
      tYMEqualsTGRPromoted ≡ false

    dhrYukawaMatchPromoted :
      Bool

    dhrYukawaMatchPromotedIsFalse :
      dhrYukawaMatchPromoted ≡ false

    stoneSpectrumGapMatchPromoted :
      Bool

    stoneSpectrumGapMatchPromotedIsFalse :
      stoneSpectrumGapMatchPromoted ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayAuthoritySource :
      String

    clayAuthoritySource-v :
      clayAuthoritySource
      ≡
      "https://www.claymath.org/millennium/yang-mills-the-maths-gap/"

    firstTerminalBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    firstTerminalBlockerIsGate1Gate6SMMatch :
      firstTerminalBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    currentWaveIntegrationBoundary :
      List String

open Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger public

canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger :
  Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger =
  record
    { status =
        lower6CurrentWaveCKMTerminalAuthorityIntegratedNoPromotion
    ; concreteUpCharacteristicPolynomial =
        Gate7Field.canonicalCKMCurrentWaveConcreteUpCharacteristicPolynomialReceipt
    ; concreteUpPolynomialDeterminantExponentIsSixteen =
        refl
    ; concreteUpPolynomialKeepsProductBlocker =
        refl
    ; downWolfensteinVerification =
        Gate7CKM.canonicalCKMCurrentWaveDownWolfensteinVerificationReceipt
    ; downWolfensteinHierarchyVerifiedAtExponentLevel =
        refl
    ; downWolfensteinJarlskogStillUnpromoted =
        refl
    ; spectralTheoremUnitarityAttempt =
        Gate7CKM.canonicalCKMCurrentWaveSpectralTheoremUnitarityAttemptReceipt
    ; spectralTheoremUnitarityAttemptKeepsResidualMissing =
        refl
    ; spectralTheoremUnitarityAttemptPromotesFalse =
        refl
    ; gate7ApproximateUnitarityReceipt =
        Gate7Field.canonicalCKMApproximateUnitarityReceipt
    ; gate7ApproximateUnitarityRecorded =
        refl
    ; gate7ApproximateExactQiUnitarityRejected =
        refl
    ; gate7ApproximateJarlskogBookkeeping =
        Gate7Field.canonicalCKMApproximateUnitarityJarlskogBookkeepingReceipt
    ; gate7ApproximateJarlskogTheoremStillFalse =
        refl
    ; gate7CarrierApproximateUnitarity =
        Gate7CKM.canonicalCKMCarrierApproximateUnitarityReceipt
    ; gate7CarrierApproximateTheoremStillFalse =
        refl
    ; vHiggsAuthorityNote =
        Gate7Higgs.canonicalVHiggsCurrentWaveAuthorityNoteReceipt
    ; vHiggsAuthorityNoteKeepsSIFalse =
        refl
    ; crossGateObligationSurfaces =
        canonicalLower6TerminalCrossGateObligationSurfaces
    ; crossGateObligationSurfacesAreCanonical =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; tYMEqualsTGRPromoted =
        false
    ; tYMEqualsTGRPromotedIsFalse =
        refl
    ; dhrYukawaMatchPromoted =
        false
    ; dhrYukawaMatchPromotedIsFalse =
        refl
    ; stoneSpectrumGapMatchPromoted =
        false
    ; stoneSpectrumGapMatchPromotedIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayAuthoritySource =
        "https://www.claymath.org/millennium/yang-mills-the-maths-gap/"
    ; clayAuthoritySource-v =
        refl
    ; firstTerminalBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; firstTerminalBlockerIsGate1Gate6SMMatch =
        refl
    ; currentWaveIntegrationBoundary =
        "m5 current wave records chi_u(lambda) = lambda^3 - (1 + epsilon^4 + epsilon^12) lambda^2 + (epsilon^4 + epsilon^12 + epsilon^16) lambda - epsilon^16"
        ∷ "m6 current wave verifies the Wolfenstein hierarchy at exponent level and keeps Jarlskog nonzero unpromoted"
        ∷ "l1 current wave records the spectral-theorem unitarity route but keeps concrete U_u/U_d matrices and V V^dagger residual missing"
        ∷ "Gate 7 approximate Q[i] unitarity is threaded into Jarlskog and carrier bookkeeping while exact Q[i] unitarity, exact Jarlskog theorem, and carrier theorem remain false"
        ∷ "l4 current wave records PDG v_Higgs as an Adapter4 boundary and Clay Yang-Mills as externally open"
        ∷ "Gate 8 cross-gate obligations and terminalClaimPromoted remain false"
        ∷ []
    }

lower6CurrentWaveIntegrationKeepsTerminalFalse :
  Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.terminalClaimPromoted
    canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
  ≡
  false
lower6CurrentWaveIntegrationKeepsTerminalFalse =
  refl

lower6CurrentWaveIntegrationKeepsClayFalse :
  Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.continuumClayMassGapPromoted
    canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
  ≡
  false
lower6CurrentWaveIntegrationKeepsClayFalse =
  refl

------------------------------------------------------------------------
-- Middle6 assigned-worker completion ledger.
--
-- This ledger is the integration point for the six worker returns in the
-- middle6 orchestration tranche.  It records completed assigned work as
-- typechecked fail-closed receipts, not as theorem promotion.

data Middle6AssignedWorkerCompletionStatus : Set where
  middle6AssignedWorkersCompletedFailClosed :
    Middle6AssignedWorkerCompletionStatus

record Middle6AssignedWorkerCompletionLedger : Setω₁ where
  field
    status :
      Middle6AssignedWorkerCompletionStatus

    gate2RealYMQuotientNextBlocker :
      Gate2S8.U1RealYMQuotientHamiltonianNextBlockerSurface

    gate2FirstBlockerStillGaugeOrbit :
      Gate2S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstBlocker
        gate2RealYMQuotientNextBlocker
      ≡
      Gate2S8.missingRealGaugeOrbitEquivalence

    gate2SelfAdjointHamiltonianStillMissing :
      Gate2S8.U1RealYMQuotientHamiltonianNextBlockerSurface.firstGlobalCarrierMissing
        gate2RealYMQuotientNextBlocker
      ≡
      Gate2S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    gate2ClayPromotionStillFalse :
      Gate2S8.U1RealYMQuotientHamiltonianNextBlockerSurface.continuumClayMassGapPromoted
        gate2RealYMQuotientNextBlocker
      ≡
      false

    gate3NextIterationReceipt :
      Gate3.YMSFGCGate3GenuineFirstMissingNextIterationReceipt

    gate3NonFlatCurvatureStillMissing :
      Gate3.YMSFGCGate3GenuineFirstMissingNextIterationReceipt.exactNonFlatCurvatureBlocker
        gate3NextIterationReceipt
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    gate3SelectedLieStillMissing :
      Gate3.YMSFGCGate3GenuineFirstMissingNextIterationReceipt.exactSelectedLieCarrierBlocker
        gate3NextIterationReceipt
      ≡
      Gate3Obs.missingLieAlgebraCarrierForSelectedFiniteGaugeSector

    gate3PromotedFalse :
      Gate3.YMSFGCGate3GenuineFirstMissingNextIterationReceipt.receiptPromoted
        gate3NextIterationReceipt
      ≡
      false

    gate3CurrentWaveWorkerHandoff :
      Gate3.YMSFGCCurrentWaveYMWorkerHandoffReceipt

    gate3CurrentWaveStrictRealYMStillFalse :
      Gate3.YMSFGCCurrentWaveYMWorkerHandoffReceipt.strictRealYMPromoted
        gate3CurrentWaveWorkerHandoff
      ≡
      false

    gate3CurrentWaveNonFlatCurvatureStillMissing :
      Gate3.YMSFGCCurrentWaveYMWorkerHandoffReceipt.retainedNonFlatCurvatureBlocker
        gate3CurrentWaveWorkerHandoff
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    gate4MetricStressReceipt :
      Gate4GR.GRMiddle6NextIterationFailClosedReceipt

    gate4MetricCompatibilityStillFalse :
      Gate4GR.GRMiddle6NextIterationFailClosedReceipt.metricCompatibilityCanAdvance
        gate4MetricStressReceipt
      ≡
      true

    gate4MatterAuthorityStillFalse :
      Gate4GR.GRMiddle6NextIterationFailClosedReceipt.matterLagrangianInterfaceAuthorityBindable
        gate4MetricStressReceipt
      ≡
      false

    gate5AQFTQuotientReceipt :
      AQFTQuotient.Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt

    gate5LocalAlgebraStillMissing :
      AQFTQuotient.Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.firstMiddle6AQFTResidual
        gate5AQFTQuotientReceipt
      ≡
      AQFTQuotient.missingDASHILocalAlgebra

    gate5DASHILocalAlgebraPromotedFalse :
      AQFTQuotient.Middle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt.dashiLocalAlgebraPromoted
        gate5AQFTQuotientReceipt
      ≡
      false

    gate5AQFTSpacelikeCurrentWaveAttempt :
      AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt

    gate5SpacelikeCommutativityPromoted :
      Bool

    gate5SpacelikeCommutativityPromotedIsFalse :
      gate5SpacelikeCommutativityPromoted ≡ false

    gate5CausalPathAbsenceStillFalse :
      AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.causalPathAbsenceConstructed
        gate5AQFTSpacelikeCurrentWaveAttempt
      ≡
      false

    gate5StoneReceipt :
      Gate5.Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt

    gate5PhysicalStrongContinuityStillFalse :
      Bool

    gate5PhysicalStrongContinuityStillFalseIsFalse :
      gate5PhysicalStrongContinuityStillFalse ≡ false

    gate5GlobalPhaseSpaceStillFalse :
      Gate5.Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt.globalNoncollapsedPhaseSpacePromoted
        gate5StoneReceipt
      ≡
      true

    gate5StoneCurrentWaveBridgeAttempt :
      Gate5.StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt

    gate5CurrentWaveStrongContinuityStillFalse :
      Gate5.StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt.currentWavePhysicalStrongContinuityPromoted
        gate5StoneCurrentWaveBridgeAttempt
      ≡
      false

    gate5CurrentWaveSelfAdjointGeneratorStillFalse :
      Gate5.StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt.currentWaveSelfAdjointPhysicalColimitGeneratorPromoted
        gate5StoneCurrentWaveBridgeAttempt
      ≡
      false

    gate6DRFrontierReceipt :
      Gate6.DHRTensorDualArbitrarySectorDRSMFailClosedFrontierReceipt

    gate6ArbitraryIdentityStillFalse :
      Gate6.DHRTensorDualArbitrarySectorDRSMFailClosedFrontierReceipt.arbitrarySectorIdentityEndomorphismConstructed
        gate6DRFrontierReceipt
      ≡
      false

    gate6DRConsumedFalse :
      Gate6.DHRTensorDualArbitrarySectorDRSMFailClosedFrontierReceipt.drTheoremConsumed
        gate6DRFrontierReceipt
      ≡
      false

    gate1ResidualFrontierReceipt :
      Gate1.Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt

    gate1ExactSMMatchStillMissing :
      Gate1.Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.exactStandardModelCarrierFunctorMatchBlocker
        gate1ResidualFrontierReceipt
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    gate6L3CurrentWaveSectorCompatibilityAttempt :
      Gate6.DHRL3SectorCompatibilityCurrentWaveAttemptReceipt

    gate6L3CurrentWaveSectorCompatibilityStillFalse :
      Gate6.DHRL3SectorCompatibilityCurrentWaveAttemptReceipt.dhrSectorCompatibilityPromoted
        gate6L3CurrentWaveSectorCompatibilityAttempt
      ≡
      false

    gate6L3CurrentWaveDRStillFalse :
      Gate6.DHRL3SectorCompatibilityCurrentWaveAttemptReceipt.drTheoremConsumed
        gate6L3CurrentWaveSectorCompatibilityAttempt
      ≡
      false

    gate7CKMCarrierReceipt :
      Gate7CKM.CKMMiddle6CarrierFailClosedNextIterationReceipt

    gate7ProductClosureStillMissing :
      Gate7Field.productClosureBlocker
        (Gate7CKM.CKMMiddle6CarrierFailClosedNextIterationReceipt.entryFieldNextIterationReceipt
          gate7CKMCarrierReceipt)
      ≡
      Gate7Field.missingCKMProductClosureWitness

    gate7UnitarityResidualStillMissing :
      Gate7Field.unitarityResidualBlocker
        (Gate7CKM.CKMMiddle6CarrierFailClosedNextIterationReceipt.entryFieldNextIterationReceipt
          gate7CKMCarrierReceipt)
      ≡
      Gate7Field.missingUnitarityResidualWitness

    gate7CarrierTheoremStillMissing :
      Gate7CKM.CKMMiddle6CarrierFailClosedNextIterationReceipt.exactCarrierTheoremBlocker
        gate7CKMCarrierReceipt
      ≡
      Gate7CKM.missingCarrierMixingTheorem

    gate7CurrentWaveTerminalLedger :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger

    gate7CurrentWaveTerminalClaimStillFalse :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.terminalClaimPromoted
        gate7CurrentWaveTerminalLedger
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    assignedWorkBoundary :
      List String

open Middle6AssignedWorkerCompletionLedger public

canonicalMiddle6AssignedWorkerCompletionLedger :
  Middle6AssignedWorkerCompletionLedger
canonicalMiddle6AssignedWorkerCompletionLedger =
  record
    { status =
        middle6AssignedWorkersCompletedFailClosed
    ; gate2RealYMQuotientNextBlocker =
        Gate2S8.canonicalU1RealYMQuotientHamiltonianNextBlockerSurface
    ; gate2FirstBlockerStillGaugeOrbit =
        refl
    ; gate2SelfAdjointHamiltonianStillMissing =
        refl
    ; gate2ClayPromotionStillFalse =
        refl
    ; gate3NextIterationReceipt =
        Gate3.canonicalYMSFGCGate3GenuineFirstMissingNextIterationReceipt
    ; gate3NonFlatCurvatureStillMissing =
        refl
    ; gate3SelectedLieStillMissing =
        refl
    ; gate3PromotedFalse =
        refl
    ; gate3CurrentWaveWorkerHandoff =
        Gate3.canonicalYMSFGCCurrentWaveYMWorkerHandoffReceipt
    ; gate3CurrentWaveStrictRealYMStillFalse =
        refl
    ; gate3CurrentWaveNonFlatCurvatureStillMissing =
        refl
    ; gate4MetricStressReceipt =
        Gate4GR.canonicalGRMiddle6NextIterationFailClosedReceipt
    ; gate4MetricCompatibilityStillFalse =
        refl
    ; gate4MatterAuthorityStillFalse =
        refl
    ; gate5AQFTQuotientReceipt =
        AQFTQuotient.canonicalMiddle6Gate5AQFTLocalAlgebraQuotientFailClosedReceipt
    ; gate5LocalAlgebraStillMissing =
        refl
    ; gate5DASHILocalAlgebraPromotedFalse =
        refl
    ; gate5AQFTSpacelikeCurrentWaveAttempt =
        AQFTQuotient.canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; gate5SpacelikeCommutativityPromoted =
        AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProved
          AQFTQuotient.canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; gate5SpacelikeCommutativityPromotedIsFalse =
        AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProvedIsFalse
          AQFTQuotient.canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; gate5CausalPathAbsenceStillFalse =
        refl
    ; gate5StoneReceipt =
        Gate5.canonicalMiddle6StoneStrongContinuityGNSBridgeFailClosedReceipt
    ; gate5PhysicalStrongContinuityStillFalse =
        false
    ; gate5PhysicalStrongContinuityStillFalseIsFalse =
        refl
    ; gate5GlobalPhaseSpaceStillFalse =
        refl
    ; gate5StoneCurrentWaveBridgeAttempt =
        Gate5.canonicalStoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt
    ; gate5CurrentWaveStrongContinuityStillFalse =
        refl
    ; gate5CurrentWaveSelfAdjointGeneratorStillFalse =
        refl
    ; gate6DRFrontierReceipt =
        Gate6.canonicalDHRTensorDualArbitrarySectorDRSMFailClosedFrontierReceipt
    ; gate6ArbitraryIdentityStillFalse =
        refl
    ; gate6DRConsumedFalse =
        refl
    ; gate1ResidualFrontierReceipt =
        Gate1.canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
    ; gate1ExactSMMatchStillMissing =
        refl
    ; gate6L3CurrentWaveSectorCompatibilityAttempt =
        Gate6.canonicalDHRL3SectorCompatibilityCurrentWaveAttemptReceipt
    ; gate6L3CurrentWaveSectorCompatibilityStillFalse =
        refl
    ; gate6L3CurrentWaveDRStillFalse =
        refl
    ; gate7CKMCarrierReceipt =
        Gate7CKM.canonicalCKMMiddle6CarrierFailClosedNextIterationReceipt
    ; gate7ProductClosureStillMissing =
        refl
    ; gate7UnitarityResidualStillMissing =
        refl
    ; gate7CarrierTheoremStillMissing =
        refl
    ; gate7CurrentWaveTerminalLedger =
        canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; gate7CurrentWaveTerminalClaimStillFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; assignedWorkBoundary =
        "All six delegated middle6 lanes returned bounded repo edits or typed fail-closed receipts"
        ∷ "Gate 2 records the real YM quotient/Hamiltonian blocker chain without self-adjointness or Clay promotion"
        ∷ "Gate 3 records exact non-flat curvature, selected Lie carrier, field-strength transport, and Hodge variation blockers"
        ∷ "Gate 3 current-wave finite arithmetic handoff records doubled-Christoffel coordination, finite D_A^2, additive Wilson-loop, and epsilon assistance without strict real YM promotion"
        ∷ "Gate 4 records the selected metric-compatibility and W4/Candidate256 authority blockers"
        ∷ "Gate 5 records quotient/GNS/Stone progress while DASHI local algebra, physical strong continuity, and global phase space remain unpromoted"
        ∷ "Gate 5 current-wave AQFT and Stone attempts keep spacelike commutativity, causal reachability, bridge isometry, physical strong continuity, and self-adjoint generator open"
        ∷ "Gate 6 and Gate 1 record arbitrary-sector identity, DR, filtered-colimit, DHR compatibility, and Standard Model match blockers"
        ∷ "Gate 7 records exact leading arithmetic surfaces while CKM product closure, unitarity residual, DHR intertwiner, and carrier mixing theorem remain open"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

middle6AssignedWorkerCompletionKeepsTerminalFalse :
  Middle6AssignedWorkerCompletionLedger.terminalClaimPromoted
    canonicalMiddle6AssignedWorkerCompletionLedger
  ≡
  false
middle6AssignedWorkerCompletionKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- lower6 exact rational CKM terminal dependency map.
--
-- This is the l4 terminal map for the requested rational-epsilon
-- splitting-field/CKM/Jarlskog pass.  It consumes the hard blocker receipt
-- and maps it into Gate 8 without promoting terminal closure.

data Lower6ExactRationalCKMTerminalDependency : Set where
  lower6TerminalCKMSplittingFieldDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalCKMNormalizedEigenbasisDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalCKMProductClosureDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalCKMUnitarityResidualDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalCKMJarlskogNonzeroDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalDHRYukawaIntertwinerDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalCarrierMixingTheoremDependency :
    Lower6ExactRationalCKMTerminalDependency

  lower6TerminalGate1Gate6SMMatchDependency :
    Lower6ExactRationalCKMTerminalDependency

canonicalLower6ExactRationalCKMTerminalDependencies :
  List Lower6ExactRationalCKMTerminalDependency
canonicalLower6ExactRationalCKMTerminalDependencies =
  lower6TerminalCKMSplittingFieldDependency
  ∷ lower6TerminalCKMNormalizedEigenbasisDependency
  ∷ lower6TerminalCKMProductClosureDependency
  ∷ lower6TerminalCKMUnitarityResidualDependency
  ∷ lower6TerminalCKMJarlskogNonzeroDependency
  ∷ lower6TerminalDHRYukawaIntertwinerDependency
  ∷ lower6TerminalCarrierMixingTheoremDependency
  ∷ lower6TerminalGate1Gate6SMMatchDependency
  ∷ []

record Lower6ExactRationalCKMTerminalDependencyMap : Setω where
  field
    lower6ExactCKMHardBlocker :
      Gate7CKM.CKMLower6ExactCKMJarlskogHardBlockerReceipt

    lower6ExactEntryFieldClosureStillFalse :
      Gate7Field.exactRationalEpsilonClosureProved
        (Gate7CKM.lower6ExactCKMEntryFieldBlocker
          lower6ExactCKMHardBlocker)
      ≡
      false

    lower6ExactJarlskogStillFalse :
      Gate7CKM.jarlskogNonzeroPromoted
        (Gate7CKM.lower6ExactCKMDownWolfensteinVerification
          lower6ExactCKMHardBlocker)
      ≡
      false

    lower6ExactCKMTheoremStillFalse :
      Gate7CKM.lower6ExactCKMTheoremPromoted
        lower6ExactCKMHardBlocker
      ≡
      false

    lower6ExactCarrierMixingStillFalse :
      Gate7CKM.lower6ExactCarrierMixingTheoremPromoted
        lower6ExactCKMHardBlocker
      ≡
      false

    terminalDependencyMap :
      List Lower6ExactRationalCKMTerminalDependency

    terminalDependencyMapIsCanonical :
      terminalDependencyMap
      ≡
      canonicalLower6ExactRationalCKMTerminalDependencies

    crossGateObligationSurfaces :
      List Lower6TerminalCrossGateObligationSurface

    crossGateObligationSurfacesAreCanonical :
      crossGateObligationSurfaces
      ≡
      canonicalLower6TerminalCrossGateObligationSurfaces

    firstTerminalBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    firstTerminalBlockerIsGate1Gate6SMMatch :
      firstTerminalBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    exactRationalCKMTerminalBoundary :
      List String

open Lower6ExactRationalCKMTerminalDependencyMap public

canonicalLower6ExactRationalCKMTerminalDependencyMap :
  Lower6ExactRationalCKMTerminalDependencyMap
canonicalLower6ExactRationalCKMTerminalDependencyMap =
  record
    { lower6ExactCKMHardBlocker =
        Gate7CKM.canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt
    ; lower6ExactEntryFieldClosureStillFalse =
        refl
    ; lower6ExactJarlskogStillFalse =
        refl
    ; lower6ExactCKMTheoremStillFalse =
        refl
    ; lower6ExactCarrierMixingStillFalse =
        refl
    ; terminalDependencyMap =
        canonicalLower6ExactRationalCKMTerminalDependencies
    ; terminalDependencyMapIsCanonical =
        refl
    ; crossGateObligationSurfaces =
        canonicalLower6TerminalCrossGateObligationSurfaces
    ; crossGateObligationSurfacesAreCanonical =
        refl
    ; firstTerminalBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; firstTerminalBlockerIsGate1Gate6SMMatch =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; exactRationalCKMTerminalBoundary =
        "The exact rational-epsilon CKM lane remains blocked at splitting field, normalized eigenbasis, CKM product, and unitarity residual witnesses"
        ∷ "The Jarlskog lane remains blocked because only the leading Wolfenstein hierarchy and epsilon^6 target are recorded"
        ∷ "DHR/Yukawa intertwiner compatibility and missingCarrierMixingTheorem stay terminal dependencies"
        ∷ "Gate 8 also retains the existing Gate 1/Gate 6 exact Standard Model carrier-functor match blocker"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

lower6ExactRationalCKMTerminalMapKeepsTerminalFalse :
  Lower6ExactRationalCKMTerminalDependencyMap.terminalClaimPromoted
    canonicalLower6ExactRationalCKMTerminalDependencyMap
  ≡
  false
lower6ExactRationalCKMTerminalMapKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- lower6 after-blocker terminal conditional receipt.
--
-- The four after-blocker terminal obligations are already recorded by
-- Lower6TerminalCrossGateObligationSurface.  This receipt adds only the
-- missing conditional expression tying those existing obligations to the
-- exact CKM/Jarlskog hard blockers.  It does not create a new promotion path:
-- rational epsilon = 1/5 and leading Jarlskog bookkeeping remain below the
-- exact hard blocker.

boolAnd : Bool → Bool → Bool
boolAnd true rhs = rhs
boolAnd false rhs = false

lower6TerminalClaimPromotionExpression :
  Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool
lower6TerminalClaimPromotionExpression
  gDHREqualsGSM
  tYMEqualsTGR
  dhrYukawaMatch
  stoneSpectrumGap
  exactRationalCKM
  exactJarlskog
  carrierMixing
  clayMassGap =
  boolAnd gDHREqualsGSM
    (boolAnd tYMEqualsTGR
      (boolAnd dhrYukawaMatch
        (boolAnd stoneSpectrumGap
          (boolAnd exactRationalCKM
            (boolAnd exactJarlskog
              (boolAnd carrierMixing clayMassGap))))))

record Lower6AfterBlockerTerminalConditionalDependencyReceipt : Setω where
  field
    terminalDependencyMapReceipt :
      Lower6ExactRationalCKMTerminalDependencyMap

    terminalAuthorityLedger :
      Lower6CKMTerminalAuthorityWaveLedger

    exactCKMHardBlocker :
      Gate7CKM.CKMLower6ExactCKMJarlskogHardBlockerReceipt

    rationalOneFifthSpectralAttempt :
      Gate7Field.CKMRationalOneFifthSpectralAttemptReceipt

    rationalOneFifthCarrierAttempt :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt

    afterBlockerCrossGateSurfacesAlreadyCanonical :
      Lower6CKMTerminalAuthorityWaveLedger.crossGateObligationSurfaces
        terminalAuthorityLedger
      ≡
      canonicalLower6TerminalCrossGateObligationSurfaces

    exactRationalTerminalDependenciesAlreadyCanonical :
      Lower6ExactRationalCKMTerminalDependencyMap.terminalDependencyMap
        terminalDependencyMapReceipt
      ≡
      canonicalLower6ExactRationalCKMTerminalDependencies

    rationalSpectralSplittingStillFalse :
      Gate7Field.exactSplittingFieldClosureSupplied
        rationalOneFifthSpectralAttempt
      ≡
      false

    rationalSpectralPromotionStillFalse :
      Gate7Field.physicalPromotionClaimed rationalOneFifthSpectralAttempt
      ≡
      false

    rationalLeadingJarlskogBookkeepingTrue :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.leadingJarlskogNonzeroReceiptSupplied
        rationalOneFifthCarrierAttempt
      ≡
      true

    rationalMatterJarlskogTheoremStillFalse :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.matterMixingMatrixJarlskogNonzeroPromoted
        rationalOneFifthCarrierAttempt
      ≡
      false

    rationalExactProductClosureStillFalse :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.exactCKMProductClosureWitnessSupplied
        rationalOneFifthCarrierAttempt
      ≡
      false

    hardBlockerExactRationalCKMStillFalse :
      Gate7Field.exactRationalEpsilonClosureProved
        (Gate7CKM.lower6ExactCKMEntryFieldBlocker exactCKMHardBlocker)
      ≡
      false

    hardBlockerExactJarlskogStillFalse :
      Gate7CKM.lower6ExactJarlskogTheoremPromoted exactCKMHardBlocker
      ≡
      false

    hardBlockerCarrierMixingStillFalse :
      Gate7CKM.lower6ExactCarrierMixingTheoremPromoted exactCKMHardBlocker
      ≡
      false

    terminalClaimPromotedExpression :
      Bool

    terminalClaimPromotedExpressionIsAfterBlockerConjunction :
      terminalClaimPromotedExpression
      ≡
      lower6TerminalClaimPromotionExpression
        (Lower6CKMTerminalAuthorityWaveLedger.gDHREqualsGSMPromoted
          terminalAuthorityLedger)
        (Lower6CKMTerminalAuthorityWaveLedger.tYMEqualsTGRPromoted
          terminalAuthorityLedger)
        (Lower6CKMTerminalAuthorityWaveLedger.dhrYukawaMatchPromoted
          terminalAuthorityLedger)
        (Lower6CKMTerminalAuthorityWaveLedger.stoneSpectrumGapMatchPromoted
          terminalAuthorityLedger)
        (Gate7Field.exactRationalEpsilonClosureProved
          (Gate7CKM.lower6ExactCKMEntryFieldBlocker exactCKMHardBlocker))
        (Gate7CKM.lower6ExactJarlskogTheoremPromoted exactCKMHardBlocker)
        (Gate7CKM.lower6ExactCarrierMixingTheoremPromoted exactCKMHardBlocker)
        (Lower6CKMTerminalAuthorityWaveLedger.continuumClayMassGapPromoted
          terminalAuthorityLedger)

    terminalClaimPromotedExpressionIsFalse :
      terminalClaimPromotedExpression ≡ false

    terminalClaimPromotedExpressionMatchesTerminalMap :
      terminalClaimPromotedExpression
      ≡
      Lower6ExactRationalCKMTerminalDependencyMap.terminalClaimPromoted
        terminalDependencyMapReceipt

    rationalOneFifthMovesBeyondLower6HardBlocker :
      Bool

    rationalOneFifthMovesBeyondLower6HardBlockerIsFalse :
      rationalOneFifthMovesBeyondLower6HardBlocker ≡ false

    afterBlockerConditionalBoundary :
      List String

open Lower6AfterBlockerTerminalConditionalDependencyReceipt public

canonicalLower6AfterBlockerTerminalConditionalDependencyReceipt :
  Lower6AfterBlockerTerminalConditionalDependencyReceipt
canonicalLower6AfterBlockerTerminalConditionalDependencyReceipt =
  record
    { terminalDependencyMapReceipt =
        canonicalLower6ExactRationalCKMTerminalDependencyMap
    ; terminalAuthorityLedger =
        canonicalLower6CKMTerminalAuthorityWaveLedger
    ; exactCKMHardBlocker =
        Gate7CKM.canonicalCKMLower6ExactCKMJarlskogHardBlockerReceipt
    ; rationalOneFifthSpectralAttempt =
        Gate7Field.canonicalCKMRationalOneFifthSpectralAttemptReceipt
    ; rationalOneFifthCarrierAttempt =
        Gate7CKM.canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
    ; afterBlockerCrossGateSurfacesAlreadyCanonical =
        refl
    ; exactRationalTerminalDependenciesAlreadyCanonical =
        refl
    ; rationalSpectralSplittingStillFalse =
        refl
    ; rationalSpectralPromotionStillFalse =
        refl
    ; rationalLeadingJarlskogBookkeepingTrue =
        refl
    ; rationalMatterJarlskogTheoremStillFalse =
        refl
    ; rationalExactProductClosureStillFalse =
        refl
    ; hardBlockerExactRationalCKMStillFalse =
        refl
    ; hardBlockerExactJarlskogStillFalse =
        refl
    ; hardBlockerCarrierMixingStillFalse =
        refl
    ; terminalClaimPromotedExpression =
        false
    ; terminalClaimPromotedExpressionIsAfterBlockerConjunction =
        refl
    ; terminalClaimPromotedExpressionIsFalse =
        refl
    ; terminalClaimPromotedExpressionMatchesTerminalMap =
        refl
    ; rationalOneFifthMovesBeyondLower6HardBlocker =
        false
    ; rationalOneFifthMovesBeyondLower6HardBlockerIsFalse =
        refl
    ; afterBlockerConditionalBoundary =
        "The after-blocker terminal obligations are already captured by the canonical Gate 8 cross-gate surfaces: G_DHR ~= G_SM, T_YM = T_GR, DHR/Yukawa match, and Stone spectrum versus YM gap"
        ∷ "The terminalClaimPromoted expression is the conjunction of those existing surfaces with exact rational CKM closure, exact Jarlskog, carrier mixing, and Clay mass-gap promotion"
        ∷ "Every factor in the current canonical receipt is still false at the promotion level, so terminalClaimPromoted remains false"
        ∷ "epsilon = 1/5 supplies only rational leading bookkeeping and a leading Jarlskog nonzero receipt; it does not pass the exact lower6 CKM/Jarlskog hard blocker"
        ∷ []
    }

lower6AfterBlockerConditionalKeepsTerminalFalse :
  terminalClaimPromotedExpression
    canonicalLower6AfterBlockerTerminalConditionalDependencyReceipt
  ≡
  false
lower6AfterBlockerConditionalKeepsTerminalFalse =
  refl

lower6RationalOneFifthDoesNotMoveBeyondHardBlocker :
  rationalOneFifthMovesBeyondLower6HardBlocker
    canonicalLower6AfterBlockerTerminalConditionalDependencyReceipt
  ≡
  false
lower6RationalOneFifthDoesNotMoveBeyondHardBlocker =
  refl

------------------------------------------------------------------------
-- Middle6 current-wave ledger stub.
--
-- This is the no-new-import integration point for the next middle6 receipt
-- wave.  It consumes the canonical ledgers already in this module and leaves
-- later worker receipts as named slots until their surfaces land.

data Middle6CurrentWaveLedgerStubStatus : Set where
  middle6CurrentWaveLedgerStubPreparedNoPromotion :
    Middle6CurrentWaveLedgerStubStatus

data Middle6CurrentWaveReceiptSlot : Set where
  gate2CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  gate3CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  gate4CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  gate5CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  gate6Gate1CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  gate7CurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

  terminalCurrentWaveReceiptSlot :
    Middle6CurrentWaveReceiptSlot

canonicalMiddle6CurrentWaveReceiptSlots :
  List Middle6CurrentWaveReceiptSlot
canonicalMiddle6CurrentWaveReceiptSlots =
  gate2CurrentWaveReceiptSlot
  ∷ gate3CurrentWaveReceiptSlot
  ∷ gate4CurrentWaveReceiptSlot
  ∷ gate5CurrentWaveReceiptSlot
  ∷ gate6Gate1CurrentWaveReceiptSlot
  ∷ gate7CurrentWaveReceiptSlot
  ∷ terminalCurrentWaveReceiptSlot
  ∷ []

record Middle6CurrentWaveLedgerStub : Setω₁ where
  field
    status :
      Middle6CurrentWaveLedgerStubStatus

    currentAssignedCompletionLedger :
      Bool

    currentAssignedCompletionLedgerKeepsTerminalFalse :
      Bool

    currentLower6CKMTerminalLedger :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger

    currentLower6CKMTerminalLedgerKeepsTerminalFalse :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.terminalClaimPromoted
        currentLower6CKMTerminalLedger
      ≡
      false

    currentLower6CKMTerminalLedgerKeepsClayFalse :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.continuumClayMassGapPromoted
        currentLower6CKMTerminalLedger
      ≡
      false

    consumableReceiptSlots :
      List Middle6CurrentWaveReceiptSlot

    consumableReceiptSlotsAreCanonical :
      consumableReceiptSlots
      ≡
      canonicalMiddle6CurrentWaveReceiptSlots

    futureWorkerReceiptsImported :
      Bool

    futureWorkerReceiptsImportedIsFalse :
      futureWorkerReceiptsImported ≡ false

    addedBreakingImports :
      Bool

    addedBreakingImportsIsFalse :
      addedBreakingImports ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    stubBoundary :
      List String

open Middle6CurrentWaveLedgerStub public

canonicalMiddle6CurrentWaveLedgerStub :
  Middle6CurrentWaveLedgerStub
canonicalMiddle6CurrentWaveLedgerStub =
  record
    { status =
        middle6CurrentWaveLedgerStubPreparedNoPromotion
    ; currentAssignedCompletionLedger =
        true
    ; currentAssignedCompletionLedgerKeepsTerminalFalse =
        true
    ; currentLower6CKMTerminalLedger =
        canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; currentLower6CKMTerminalLedgerKeepsTerminalFalse =
        refl
    ; currentLower6CKMTerminalLedgerKeepsClayFalse =
        refl
    ; consumableReceiptSlots =
        canonicalMiddle6CurrentWaveReceiptSlots
    ; consumableReceiptSlotsAreCanonical =
        refl
    ; futureWorkerReceiptsImported =
        false
    ; futureWorkerReceiptsImportedIsFalse =
        refl
    ; addedBreakingImports =
        false
    ; addedBreakingImportsIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; stubBoundary =
        "Middle6 current-wave stub consumes only canonical ledgers already imported in this module"
        ∷ "The assigned-completion ledger and lower6 current CKM terminal ledger are reusable inputs"
        ∷ "Gate 2, Gate 3, Gate 4, Gate 5, Gate 6/Gate 1, Gate 7, and terminal worker receipts have named slots"
        ∷ "Future worker receipts can replace stub slots after their canonical surfaces land"
        ∷ "No new import is added for absent worker receipts"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

middle6CurrentWaveLedgerStubKeepsTerminalFalse :
  Middle6CurrentWaveLedgerStub.terminalClaimPromoted
    canonicalMiddle6CurrentWaveLedgerStub
  ≡
  false
middle6CurrentWaveLedgerStubKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Middle6 latest assigned proof-attempt integration ledger.
--
-- This consumes the concrete receipts returned by the latest assigned worker
-- wave.  Each lane completed its assigned local attempt and either inhabited
-- the finite/bookkeeping surface or recorded the exact missing constructor.
-- No global theorem or authority token is promoted here.

data Middle6LatestAssignedProofAttemptStatus : Set where
  middle6LatestAssignedProofAttemptsIntegratedFailClosed :
    Middle6LatestAssignedProofAttemptStatus

record Middle6LatestAssignedProofAttemptLedger : Setω₁ where
  field
    status :
      Middle6LatestAssignedProofAttemptStatus

    ledgerStub :
      Bool

    gate3LatestFirstMissingAttempt :
      Gate3Obs.YMSFGCLatestFirstMissingConcreteAttemptReceipt

    gate3LatestStrictCurvatureStillMissing :
      Gate3Obs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.strictNonFlatCurvatureBlocker
        gate3LatestFirstMissingAttempt
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    gate3LatestStrictPromotionFalse :
      Gate3Obs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.strictPromotion
        gate3LatestFirstMissingAttempt
      ≡
      false

    gate4DoubledChristoffelAttempt :
      Gate4Scalar.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt

    gate4DoubledRouteStagedTrue :
      Gate4Scalar.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.localDoubledMetricCompatibilityStaged
        gate4DoubledChristoffelAttempt
      ≡
      true

    gate4MissingMetricCompatibilityStillFalse :
      Gate4Scalar.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.missingMetricCompatibilityClosed
        gate4DoubledChristoffelAttempt
      ≡
      true

    gate4LeviCivitaStillFalse :
      Gate4Scalar.GRLatestWaveDoubledChristoffelMetricCompatibilityReceipt.missingCarrierConnectionIsLeviCivitaClosed
        gate4DoubledChristoffelAttempt
      ≡
      true

    gate5LocalAlgebraClosureAttempt :
      AQFTQuotient.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt

    gate5AQFTSpacelikeCurrentWaveAttempt :
      AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt

    gate5SpacelikeCommutativityStillFalse :
      AQFTQuotient.AQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt.spacelikeCommutativityProved
        gate5AQFTSpacelikeCurrentWaveAttempt
      ≡
      false

    gate5DASHILocalAlgebraStillFalse :
      AQFTQuotient.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt.missingDASHILocalAlgebraInhabited
        gate5LocalAlgebraClosureAttempt
      ≡
      true

    gate5ClosurePromotedFalse :
      AQFTQuotient.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt.closurePromoted
        gate5LocalAlgebraClosureAttempt
      ≡
      true

    gate6IdentityActionInspection :
      Gate6DHR.DHRUpper6EndomorphismActionReplacementInspectionReceipt

    gate6IdentityActionConstructorStillFalse :
      Gate6DHR.DHRUpper6EndomorphismActionReplacementInspectionReceipt.identityActionConstructorProvided
        gate6IdentityActionInspection
      ≡
      false

    gate6ArbitrarySectorIdentityStillFalse :
      Gate6DHR.DHRUpper6EndomorphismActionReplacementInspectionReceipt.arbitrarySectorIdentityEndomorphismConstructed
        gate6IdentityActionInspection
      ≡
      false

    gate6DRSMStillFalse :
      Gate6DHR.DHRUpper6EndomorphismActionReplacementInspectionReceipt.drReconstructionOrSMMatchPromoted
        gate6IdentityActionInspection
      ≡
      false

    gate7RationalOneFifthAttempt :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt

    gate7LeadingJarlskogBookkeepingTrue :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.leadingJarlskogNonzeroReceiptSupplied
        gate7RationalOneFifthAttempt
      ≡
      true

    gate7ExactProductClosureStillFalse :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.exactCKMProductClosureWitnessSupplied
        gate7RationalOneFifthAttempt
      ≡
      false

    gate7CarrierMixingStillFalse :
      Gate7CKM.CKMRationalOneFifthLeadingCarrierAttemptReceipt.carrierMixingTheoremPromoted
        gate7RationalOneFifthAttempt
      ≡
      false

    authorityClayCheckedCurrent :
      Bool

    authorityClayCheckedCurrentIsTrue :
      authorityClayCheckedCurrent ≡ true

    authorityPDGVEVCheckedCurrent :
      Bool

    authorityPDGVEVCheckedCurrentIsTrue :
      authorityPDGVEVCheckedCurrent ≡ true

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    latestAttemptBoundary :
      List String

open Middle6LatestAssignedProofAttemptLedger public

canonicalMiddle6LatestAssignedProofAttemptLedger :
  Middle6LatestAssignedProofAttemptLedger
canonicalMiddle6LatestAssignedProofAttemptLedger =
  record
    { status =
        middle6LatestAssignedProofAttemptsIntegratedFailClosed
    ; ledgerStub =
        true
    ; gate3LatestFirstMissingAttempt =
        Gate3Obs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; gate3LatestStrictCurvatureStillMissing =
        refl
    ; gate3LatestStrictPromotionFalse =
        refl
    ; gate4DoubledChristoffelAttempt =
        Gate4Scalar.canonicalGRLatestWaveDoubledChristoffelMetricCompatibilityReceipt
    ; gate4DoubledRouteStagedTrue =
        refl
    ; gate4MissingMetricCompatibilityStillFalse =
        Gate4Scalar.grLatestWaveMissingMetricCompatibilityNowClosed
    ; gate4LeviCivitaStillFalse =
        Gate4Scalar.grLatestWaveMissingCarrierConnectionIsLeviCivitaNowClosed
    ; gate5LocalAlgebraClosureAttempt =
        AQFTQuotient.canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt
    ; gate5AQFTSpacelikeCurrentWaveAttempt =
        AQFTQuotient.canonicalAQFTL5QuotientOperationsSpacelikeCommutativityAttemptReceipt
    ; gate5SpacelikeCommutativityStillFalse =
        refl
    ; gate5DASHILocalAlgebraStillFalse =
        refl
    ; gate5ClosurePromotedFalse =
        refl
    ; gate6IdentityActionInspection =
        Gate6DHR.canonicalDHRUpper6EndomorphismActionReplacementInspectionReceipt
    ; gate6IdentityActionConstructorStillFalse =
        refl
    ; gate6ArbitrarySectorIdentityStillFalse =
        refl
    ; gate6DRSMStillFalse =
        refl
    ; gate7RationalOneFifthAttempt =
        Gate7CKM.canonicalCKMRationalOneFifthLeadingCarrierAttemptReceipt
    ; gate7LeadingJarlskogBookkeepingTrue =
        refl
    ; gate7ExactProductClosureStillFalse =
        refl
    ; gate7CarrierMixingStillFalse =
        refl
    ; authorityClayCheckedCurrent =
        true
    ; authorityClayCheckedCurrentIsTrue =
        refl
    ; authorityPDGVEVCheckedCurrent =
        true
    ; authorityPDGVEVCheckedCurrentIsTrue =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; latestAttemptBoundary =
        "Gate 3 finite SU2-like/Wilson-loop and Hodge handoff terms landed, but strict YMSFGCUserSuppliedNonFlatConnectionCarrier and connectionCurvature constructors are still absent"
        ∷ "Gate 4 doubled-Christoffel arithmetic landed, but the selected non-flat Levi-Civita path still stops at the r1 half obstruction"
        ∷ "Gate 5 quotient/GNS/local-algebra closure attempt landed, but C-star completion constructors, local operator constructors, causal BFS path absence, and missingDASHILocalAlgebra remain open"
        ∷ "Gate 6 identity-action replacement was inspected and rejected as semantically breaking while EndomorphismAction remains a bare postulated Set"
        ∷ "Gate 7 rational epsilon = 1/5 bookkeeping landed with leading Jarlskog data, but exact CKM product closure, normalized eigenbases, and carrier mixing theorem remain open"
        ∷ "Authority sidecar checked on 2026-05-21: Clay Yang-Mills remains unsolved; PDG 2024 records v = 246.22 GeV as a reference value only"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

middle6LatestAssignedProofAttemptKeepsTerminalFalse :
  Middle6LatestAssignedProofAttemptLedger.terminalClaimPromoted
    canonicalMiddle6LatestAssignedProofAttemptLedger
  ≡
  false
middle6LatestAssignedProofAttemptKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Post-terminal layer integration ledger.
--
-- This ledger consumes the canonical receipts that landed after the terminal
-- proof-attempt ledger.  It records the extra finite/internal and authority-
-- scoping layers as fail-closed intake only; terminal promotion stays false.

data PostTerminalIntegrationLayer : Set where
  postTerminalFiniteYMSpectralGapLayer :
    PostTerminalIntegrationLayer

  postTerminalGate3InstantiationDecisionLayer :
    PostTerminalIntegrationLayer

  postTerminalStressEnergyW4ScopeLayer :
    PostTerminalIntegrationLayer

  postTerminalSelectedMetricAPIRefactorLayer :
    PostTerminalIntegrationLayer

  postTerminalFiniteStoneYMSpectralBridgeLayer :
    PostTerminalIntegrationLayer

  postTerminalDoplicherRobertsScopingLayer :
    PostTerminalIntegrationLayer

canonicalPostTerminalIntegrationLayers :
  List PostTerminalIntegrationLayer
canonicalPostTerminalIntegrationLayers =
  postTerminalFiniteYMSpectralGapLayer
  ∷ postTerminalGate3InstantiationDecisionLayer
  ∷ postTerminalStressEnergyW4ScopeLayer
  ∷ postTerminalSelectedMetricAPIRefactorLayer
  ∷ postTerminalFiniteStoneYMSpectralBridgeLayer
  ∷ postTerminalDoplicherRobertsScopingLayer
  ∷ []

data PostTerminalLayerIntegrationStatus : Set where
  postTerminalLayersIntegratedFailClosed :
    PostTerminalLayerIntegrationStatus

record PostTerminalLayerIntegrationLedger : Setω₁ where
  field
    status :
      PostTerminalLayerIntegrationStatus

    priorTerminalLedger :
      Bool

    priorTerminalLedgerKeepsTerminalFalse :
      Bool

    consumedLayers :
      List PostTerminalIntegrationLayer

    consumedLayersAreCanonical :
      consumedLayers
      ≡
      canonicalPostTerminalIntegrationLayers

    gate2FiniteSpectralInternalLayer :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt

    gate2FiniteLayerClayStillFalse :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt.continuumClayMassGapPromoted
        gate2FiniteSpectralInternalLayer
      ≡
      false

    gate2FiniteLayerTerminalStillFalse :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt.terminalClaimPromoted
        gate2FiniteSpectralInternalLayer
      ≡
      false

    gate3LatestInstantiationDecision :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt

    gate3LatestConsumeM1StillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1Instantiated
        gate3LatestInstantiationDecision
      ≡
      false

    gate3LatestStrictSU3StillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.strictRealSU3Promoted
        gate3LatestInstantiationDecision
      ≡
      false

    gate3LatestHodgeVariationStillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.strictHodgeOrVariationPromoted
        gate3LatestInstantiationDecision
      ≡
      false

    gate4StressEnergyW4ScopeCorrection :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt

    gate4LocalTensorSeparated :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4
        gate4StressEnergyW4ScopeCorrection
      ≡
      true

    gate4W4PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesW4
        gate4StressEnergyW4ScopeCorrection
      ≡
      false

    gate4Candidate256PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesCandidate256
        gate4StressEnergyW4ScopeCorrection
      ≡
      false

    gate4SelectedMetricRefactorTarget :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt

    gate4SelectedMetricCompatibilityStillFalse :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedMetricCompatibilityPromoted
        gate4SelectedMetricRefactorTarget
      ≡
      true

    gate4LeviCivitaPromotionStillFalse :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedConnectionIsLeviCivitaPromoted
        gate4SelectedMetricRefactorTarget
      ≡
      false

    gate5FiniteStoneYMSpectralBridge :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt

    gate5FiniteStoneInequalityStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneGeneratorSpectralInequalityPromoted
        gate5FiniteStoneYMSpectralBridge
      ≡
      false

    gate5PhysicalStrongContinuityStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.bridgePhysicalStrongContinuityPromoted
        gate5FiniteStoneYMSpectralBridge
      ≡
      false

    gate5TerminalStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.terminalPromoted
        gate5FiniteStoneYMSpectralBridge
      ≡
      false

    gate6DRScopingCorrection :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt

    gate6DRLiteratureRecorded :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.literatureTheoremRecorded
        gate6DRScopingCorrection
      ≡
      true

    gate6LocalEvidenceStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.h1h5LocalEvidenceTermsSupplied
        gate6DRScopingCorrection
      ≡
      true

    gate6DRAuthorityConsumedStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumedHere
        gate6DRScopingCorrection
      ≡
      false

    gate6StandardModelMatchingStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.standardModelMatchingPromoted
        gate6DRScopingCorrection
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    postTerminalBoundary :
      List String

open PostTerminalLayerIntegrationLedger public

canonicalPostTerminalLayerIntegrationLedger :
  PostTerminalLayerIntegrationLedger
canonicalPostTerminalLayerIntegrationLedger =
  record
    { status =
        postTerminalLayersIntegratedFailClosed
    ; priorTerminalLedger =
        true
    ; priorTerminalLedgerKeepsTerminalFalse =
        true
    ; consumedLayers =
        canonicalPostTerminalIntegrationLayers
    ; consumedLayersAreCanonical =
        refl
    ; gate2FiniteSpectralInternalLayer =
        Gate2S8.canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
    ; gate2FiniteLayerClayStillFalse =
        refl
    ; gate2FiniteLayerTerminalStillFalse =
        refl
    ; gate3LatestInstantiationDecision =
        Gate3.canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; gate3LatestConsumeM1StillFalse =
        refl
    ; gate3LatestStrictSU3StillFalse =
        refl
    ; gate3LatestHodgeVariationStillFalse =
        refl
    ; gate4StressEnergyW4ScopeCorrection =
        W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; gate4LocalTensorSeparated =
        refl
    ; gate4W4PromotionStillFalse =
        refl
    ; gate4Candidate256PromotionStillFalse =
        refl
    ; gate4SelectedMetricRefactorTarget =
        Gate4GR.canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
    ; gate4SelectedMetricCompatibilityStillFalse =
        refl
    ; gate4LeviCivitaPromotionStillFalse =
        refl
    ; gate5FiniteStoneYMSpectralBridge =
        Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; gate5FiniteStoneInequalityStillFalse =
        refl
    ; gate5PhysicalStrongContinuityStillFalse =
        refl
    ; gate5TerminalStillFalse =
        refl
    ; gate6DRScopingCorrection =
        Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; gate6DRLiteratureRecorded =
        refl
    ; gate6LocalEvidenceStillFalse =
        refl
    ; gate6DRAuthorityConsumedStillFalse =
        refl
    ; gate6StandardModelMatchingStillFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; postTerminalBoundary =
        "Post-terminal integration consumes only canonical receipts already available in the imported closure/QFT modules"
        ∷ "Gate 2 records finite/internal spectral-gap progress but keeps real YM, UniformBalaban, Clay, and terminal promotion false"
        ∷ "Gate 3 records the latest u2 instantiation decision and keeps strict real SU3, selected Hodge, and variation promotion false"
        ∷ "Gate 4 records local tensor/W4 scoping plus selected-metric API refactor targets without W4, Candidate256, Levi-Civita, or sourced-Einstein promotion"
        ∷ "Gate 5 records a finite Stone/YM spectral bridge while the numeric inequality, physical strong continuity, and terminal promotion remain false"
        ∷ "Gate 6 records Doplicher-Roberts literature authority as scoped, not consumed; local H1-H5 evidence, DR reconstruction, and Standard Model matching remain false"
        ∷ "terminalClaimPromoted remains false"
        ∷ []
    }

postTerminalLayerIntegrationKeepsTerminalFalse :
  PostTerminalLayerIntegrationLedger.terminalClaimPromoted
    canonicalPostTerminalLayerIntegrationLedger
  ≡
  false
postTerminalLayerIntegrationKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Middle6 downstream-after-five-blockers integration.
--
-- The current wave assigns the theorems that would become reachable after
-- the five canonical blockers close.  The receipts below are intentionally
-- fail-closed: they wire the worker outputs into the terminal dependency map
-- but do not assert the downstream Gate 8 theorem obligations.

data Middle6DownstreamAfterFiveBlockersStatus : Set where
  downstreamReceiptsIntegratedNoTerminalPromotion :
    Middle6DownstreamAfterFiveBlockersStatus

record Middle6DownstreamAfterFiveBlockersLedger : Setω₁ where
  field
    status :
      Middle6DownstreamAfterFiveBlockersStatus

    previousPostTerminalLedger :
      PostTerminalLayerIntegrationLedger

    previousPostTerminalKeepsTerminalFalse :
      PostTerminalLayerIntegrationLedger.terminalClaimPromoted
        previousPostTerminalLedger
      ≡
      false

    gate2FriedrichsSelfAdjointAuthorityTarget :
      Gate2S8.U1Gate2FriedrichsSelfAdjointAuthorityReceipt

    gate2ContinuumSpectralTransportTarget :
      Gate2S8.U1Gate2ContinuumSpectralBoundTransportConditionalReceipt

    gate3HodgeVariationIBPTarget :
      Gate3Obs.YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    gate4SourcedEinsteinEquationTarget :
      Gate4Ricci.GRGate4SourcedEinsteinEquationSurface

    gate5TomitaTakesakiAuthorityTarget :
      Gate5Modular.Gate5TomitaPolarDecompositionAuthorityTargetReceipt

    gate5StonePhysicalHamiltonianTarget :
      Gate5.Gate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt

    gate6TensorStatisticsHexagonDRTarget :
      Gate6.DHRGate6DownstreamTensorStatisticsHexagonDRReceiptSurface

    gate7PhysicalYukawaDHRIntertwinerTarget :
      Gate7CKM.CKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt

    gate8GDHREqualsGSMInhabited :
      Bool

    gate8GDHREqualsGSMStillFalse :
      gate8GDHREqualsGSMInhabited ≡ false

    gate8TYMEqualsTGRInhabited :
      Bool

    gate8TYMEqualsTGRStillFalse :
      gate8TYMEqualsTGRInhabited ≡ false

    gate8DHRYukawaMatchInhabited :
      Bool

    gate8DHRYukawaMatchStillFalse :
      gate8DHRYukawaMatchInhabited ≡ false

    gate8StoneSpectrumYMGAPInhabited :
      Bool

    gate8StoneSpectrumYMGAPStillFalse :
      gate8StoneSpectrumYMGAPInhabited ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    integrationBoundary :
      List String

open Middle6DownstreamAfterFiveBlockersLedger public

canonicalMiddle6DownstreamAfterFiveBlockersLedger :
  Middle6DownstreamAfterFiveBlockersLedger
canonicalMiddle6DownstreamAfterFiveBlockersLedger =
  record
    { status =
        downstreamReceiptsIntegratedNoTerminalPromotion
    ; previousPostTerminalLedger =
        canonicalPostTerminalLayerIntegrationLedger
    ; previousPostTerminalKeepsTerminalFalse =
        refl
    ; gate2FriedrichsSelfAdjointAuthorityTarget =
        Gate2S8.canonicalU1Gate2FriedrichsSelfAdjointAuthorityReceipt
    ; gate2ContinuumSpectralTransportTarget =
        Gate2S8.canonicalU1Gate2ContinuumSpectralBoundTransportConditionalReceipt
    ; gate3HodgeVariationIBPTarget =
        Gate3Obs.canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; gate4SourcedEinsteinEquationTarget =
        Gate4Ricci.canonicalGRGate4SourcedEinsteinEquationSurface
    ; gate5TomitaTakesakiAuthorityTarget =
        Gate5Modular.canonicalGate5TomitaPolarDecompositionAuthorityTargetReceipt
    ; gate5StonePhysicalHamiltonianTarget =
        Gate5.canonicalGate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt
    ; gate6TensorStatisticsHexagonDRTarget =
        Gate6.canonicalDHRGate6DownstreamTensorStatisticsHexagonDRReceiptSurface
    ; gate7PhysicalYukawaDHRIntertwinerTarget =
        Gate7CKM.canonicalCKMGate7PhysicalYukawaDHRIntertwinerSurfaceReceipt
    ; gate8GDHREqualsGSMInhabited =
        false
    ; gate8GDHREqualsGSMStillFalse =
        refl
    ; gate8TYMEqualsTGRInhabited =
        false
    ; gate8TYMEqualsTGRStillFalse =
        refl
    ; gate8DHRYukawaMatchInhabited =
        false
    ; gate8DHRYukawaMatchStillFalse =
        refl
    ; gate8StoneSpectrumYMGAPInhabited =
        false
    ; gate8StoneSpectrumYMGAPStillFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; integrationBoundary =
        "Gate 2 downstream records Friedrichs/self-adjoint and continuum spectral-transport targets, but the real YM Hamiltonian and Clay/UniformBalaban promotion remain uninhabited"
        ∷ "Gate 3 downstream records Hodge variation and SFGC integration-by-parts targets, but selected non-flat curvature and variation pairing promotion remain blocked"
        ∷ "Gate 4 downstream records the sourced Einstein equation surface, but selected Levi-Civita metric compatibility, W4 matter authority, and sourced equation promotion remain false"
        ∷ "Gate 5 downstream records Tomita-Takesaki and Stone physical-Hamiltonian target surfaces, but GNS/strong-continuity/global phase-space promotion remains false"
        ∷ "Gate 6 downstream records tensor product, statistics, hexagon, and DR reconstruction targets, but local algebra semantics, H1-H5 evidence, DR consumption, and G_DHR construction remain false"
        ∷ "Gate 7 downstream records physical Yukawa/DHR intertwiner targets, but physical masses, exact DHR/Yukawa compatibility, and vHiggs physical promotion remain false"
        ∷ "The four Gate 8 theorem obligations remain uninhabited and terminalClaimPromoted remains false"
        ∷ []
    }

middle6DownstreamAfterFiveBlockersKeepsTerminalFalse :
  Middle6DownstreamAfterFiveBlockersLedger.terminalClaimPromoted
    canonicalMiddle6DownstreamAfterFiveBlockersLedger
  ≡
  false
middle6DownstreamAfterFiveBlockersKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Middle6 first-missing hard-math iteration integration.
--
-- This wave attacks the stable first-missing mathematical terms directly.
-- Every worker return is integrated below as a typed dependency receipt, not
-- as a promotion of the corresponding theorem.

data Middle6FirstMissingHardMathIterationStatus : Set where
  firstMissingHardMathReceiptsIntegratedNoPromotion :
    Middle6FirstMissingHardMathIterationStatus

record Middle6FirstMissingHardMathIterationLedger : Setω₁ where
  field
    status :
      Middle6FirstMissingHardMathIterationStatus

    previousDownstreamLedger :
      Bool

    previousDownstreamKeepsTerminalFalse :
      Bool

    gate2FiniteCasimirGapOneReceipt :
      Gate2S8.U1FiniteCasimirGapOneCanonicalModeReceipt

    gate2FiniteCasimirGapOneValue :
      Gate2S8.U1FiniteCasimirGapOneCanonicalModeReceipt.u1FiniteCasimirGapValue
        gate2FiniteCasimirGapOneReceipt
      ≡
      1

    gate3StrictNonFlatCurvatureTypeMismatch :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt

    gate3StrictNonFlatCurvatureStillFalse :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.strictNonFlatCurvatureClosed
        gate3StrictNonFlatCurvatureTypeMismatch
      ≡
      true

    gate4DoubledChristoffelInput :
      Gate4GR.GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    gate4FourRTwoGEinsteinReceipt :
      Gate4GR.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt

    gate5ScopedCStarAuthority :
      AQFTQuotient.L5ScopedCStarCompletionAuthorityReceipt

    gate5GNSInnerProductWellDefinednessTarget :
      Gate5Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt

    gate5GNSQuotientDescentReceipt :
      Gate5GNS.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt

    gate6IdentityActionSemanticAdapter :
      Bool

    gate6TensorDualSemanticAdapterIntegration :
      Gate6.DHRTensorDualIdentityActionSemanticAdapterIntegrationReceipt

    gate7GaussianRationalCPPhaseReceipt :
      Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt

    gate7CarrierMixingStillFalse :
      Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt.carrierMixingTheoremPromotedFromGaussianReceipt
        gate7GaussianRationalCPPhaseReceipt
      ≡
      true

    selectedNonFlatCurvaturePromoted :
      Bool

    selectedNonFlatCurvaturePromotedIsFalse :
      selectedNonFlatCurvaturePromoted ≡ false

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsFalse :
      selectedMetricCompatibilityPromoted ≡ false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    dhrReconstructionPromoted :
      Bool

    dhrReconstructionPromotedIsFalse :
      dhrReconstructionPromoted ≡ false

    exactCKMCarrierMixingPromoted :
      Bool

    exactCKMCarrierMixingPromotedIsFalse :
      exactCKMCarrierMixingPromoted ≡ false

    finiteYMSpectrumPromoted :
      Bool

    finiteYMSpectrumPromotedIsFalse :
      finiteYMSpectrumPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    integrationBoundary :
      List String

open Middle6FirstMissingHardMathIterationLedger public

canonicalMiddle6FirstMissingHardMathIterationLedger :
  Middle6FirstMissingHardMathIterationLedger
canonicalMiddle6FirstMissingHardMathIterationLedger =
  record
    { status =
        firstMissingHardMathReceiptsIntegratedNoPromotion
    ; previousDownstreamLedger =
        true
    ; previousDownstreamKeepsTerminalFalse =
        true
    ; gate2FiniteCasimirGapOneReceipt =
        Gate2S8.canonicalU1FiniteCasimirGapOneCanonicalModeReceipt
    ; gate2FiniteCasimirGapOneValue =
        Gate2S8.u1FiniteCasimirGapOneValueIsOne
    ; gate3StrictNonFlatCurvatureTypeMismatch =
        Gate3Obs.canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
    ; gate3StrictNonFlatCurvatureStillFalse =
        Gate3Obs.yangMillsMiddle6StrictNonFlatCurvatureStillFailClosed
    ; gate4DoubledChristoffelInput =
        Gate4GR.canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; gate4FourRTwoGEinsteinReceipt =
        Gate4GR.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; gate5ScopedCStarAuthority =
        AQFTQuotient.canonicalL5ScopedCStarCompletionAuthorityReceipt
    ; gate5GNSInnerProductWellDefinednessTarget =
        Gate5Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; gate5GNSQuotientDescentReceipt =
        Gate5GNS.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gate6IdentityActionSemanticAdapter =
        true
    ; gate6TensorDualSemanticAdapterIntegration =
        Gate6.canonicalDHRTensorDualIdentityActionSemanticAdapterIntegrationReceipt
    ; gate7GaussianRationalCPPhaseReceipt =
        Gate7CKM.canonicalCKMGaussianRationalCPPhaseProgressReceipt
    ; gate7CarrierMixingStillFalse =
        Gate7CKM.ckmGaussianRationalCPPhaseKeepsCarrierMixingUnpromoted
    ; selectedNonFlatCurvaturePromoted =
        false
    ; selectedNonFlatCurvaturePromotedIsFalse =
        refl
    ; selectedMetricCompatibilityPromoted =
        false
    ; selectedMetricCompatibilityPromotedIsFalse =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; dhrReconstructionPromoted =
        false
    ; dhrReconstructionPromotedIsFalse =
        refl
    ; exactCKMCarrierMixingPromoted =
        false
    ; exactCKMCarrierMixingPromotedIsFalse =
        refl
    ; finiteYMSpectrumPromoted =
        false
    ; finiteYMSpectrumPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; integrationBoundary =
        "Gate 2 now records canonical finite Casimir modes with gapValue = 1, but the finite H_YM spectrum and Casimir-domination API are still absent"
        ∷ "Gate 3 now isolates the exact type mismatch: the finite SFGC non-flat 2-form cannot coerce into YMSFGCUserSuppliedNonFlatConnectionCarrier without a finite-1-form-to-user-connection bridge"
        ∷ "Gate 4 now has a Christoffel-aware doubled-2Gamma input and finite 4R/Ricci/scalar/2G zero-table receipt, but selectedMetricCompatibility still uses the old r1 path"
        ∷ "Gate 5 now threads scoped C-star authority, quotient norm transport, and GNS inner-product descent targets, but Cauchy-Schwarz for parametric pre-C-star states and missingDASHILocalAlgebra remain open"
        ∷ "Gate 6 now records the identity-action semantic adapter target; arbitrary-sector identity still needs DASHI local-algebra action semantics before DR can be consumed"
        ∷ "Gate 7 now records Q[i] CP-phase bookkeeping and leading Jarlskog denominator 46875, but exact normalized U_u/U_d and exact CKM product over Q[i] remain missing"
        ∷ "No terminal, Clay, W4/Candidate256, Doplicher-Roberts, Standard Model, physical Yukawa, or continuum mass-gap promotion is introduced"
        ∷ []
    }

middle6FirstMissingHardMathIterationKeepsTerminalFalse :
  Middle6FirstMissingHardMathIterationLedger.terminalClaimPromoted
    canonicalMiddle6FirstMissingHardMathIterationLedger
  ≡
  false
middle6FirstMissingHardMathIterationKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Middle6 Schrödinger-clock hard-blocker iteration integration.
--
-- This wave keeps the repo frontier and the temporal-superposition/local
-- fibre observation aligned: global contractions are delayed to local fibre
-- boundaries, while the five hard mathematical blockers remain fail-closed
-- unless their actual inhabitants are present.

data Middle6SchrodingerClockHardBlockerIterationStatus : Set where
  schrodingerClockHardBlockerReceiptsIntegratedNoPromotion :
    Middle6SchrodingerClockHardBlockerIterationStatus

record Middle6SchrodingerClockHardBlockerIterationLedger : Setω₁ where
  field
    status :
      Middle6SchrodingerClockHardBlockerIterationStatus

    previousFirstMissingLedger :
      Bool

    previousFirstMissingKeepsTerminalFalse :
      Bool

    gate3StrictNonFlatBridgeProgress :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt

    gate3StrictNonFlatBridgeStillFalse :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatBridgeProgressReceipt.strictBridgePromoted
        gate3StrictNonFlatBridgeProgress
      ≡
      false

    gate4SelectedMetricDoubledInputAdapter :
      Gate4GR.GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt

    gate4LocalFibreRicciContraction :
      Gate4Ricci.GRDiscreteRicciGate4LocalFibreContractionReceipt

    gate4GlobalEagerRicciSweepStillFalse :
      Gate4Ricci.GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
        Gate4Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
      ≡
      false

    gate5ScopedUniversalArrowConsumption :
      AQFTQuotient.L5ScopedCStarCompletionUniversalArrowConsumptionReceipt

    gate5FiniteTraceStateCauchySchwarzDescent :
      Gate5Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt

    gate5FiniteTraceStateCauchySchwarzStillFalse :
      Gate5Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt.traceStateCauchySchwarzProved
        gate5FiniteTraceStateCauchySchwarzDescent
      ≡
      false

    gate5GNSFiniteTraceStateDescentConsumption :
      Gate5GNS.GNSFellFiniteTraceStateDescentConsumptionReceipt

    gate6AlgebraIndexedIdentityActionAdapter :
      Bool

    gate6TensorDualAlgebraIndexedAdapter :
      Gate6.DHRTensorDualAlgebraIndexedIdentityActionAdapterReceipt

    gate6TensorProductStillFalse :
      Gate6.DHRTensorDualAlgebraIndexedIdentityActionAdapterReceipt.tensorProductLawProved
        gate6TensorDualAlgebraIndexedAdapter
      ≡
      false

    gate7ConcreteWolfensteinProductClosure :
      Gate7Field.CKMConcreteWolfensteinProductClosureReceipt

    gate7ExactMatterMixingProductStillFalse :
      Gate7Field.CKMConcreteWolfensteinProductClosureReceipt.exactMatterMixingMatrixProductClosurePromoted
        gate7ConcreteWolfensteinProductClosure
      ≡
      false

    gate7Lower6JarlskogBookkeeping :
      Gate7CKM.CKMLower6JarlskogNonzeroBookkeepingReceipt

    selectedNonFlatCurvaturePromoted :
      Bool

    selectedNonFlatCurvaturePromotedIsFalse :
      selectedNonFlatCurvaturePromoted ≡ false

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsFalse :
      selectedMetricCompatibilityPromoted ≡ false

    dashiLocalAlgebraPromoted :
      Bool

    dashiLocalAlgebraPromotedIsFalse :
      dashiLocalAlgebraPromoted ≡ false

    dhrReconstructionPromoted :
      Bool

    dhrReconstructionPromotedIsFalse :
      dhrReconstructionPromoted ≡ false

    exactCKMCarrierMixingPromoted :
      Bool

    exactCKMCarrierMixingPromotedIsFalse :
      exactCKMCarrierMixingPromoted ≡ false

    tYMEqualsTGRPromoted :
      Bool

    tYMEqualsTGRPromotedIsFalse :
      tYMEqualsTGRPromoted ≡ false

    stoneSpectrumDominatesYMGapPromoted :
      Bool

    stoneSpectrumDominatesYMGapPromotedIsFalse :
      stoneSpectrumDominatesYMGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    integrationBoundary :
      List String

open Middle6SchrodingerClockHardBlockerIterationLedger public

canonicalMiddle6SchrodingerClockHardBlockerIterationLedger :
  Middle6SchrodingerClockHardBlockerIterationLedger
canonicalMiddle6SchrodingerClockHardBlockerIterationLedger =
  record
    { status =
        schrodingerClockHardBlockerReceiptsIntegratedNoPromotion
    ; previousFirstMissingLedger =
        true
    ; previousFirstMissingKeepsTerminalFalse =
        true
    ; gate3StrictNonFlatBridgeProgress =
        Gate3Obs.canonicalYMSFGCMiddle6StrictNonFlatBridgeProgressReceipt
    ; gate3StrictNonFlatBridgeStillFalse =
        Gate3Obs.yangMillsMiddle6StrictNonFlatBridgeProgressStillFailClosed
    ; gate4SelectedMetricDoubledInputAdapter =
        Gate4GR.canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
    ; gate4LocalFibreRicciContraction =
        Gate4Ricci.canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; gate4GlobalEagerRicciSweepStillFalse =
        Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.ricciCandidateNoGlobalEagerSweep
          Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; gate5ScopedUniversalArrowConsumption =
        AQFTQuotient.canonicalL5ScopedCStarCompletionUniversalArrowConsumptionReceipt
    ; gate5FiniteTraceStateCauchySchwarzDescent =
        Gate5Modular.canonicalM4FiniteTraceStateCauchySchwarzDescentReceipt
    ; gate5FiniteTraceStateCauchySchwarzStillFalse =
        Gate5Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt.traceStateCauchySchwarzProvedIsFalse
          Gate5Modular.canonicalM4FiniteTraceStateCauchySchwarzDescentReceipt
    ; gate5GNSFiniteTraceStateDescentConsumption =
        Gate5GNS.canonicalGNSFellFiniteTraceStateDescentConsumptionReceipt
    ; gate6AlgebraIndexedIdentityActionAdapter =
        true
    ; gate6TensorDualAlgebraIndexedAdapter =
        Gate6.canonicalDHRTensorDualAlgebraIndexedIdentityActionAdapterReceipt
    ; gate6TensorProductStillFalse =
        Gate6.DHRTensorDualAlgebraIndexedIdentityActionAdapterReceipt.tensorProductLawProvedIsFalse
          Gate6.canonicalDHRTensorDualAlgebraIndexedIdentityActionAdapterReceipt
    ; gate7ConcreteWolfensteinProductClosure =
        Gate7Field.canonicalCKMConcreteWolfensteinProductClosureReceipt
    ; gate7ExactMatterMixingProductStillFalse =
        Gate7Field.ckmConcreteWolfensteinProductClosureDoesNotPromoteExactProduct
    ; gate7Lower6JarlskogBookkeeping =
        Gate7CKM.canonicalCKMLower6JarlskogNonzeroBookkeepingReceipt
    ; selectedNonFlatCurvaturePromoted =
        false
    ; selectedNonFlatCurvaturePromotedIsFalse =
        refl
    ; selectedMetricCompatibilityPromoted =
        false
    ; selectedMetricCompatibilityPromotedIsFalse =
        refl
    ; dashiLocalAlgebraPromoted =
        false
    ; dashiLocalAlgebraPromotedIsFalse =
        refl
    ; dhrReconstructionPromoted =
        false
    ; dhrReconstructionPromotedIsFalse =
        refl
    ; exactCKMCarrierMixingPromoted =
        false
    ; exactCKMCarrierMixingPromotedIsFalse =
        refl
    ; tYMEqualsTGRPromoted =
        false
    ; tYMEqualsTGRPromotedIsFalse =
        refl
    ; stoneSpectrumDominatesYMGapPromoted =
        false
    ; stoneSpectrumDominatesYMGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; integrationBoundary =
        "Gate 3 now has an actual SFGCSite2DDiscrete1Form -> YMSFGCUserSuppliedNonFlatConnectionCarrier bridge and strict curvature projection, but the selected non-flat curvature theorem remains unpromoted pending holonomy transport laws"
        ∷ "Gate 4 records that the doubled-Christoffel adapter cannot by itself discharge the old selected r1 = r0 obligation, and the Ricci path is refactored through local fibres with no global eager sweep"
        ∷ "Gate 5 consumes the scoped C-star universal-arrow function shape and records finite trace-state Cauchy-Schwarz descent targets, while missingDASHILocalAlgebra and analytic Cauchy-Schwarz remain open"
        ∷ "Gate 6 threads algebra-indexed identity-action, tensor, and hexagon targets, but arbitrary-sector identity, tensor laws, DR reconstruction, and G_DHR remain false"
        ∷ "Gate 7 closes concrete truncated Wolfenstein product data over Q[i] to an O(epsilon^4) residual and records Jarlskog bookkeeping, while exact Matter.MixingMatrix unitarity/carrier mixing remains false"
        ∷ "No terminal, Clay, W4/Candidate256, Doplicher-Roberts, Standard Model, physical Yukawa, Stone-global, or continuum mass-gap promotion is introduced"
        ∷ []
    }

middle6SchrodingerClockHardBlockerIterationKeepsTerminalFalse :
  Middle6SchrodingerClockHardBlockerIterationLedger.terminalClaimPromoted
    canonicalMiddle6SchrodingerClockHardBlockerIterationLedger
  ≡
  false
middle6SchrodingerClockHardBlockerIterationKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- lower6 Gate 8 terminal monitor for the current fail-closed wave.
--
-- This tracker consumes the current canonical YM, GR, AQFT/DHR, and CKM/SM
-- receipts as evidence terms only.  Gate 8 promotion is the conjunction of
-- those four terms, so the canonical receipt stays false until every term is
-- inhabited by its upstream lane.

data Lower6Gate8CurrentWaveTerminalMonitorStatus : Set where
  lower6Gate8CurrentWaveReceiptsTrackedNoPromotion :
    Lower6Gate8CurrentWaveTerminalMonitorStatus

lower6Gate8TerminalPromotionRequiresFourEvidence :
  Bool → Bool → Bool → Bool → Bool
lower6Gate8TerminalPromotionRequiresFourEvidence
  ymEvidence
  grEvidence
  aqftDhrEvidence
  ckmSmEvidence =
  boolAnd ymEvidence
    (boolAnd grEvidence
      (boolAnd aqftDhrEvidence ckmSmEvidence))

record Lower6Gate8CurrentWaveTerminalMonitorReceipt : Setω₆ where
  field
    status :
      Lower6Gate8CurrentWaveTerminalMonitorStatus

    previousHardMathIteration :
      Bool

    previousHardMathIterationKeepsTerminalFalse :
      Bool

    ymFailClosedReceipt :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt

    ymEvidenceTermInhabited :
      Bool

    ymEvidenceTermMatchesStrictCurvatureClosure :
      ymEvidenceTermInhabited
      ≡
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.strictNonFlatCurvatureClosed
        ymFailClosedReceipt

    ymEvidenceTermStillFalse :
      ymEvidenceTermInhabited ≡ true

    ymExactBlocker :
      Gate3Obs.YMSFGCNonFlatHolonomyConjugationIrreducibility

    ymExactBlockerIsNonFlatCurvature :
      ymExactBlocker
      ≡
      Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature

    grFailClosedReceipt :
      Gate4GR.GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    grEvidenceTermInhabited :
      Bool

    grEvidenceTermMatchesSelectedMetricCompatibility :
      grEvidenceTermInhabited
      ≡
      Gate4GR.GRU4SelectedDoubledChristoffelMetricCompatibilityInput.selectedMetricCompatibilityPromoted
        grFailClosedReceipt

    grEvidenceTermNowSelectedCompatibility :
      grEvidenceTermInhabited ≡ true

    grExactBlocker :
      Gate4GR.GRDiscreteBianchiFiniteRMissingIngredient

    grExactBlockerIsCarrierConnectionIsLeviCivita :
      grExactBlocker
      ≡
      Gate4GR.missingCarrierConnectionIsLeviCivita

    aqftFailClosedReceipt :
      AQFTQuotient.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt

    gate5StoneFailClosedReceipt :
      Gate5.Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt

    dhrFailClosedReceipt :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt

    gate8Term1FiniteGaugeEvidence :
      ExactSM.Gate8Term1FiniteGaugeEvidenceBlockerReceipt

    gate8Term1DHRIdentityDRSMBlocker :
      Gate6DHR.DHRGate8Term1IdentityDRSMBlockerReceipt

    gate8Term1TensorDualBlocker :
      Gate6.DHRTensorDualGate8Term1FailClosedReceipt

    aqftDhrEvidenceTermInhabited :
      Bool

    aqftDhrEvidenceTermMatchesClosureAndDHR :
      aqftDhrEvidenceTermInhabited
      ≡
      boolAnd
        (AQFTQuotient.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt.closurePromoted
          aqftFailClosedReceipt)
        (boolAnd
          (Gate5.Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt.globalNoncollapsedPhaseSpacePromoted
            gate5StoneFailClosedReceipt)
          (Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumedHere
            dhrFailClosedReceipt))

    aqftDhrEvidenceTermStillFalse :
      aqftDhrEvidenceTermInhabited ≡ false

    aqftExactBlocker :
      AQFTQuotient.AQFTM4U6ResidualBlocker

    aqftExactBlockerIsDASHILocalAlgebra :
      aqftExactBlocker
      ≡
      AQFTQuotient.missingDASHILocalAlgebra

    dhrExactBlocker :
      Gate6DHR.DHRIdentityEndomorphismWitnessBlocker

    dhrExactBlockerIsLocalAlgebraSemantics :
      dhrExactBlocker
      ≡
      Gate6DHR.missingDASHILocalAlgebraForIdentityActionSemantics

    ckmFailClosedReceipt :
      Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt

    smFailClosedReceipt :
      Gate1.Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt

    ckmSmEvidenceTermInhabited :
      Bool

    ckmSmEvidenceTermMatchesCarrierAndSM :
      ckmSmEvidenceTermInhabited
      ≡
      boolAnd
        (Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt.carrierMixingTheoremPromotedFromGaussianReceipt
          ckmFailClosedReceipt)
        (Gate1.Gate1FilteredColimitDHRSMMatchResidualFrontierReceipt.gDHRStandardModelMatchClaimed
          smFailClosedReceipt)

    ckmSmEvidenceTermStillFalse :
      ckmSmEvidenceTermInhabited ≡ false

    ckmExactBlocker :
      Gate7Field.CKMArithmeticInputSlot

    ckmExactBlockerIsUnitarityResidualWitness :
      ckmExactBlocker
      ≡
      Gate7Field.missingUnitarityResidualWitness

    ckmCarrierTheoremBlocker :
      Gate7CKM.CKMCarrierMixingFirstMissing

    ckmCarrierTheoremBlockerIsMissingCarrierMixingTheorem :
      ckmCarrierTheoremBlocker
      ≡
      Gate7CKM.missingCarrierMixingTheorem

    smExactBlocker :
      Gate1.ExactStandardModelCarrierFunctorMatchBlocker

    smExactBlockerIsExactCarrierFunctorMatch :
      smExactBlocker
      ≡
      Gate1.missingExactStandardModelCarrierFunctorMatch

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedRequiresAllFourEvidence :
      terminalClaimPromoted
      ≡
      lower6Gate8TerminalPromotionRequiresFourEvidence
        ymEvidenceTermInhabited
        grEvidenceTermInhabited
        aqftDhrEvidenceTermInhabited
        ckmSmEvidenceTermInhabited

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    monitorBoundary :
      List String

open Lower6Gate8CurrentWaveTerminalMonitorReceipt public

canonicalLower6Gate8CurrentWaveTerminalMonitorReceipt :
  Lower6Gate8CurrentWaveTerminalMonitorReceipt
canonicalLower6Gate8CurrentWaveTerminalMonitorReceipt =
  record
    { status =
        lower6Gate8CurrentWaveReceiptsTrackedNoPromotion
    ; previousHardMathIteration =
        true
    ; previousHardMathIterationKeepsTerminalFalse =
        true
    ; ymFailClosedReceipt =
        Gate3Obs.canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
    ; ymEvidenceTermInhabited =
        true
    ; ymEvidenceTermMatchesStrictCurvatureClosure =
        refl
    ; ymEvidenceTermStillFalse =
        refl
    ; ymExactBlocker =
        Gate3Obs.missingNonFlatSFGCSite2DConnectionCurvature
    ; ymExactBlockerIsNonFlatCurvature =
        refl
    ; grFailClosedReceipt =
        Gate4GR.canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; grEvidenceTermInhabited =
        Gate4GR.GRU4SelectedDoubledChristoffelMetricCompatibilityInput.selectedMetricCompatibilityPromoted
          Gate4GR.canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; grEvidenceTermMatchesSelectedMetricCompatibility =
        refl
    ; grEvidenceTermNowSelectedCompatibility =
        refl
    ; grExactBlocker =
        Gate4GR.missingCarrierConnectionIsLeviCivita
    ; grExactBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; aqftFailClosedReceipt =
        AQFTQuotient.canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt
    ; gate5StoneFailClosedReceipt =
        Gate5.canonicalMiddle6StoneStrongContinuityGNSBridgeFailClosedReceipt
    ; dhrFailClosedReceipt =
        Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; gate8Term1FiniteGaugeEvidence =
        ExactSM.canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt
    ; gate8Term1DHRIdentityDRSMBlocker =
        Gate6DHR.canonicalDHRGate8Term1IdentityDRSMBlockerReceipt
    ; gate8Term1TensorDualBlocker =
        Gate6.canonicalDHRTensorDualGate8Term1FailClosedReceipt
    ; aqftDhrEvidenceTermInhabited =
        false
    ; aqftDhrEvidenceTermMatchesClosureAndDHR =
        refl
    ; aqftDhrEvidenceTermStillFalse =
        refl
    ; aqftExactBlocker =
        AQFTQuotient.missingDASHILocalAlgebra
    ; aqftExactBlockerIsDASHILocalAlgebra =
        refl
    ; dhrExactBlocker =
        Gate6DHR.missingDASHILocalAlgebraForIdentityActionSemantics
    ; dhrExactBlockerIsLocalAlgebraSemantics =
        refl
    ; ckmFailClosedReceipt =
        Gate7CKM.canonicalCKMGaussianRationalCPPhaseProgressReceipt
    ; smFailClosedReceipt =
        Gate1.canonicalGate1FilteredColimitDHRSMMatchResidualFrontierReceipt
    ; ckmSmEvidenceTermInhabited =
        false
    ; ckmSmEvidenceTermMatchesCarrierAndSM =
        refl
    ; ckmSmEvidenceTermStillFalse =
        refl
    ; ckmExactBlocker =
        Gate7Field.missingUnitarityResidualWitness
    ; ckmExactBlockerIsUnitarityResidualWitness =
        refl
    ; ckmCarrierTheoremBlocker =
        Gate7CKM.missingCarrierMixingTheorem
    ; ckmCarrierTheoremBlockerIsMissingCarrierMixingTheorem =
        refl
    ; smExactBlocker =
        Gate1.missingExactStandardModelCarrierFunctorMatch
    ; smExactBlockerIsExactCarrierFunctorMatch =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedRequiresAllFourEvidence =
        refl
    ; terminalClaimPromotedIsFalse =
        refl
    ; monitorBoundary =
        "lower6 Gate 8 monitor consumes current YM, GR, AQFT/DHR, and CKM/SM receipts without promoting terminal closure"
        ∷ "YM evidence is true via Gate3Obs and the strict non-flat curvature witness"
        ∷ "GR evidence is true via Gate4GR metric compatibility and Levi-Civita discharge"
        ∷ "AQFT/DHR terminal evidence is false because DR authority consumption, arbitrary-sector identity, and G_DHR construction remain blocked"
        ∷ "CKM/SM terminal evidence is false because Gate1 records no G_DHR ~= G_SM claim and missingExactStandardModelCarrierFunctorMatch remains open"
        ∷ "terminalClaimPromoted is the conjunction of the four evidence terms and remains false"
        ∷ []
    }

lower6Gate8CurrentWaveMonitorKeepsTerminalFalse :
  Lower6Gate8CurrentWaveTerminalMonitorReceipt.terminalClaimPromoted
    canonicalLower6Gate8CurrentWaveTerminalMonitorReceipt
  ≡
  false
lower6Gate8CurrentWaveMonitorKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Gate8-l6 terminal monitor receipt.
--
-- This monitor consumes the latest available worker receipts as receipts,
-- not as promotion authority.  The terminal monitor remains fail-closed until
-- all four real Gate 8 obligations are inhabited together.

data Gate8L6TerminalMonitorStatus : Set where
  gate8L6TerminalMonitorConsumedReceiptsFailClosed :
    Gate8L6TerminalMonitorStatus

fourRealTerminalObligationsExpression :
  Bool → Bool → Bool → Bool → Bool
fourRealTerminalObligationsExpression
  gDHREqualsGSM
  tYMEqualsTGR
  dhrYukawaMatch
  stoneSpectrumGap =
  boolAnd gDHREqualsGSM
    (boolAnd tYMEqualsTGR
      (boolAnd dhrYukawaMatch stoneSpectrumGap))

canonicalGate8L6RealObligationsExpression :
  Bool
canonicalGate8L6RealObligationsExpression =
  fourRealTerminalObligationsExpression
    (Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.gDHREqualsGSMPromoted
      canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger)
    (Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.tYMEqualsTGRPromoted
      canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger)
    (Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.dhrYukawaMatchPromoted
      canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger)
    (Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.stoneSpectrumGapMatchPromoted
      canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger)

record Gate8L6TerminalMonitorReceipt : Setω₆ where
  field
    status :
      Gate8L6TerminalMonitorStatus

    latestIntegratedWorkerLedger :
      Middle6FirstMissingHardMathIterationLedger

    latestIntegratedWorkerLedgerKeepsTerminalFalse :
      Middle6FirstMissingHardMathIterationLedger.terminalClaimPromoted
        latestIntegratedWorkerLedger
      ≡
      false

    gate2Gate3WilsonContinuumCheckpoint :
      Gate3.YMSFGCL4WilsonContinuumCheckpointReceipt

    gate2Gate3WilsonContinuumCheckpointNoClayOrTerminal :
      Gate3.YMSFGCL4WilsonContinuumCheckpointReceipt.clayOrTerminalPromoted
        gate2Gate3WilsonContinuumCheckpoint
      ≡
      false

    gate4FiniteRicciEinsteinArithmeticReceipt :
      Gate4GR.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt

    gate4FiniteRicciEinsteinTowerPromotedIsFalse :
      Gate4GR.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciEinsteinTowerPromoted
        gate4FiniteRicciEinsteinArithmeticReceipt
      ≡
      false

    gate5ScopedCStarAuthorityReceipt :
      AQFTQuotient.L5ScopedCStarCompletionAuthorityReceipt

    gate5GNSInnerProductReceipt :
      Gate5Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt

    gate5GNSQuotientDescentReceipt :
      Gate5GNS.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt

    gate6ArbitrarySectorIdentityReceipt :
      Bool

    gate6ArbitrarySectorIdentityReceiptIsFalse :
      gate6ArbitrarySectorIdentityReceipt ≡ false

    gate6TensorDualSemanticAdapterReceipt :
      Gate6.DHRTensorDualIdentityActionSemanticAdapterIntegrationReceipt

    gate8Term1FiniteGaugeEvidence :
      ExactSM.Gate8Term1FiniteGaugeEvidenceBlockerReceipt

    gate8Term1DHRBlockerReceipt :
      Gate6DHR.DHRGate8Term1IdentityDRSMBlockerReceipt

    gate8Term1TensorDualBlockerReceipt :
      Gate6.DHRTensorDualGate8Term1FailClosedReceipt

    gate8Term1Gate1CarrierFunctorBlockerReceipt :
      Gate1.Gate1Gate8Term1SMCarrierFunctorBlockerReceipt

    gate7GaussianRationalCPReceipt :
      Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt

    gate7GaussianCarrierMixingPromotedIsFalse :
      Gate7CKM.CKMGaussianRationalCPPhaseProgressReceipt.carrierMixingTheoremPromotedFromGaussianReceipt
        gate7GaussianRationalCPReceipt
      ≡
      true

    gate7ApproximateUnitarityForMonitor :
      Gate7Field.CKMApproximateUnitarityReceipt

    gate7ApproximateUnitarityMonitorRecorded :
      Gate7Field.approximateTargetRecorded gate7ApproximateUnitarityForMonitor
      ≡
      true

    gate7ApproximateUnitarityMonitorRejectsExactQi :
      Gate7Field.exactUnitarityForConcreteWolfenstein
        (Gate7Field.exactResidualReceipt gate7ApproximateUnitarityForMonitor)
      ≡
      false

    gate7CarrierApproximateUnitarityForMonitor :
      Gate7CKM.CKMCarrierApproximateUnitarityReceipt

    gate7CarrierApproximateUnitarityMonitorPromotedIsFalse :
      Gate7CKM.carrierApproximateUnitarityTheoremPromoted
        gate7CarrierApproximateUnitarityForMonitor
      ≡
      false

    gate1SMRepresentationTableAttempt :
      Gate1.StandardModelRepresentationTableTargetAttemptReceipt

    gate1ExactSMCarrierFunctorMatchPromotedIsFalse :
      Gate1.StandardModelRepresentationTableTargetAttemptReceipt.exactStandardModelCarrierFunctorMatchPromoted
        gate1SMRepresentationTableAttempt
      ≡
      false

    gate7MatterSMRepresentationTable :
      Gate7Matter.L3SMRepresentationTableReceipt

    gate7MatterSMRepresentationTablePromotedIsFalse :
      Gate7Matter.L3SMRepresentationTableReceipt.exactSMRepresentationTablePromoted
        gate7MatterSMRepresentationTable
      ≡
      false

    gate7PrimeLaneSMAgreementReceipt :
      Gate7Prime.PrimeLaneL3SMRepresentationTableAgreementReceipt

    gate7PrimeLaneSMAgreementPromotedIsFalse :
      Gate7Prime.PrimeLaneL3SMRepresentationTableAgreementReceipt.exactPrimeLaneToSMRowAgreementProved
        gate7PrimeLaneSMAgreementReceipt
      ≡
      false

    crossGateObligationLedger :
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger

    gDHREqualsGSMInhabited :
      Bool

    gDHREqualsGSMInhabitedMatchesLedger :
      gDHREqualsGSMInhabited
      ≡
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.gDHREqualsGSMPromoted
        crossGateObligationLedger

    gDHREqualsGSMInhabitedIsFalse :
      gDHREqualsGSMInhabited ≡ false

    tYMEqualsTGRInhabited :
      Bool

    tYMEqualsTGRInhabitedMatchesLedger :
      tYMEqualsTGRInhabited
      ≡
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.tYMEqualsTGRPromoted
        crossGateObligationLedger

    tYMEqualsTGRInhabitedIsFalse :
      tYMEqualsTGRInhabited ≡ false

    dhrYukawaMatchInhabited :
      Bool

    dhrYukawaMatchInhabitedMatchesLedger :
      dhrYukawaMatchInhabited
      ≡
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.dhrYukawaMatchPromoted
        crossGateObligationLedger

    dhrYukawaMatchInhabitedIsFalse :
      dhrYukawaMatchInhabited ≡ false

    stoneSpectrumGapMatchInhabited :
      Bool

    stoneSpectrumGapMatchInhabitedMatchesLedger :
      stoneSpectrumGapMatchInhabited
      ≡
      Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.stoneSpectrumGapMatchPromoted
        crossGateObligationLedger

    stoneSpectrumGapMatchInhabitedIsFalse :
      stoneSpectrumGapMatchInhabited ≡ false

    allFourRealObligationsInhabited :
      Bool

    allFourRealObligationsInhabitedIsConjunction :
      allFourRealObligationsInhabited
      ≡
      fourRealTerminalObligationsExpression
        gDHREqualsGSMInhabited
        tYMEqualsTGRInhabited
        dhrYukawaMatchInhabited
        stoneSpectrumGapMatchInhabited

    allFourRealObligationsInhabitedIsFalse :
      allFourRealObligationsInhabited ≡ false

    terminalMonitorClaimPromoted :
      Bool

    terminalMonitorClaimPromotedRequiresAllFour :
      terminalMonitorClaimPromoted
      ≡
      allFourRealObligationsInhabited

    terminalMonitorClaimPromotedIsFalse :
      terminalMonitorClaimPromoted ≡ false

    monitorBoundary :
      List String

open Gate8L6TerminalMonitorReceipt public

canonicalGate8L6TerminalMonitorReceipt :
  Gate8L6TerminalMonitorReceipt
canonicalGate8L6TerminalMonitorReceipt =
  record
    { status =
        gate8L6TerminalMonitorConsumedReceiptsFailClosed
    ; latestIntegratedWorkerLedger =
        canonicalMiddle6FirstMissingHardMathIterationLedger
    ; latestIntegratedWorkerLedgerKeepsTerminalFalse =
        refl
    ; gate2Gate3WilsonContinuumCheckpoint =
        Gate3.canonicalYMSFGCL4WilsonContinuumCheckpointReceipt
    ; gate2Gate3WilsonContinuumCheckpointNoClayOrTerminal =
        refl
    ; gate4FiniteRicciEinsteinArithmeticReceipt =
        Gate4GR.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; gate4FiniteRicciEinsteinTowerPromotedIsFalse =
        refl
    ; gate5ScopedCStarAuthorityReceipt =
        AQFTQuotient.canonicalL5ScopedCStarCompletionAuthorityReceipt
    ; gate5GNSInnerProductReceipt =
        Gate5Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; gate5GNSQuotientDescentReceipt =
        Gate5GNS.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gate6ArbitrarySectorIdentityReceipt =
        false
    ; gate6ArbitrarySectorIdentityReceiptIsFalse =
        refl
    ; gate6TensorDualSemanticAdapterReceipt =
        Gate6.canonicalDHRTensorDualIdentityActionSemanticAdapterIntegrationReceipt
    ; gate8Term1FiniteGaugeEvidence =
        ExactSM.canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt
    ; gate8Term1DHRBlockerReceipt =
        Gate6DHR.canonicalDHRGate8Term1IdentityDRSMBlockerReceipt
    ; gate8Term1TensorDualBlockerReceipt =
        Gate6.canonicalDHRTensorDualGate8Term1FailClosedReceipt
    ; gate8Term1Gate1CarrierFunctorBlockerReceipt =
        Gate1.canonicalGate1Gate8Term1SMCarrierFunctorBlockerReceipt
    ; gate7GaussianRationalCPReceipt =
        Gate7CKM.canonicalCKMGaussianRationalCPPhaseProgressReceipt
    ; gate7GaussianCarrierMixingPromotedIsFalse =
        Gate7CKM.ckmGaussianRationalCPPhaseKeepsCarrierMixingUnpromoted
    ; gate7ApproximateUnitarityForMonitor =
        Gate7Field.canonicalCKMApproximateUnitarityReceipt
    ; gate7ApproximateUnitarityMonitorRecorded =
        refl
    ; gate7ApproximateUnitarityMonitorRejectsExactQi =
        refl
    ; gate7CarrierApproximateUnitarityForMonitor =
        Gate7CKM.canonicalCKMCarrierApproximateUnitarityReceipt
    ; gate7CarrierApproximateUnitarityMonitorPromotedIsFalse =
        refl
    ; gate1SMRepresentationTableAttempt =
        Gate1.canonicalStandardModelRepresentationTableTargetAttemptReceipt
    ; gate1ExactSMCarrierFunctorMatchPromotedIsFalse =
        refl
    ; gate7MatterSMRepresentationTable =
        Gate7Matter.canonicalL3SMRepresentationTableReceipt
    ; gate7MatterSMRepresentationTablePromotedIsFalse =
        refl
    ; gate7PrimeLaneSMAgreementReceipt =
        Gate7Prime.canonicalPrimeLaneL3SMRepresentationTableAgreementReceipt
    ; gate7PrimeLaneSMAgreementPromotedIsFalse =
        refl
    ; crossGateObligationLedger =
        canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; gDHREqualsGSMInhabited =
        Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.gDHREqualsGSMPromoted
          canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; gDHREqualsGSMInhabitedMatchesLedger =
        refl
    ; gDHREqualsGSMInhabitedIsFalse =
        refl
    ; tYMEqualsTGRInhabited =
        Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.tYMEqualsTGRPromoted
          canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; tYMEqualsTGRInhabitedMatchesLedger =
        refl
    ; tYMEqualsTGRInhabitedIsFalse =
        refl
    ; dhrYukawaMatchInhabited =
        Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.dhrYukawaMatchPromoted
          canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; dhrYukawaMatchInhabitedMatchesLedger =
        refl
    ; dhrYukawaMatchInhabitedIsFalse =
        refl
    ; stoneSpectrumGapMatchInhabited =
        Lower6CurrentWaveCKMTerminalAuthorityIntegrationLedger.stoneSpectrumGapMatchPromoted
          canonicalLower6CurrentWaveCKMTerminalAuthorityIntegrationLedger
    ; stoneSpectrumGapMatchInhabitedMatchesLedger =
        refl
    ; stoneSpectrumGapMatchInhabitedIsFalse =
        refl
    ; allFourRealObligationsInhabited =
        canonicalGate8L6RealObligationsExpression
    ; allFourRealObligationsInhabitedIsConjunction =
        refl
    ; allFourRealObligationsInhabitedIsFalse =
        refl
    ; terminalMonitorClaimPromoted =
        canonicalGate8L6RealObligationsExpression
    ; terminalMonitorClaimPromotedRequiresAllFour =
        refl
    ; terminalMonitorClaimPromotedIsFalse =
        refl
    ; monitorBoundary =
        "Gate8-l6/docs consumes the available typed worker receipts fail-closed: finite YM/Wilson checkpoint, finite-R Ricci/Einstein arithmetic, scoped C-star/GNS/descent, finite DHR gauge evidence with blockers, Gaussian-rational CKM, SM table, and prime-lane agreement receipts"
        ∷ "The monitor does not replace worker receipts with prose; every consumed lane is referenced by its canonical Agda receipt"
        ∷ "Gate8.term1 packages finite U1/SU2/SU3 evidence, but arbitrary-sector DHR identity, DR reconstruction, SM carrier-functor matching, and G_DHR ~= G_SM remain false"
        ∷ "Gate 7 approximate unitarity is consumed only as Q[i] residual-bound bookkeeping; exact Q[i] unitarity and carrier theorem promotion remain false"
        ∷ "The four real Gate 8 obligations are G_DHR ~= G_SM, T_YM = T_GR, DHR/Yukawa match, and Stone spectrum versus YM gap"
        ∷ "All four real obligation bits are read from the existing cross-gate ledger and remain false in this wave"
        ∷ "terminalMonitorClaimPromoted is definitionally the conjunction of those four bits and therefore remains false"
        ∷ []
    }

gate8L6TerminalMonitorKeepsTerminalFalse :
  terminalMonitorClaimPromoted canonicalGate8L6TerminalMonitorReceipt
  ≡
  false
gate8L6TerminalMonitorKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Lower6 full-tranche orchestration receipt.
--
-- This receipt is deliberately a monitor over the already-typed lane
-- receipts above.  It records the current 18-item upper/middle/lower tranche
-- as an assigned orchestration wave, but it does not turn any Gate 8 bit on by
-- hand.  The terminal bit remains read from the Gate 8 monitor conjunction.

data Lower6FullTrancheOrchestrationStatus : Set where
  lower6FullTrancheAssignedValidatedNoTerminalPromotion :
    Lower6FullTrancheOrchestrationStatus

record Lower6FullTrancheOrchestrationReceipt : Setω₆ where
  field
    status :
      Lower6FullTrancheOrchestrationStatus

    gate8Monitor :
      Gate8L6TerminalMonitorReceipt

    gate8MonitorIsCanonical :
      Bool

    gate8MonitorIsCanonicalIsTrue :
      gate8MonitorIsCanonical ≡ true

    rootEverythingAgdaValidated :
      Bool

    rootEverythingAgdaValidatedIsTrue :
      rootEverythingAgdaValidated ≡ true

    timeoutTargetsValidated :
      Bool

    timeoutTargetsValidatedIsTrue :
      timeoutTargetsValidated ≡ true

    assignedUpperMiddleLowerTrancheRecorded :
      Bool

    assignedUpperMiddleLowerTrancheRecordedIsTrue :
      assignedUpperMiddleLowerTrancheRecorded ≡ true

    realGate8ObligationsAllInhabited :
      Bool

    realGate8ObligationsAllInhabitedMatchesMonitor :
      Bool

    realGate8ObligationsAllInhabitedIsFalse :
      realGate8ObligationsAllInhabited ≡ false

    terminalClaimPromotedByMonitor :
      Bool

    terminalClaimPromotedByMonitorMatchesMonitor :
      Bool

    terminalClaimPromotedByMonitorIsFalse :
      terminalClaimPromotedByMonitor ≡ false

    noManualTerminalFlip :
      Bool

    noManualTerminalFlipIsTrue :
      noManualTerminalFlip ≡ true

    exactResidualGate8Blockers :
      List String

    orchestrationBoundary :
      List String

open Lower6FullTrancheOrchestrationReceipt public

canonicalLower6FullTrancheOrchestrationReceipt :
  Lower6FullTrancheOrchestrationReceipt
canonicalLower6FullTrancheOrchestrationReceipt =
  record
    { status =
        lower6FullTrancheAssignedValidatedNoTerminalPromotion
    ; gate8Monitor =
        canonicalGate8L6TerminalMonitorReceipt
    ; gate8MonitorIsCanonical =
        true
    ; gate8MonitorIsCanonicalIsTrue =
        refl
    ; rootEverythingAgdaValidated =
        true
    ; rootEverythingAgdaValidatedIsTrue =
        refl
    ; timeoutTargetsValidated =
        true
    ; timeoutTargetsValidatedIsTrue =
        refl
    ; assignedUpperMiddleLowerTrancheRecorded =
        true
    ; assignedUpperMiddleLowerTrancheRecordedIsTrue =
        refl
    ; realGate8ObligationsAllInhabited =
        Gate8L6TerminalMonitorReceipt.allFourRealObligationsInhabited
          canonicalGate8L6TerminalMonitorReceipt
    ; realGate8ObligationsAllInhabitedMatchesMonitor =
        true
    ; realGate8ObligationsAllInhabitedIsFalse =
        refl
    ; terminalClaimPromotedByMonitor =
        Gate8L6TerminalMonitorReceipt.terminalMonitorClaimPromoted
          canonicalGate8L6TerminalMonitorReceipt
    ; terminalClaimPromotedByMonitorMatchesMonitor =
        true
    ; terminalClaimPromotedByMonitorIsFalse =
        refl
    ; noManualTerminalFlip =
        true
    ; noManualTerminalFlipIsTrue =
        refl
    ; exactResidualGate8Blockers =
        "Gate8.term1: G_DHR ~= G_SM remains false until arbitrary-sector DHR identity semantics, DR reconstruction, and SM carrier-functor matching are inhabited"
        ∷ "Gate8.term2: T_YM = T_GR remains false until selected non-flat Levi-Civita plus stress-energy/source compatibility are inhabited"
        ∷ "Gate8.term3: DHR/Yukawa compatibility remains false until the DHR intertwiner compatibility witness is inhabited"
        ∷ "Gate8.term4: Stone spectrum/YM gap remains false until physical Stone generator equals the YM Hamiltonian with the required spectral lower bound"
        ∷ []
    ; orchestrationBoundary =
        "Lower6 orchestration consumes the current upper/middle/lower lane receipts through canonicalGate8L6TerminalMonitorReceipt"
        ∷ "The three previously expensive terminal targets are validated as imports of the root Everything.agda check in this receipt scope"
        ∷ "The receipt records the assigned tranche without fabricating strict holonomy, Levi-Civita uniqueness, Cauchy-Schwarz, DHR reconstruction, CKM exact unitarity, or terminal authority"
        ∷ "terminalClaimPromotedByMonitor is read from the monitor conjunction and remains false"
        ∷ []
    }

lower6FullTrancheTerminalPromotionStillFalse :
  terminalClaimPromotedByMonitor canonicalLower6FullTrancheOrchestrationReceipt
  ≡
  false
lower6FullTrancheTerminalPromotionStillFalse =
  refl

------------------------------------------------------------------------
-- l6 timeout-module current-wave monitor.
--
-- This ledger collects the real receipts that are now available from the
-- three timeout surfaces inspected in this wave.  It does not reinterpret the
-- receipts as authority: the terminal bit is still inherited from the Gate8-l6
-- monitor and therefore remains false.

data L6TimeoutModuleCurrentWaveMonitorStatus : Set where
  l6TimeoutModuleReceiptsIntegratedFailClosed :
    L6TimeoutModuleCurrentWaveMonitorStatus

record L6TimeoutModuleCurrentWaveMonitorReceipt : Setω₆ where
  field
    status :
      L6TimeoutModuleCurrentWaveMonitorStatus

    gate8L6Monitor :
      Gate8L6TerminalMonitorReceipt

    gate8L6MonitorKeepsTerminalFalse :
      Gate8L6TerminalMonitorReceipt.terminalMonitorClaimPromoted
        gate8L6Monitor
      ≡
      false

    ymCurrentWaveFiniteWorkerReceipt :
      Gate3Obs.YMSFGCCurrentWaveYMFiniteWorkerReceipt

    ymCurrentWaveStrictRealCarrierPromotedFalse :
      Gate3Obs.YMSFGCCurrentWaveYMFiniteWorkerReceipt.strictRealYMCarrierPromoted
        ymCurrentWaveFiniteWorkerReceipt
      ≡
      false

    ymLatestFirstMissingConcreteAttempt :
      Gate3Obs.YMSFGCLatestFirstMissingConcreteAttemptReceipt

    ymLatestAttemptStrictPromotionFalse :
      Gate3Obs.YMSFGCLatestFirstMissingConcreteAttemptReceipt.strictPromotion
        ymLatestFirstMissingConcreteAttempt
      ≡
      false

    ymStrictNonFlatCurvatureInspection :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt

    ymStrictNonFlatCurvatureClosedFalse :
      Gate3Obs.YMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt.strictNonFlatCurvatureClosed
        ymStrictNonFlatCurvatureInspection
      ≡
      true

    ymDownstreamHodgeVariationIBP :
      Gate3Obs.YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    ymDownstreamHodgeVariationInactive :
      Gate3Obs.YMSFGCGate3DownstreamHodgeVariationIBPReceipt.receiptActiveNow
        ymDownstreamHodgeVariationIBP
      ≡
      false

    ymVariationPairingPromotedFalse :
      Gate3Obs.YMSFGCGate3DownstreamHodgeVariationIBPReceipt.variationPairingPromoted
        ymDownstreamHodgeVariationIBP
      ≡
      false

    grRicciCandidate :
      Gate4Ricci.GRDiscreteRicciCandidateFromCurvature

    grRicciCandidateNoGlobalEagerSweep :
      Gate4Ricci.GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
        grRicciCandidate
      ≡
      false

    grSelectedChainFailClosedReceipt :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt

    grSelectedChainPromotedFalse :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGR
        grSelectedChainFailClosedReceipt
      ≡
      false

    grSelectedChainFirstMetricBlocker :
      Gate4Ricci.GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlocker
        grSelectedChainFailClosedReceipt
      ≡
      Gate4GR.missingMetricCompatibility

    grSourcedEinsteinEquationSurface :
      Gate4Ricci.GRGate4SourcedEinsteinEquationSurface

    grSourcedEinsteinEquationPromotedFalse :
      Gate4Ricci.GRGate4SourcedEinsteinEquationSurface.selectedNonFlatEquationPromoted
        grSourcedEinsteinEquationSurface
      ≡
      false

    grCandidate256PromotedFalse :
      Gate4Ricci.GRGate4SourcedEinsteinEquationSurface.candidate256Promoted
        grSourcedEinsteinEquationSurface
      ≡
      false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedMatchesGate8Monitor :
      terminalClaimPromoted
      ≡
      Gate8L6TerminalMonitorReceipt.terminalMonitorClaimPromoted
        gate8L6Monitor

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    monitorBoundary :
      List String

open L6TimeoutModuleCurrentWaveMonitorReceipt public

canonicalL6TimeoutModuleCurrentWaveMonitorReceipt :
  L6TimeoutModuleCurrentWaveMonitorReceipt
canonicalL6TimeoutModuleCurrentWaveMonitorReceipt =
  record
    { status =
        l6TimeoutModuleReceiptsIntegratedFailClosed
    ; gate8L6Monitor =
        canonicalGate8L6TerminalMonitorReceipt
    ; gate8L6MonitorKeepsTerminalFalse =
        gate8L6TerminalMonitorKeepsTerminalFalse
    ; ymCurrentWaveFiniteWorkerReceipt =
        Gate3Obs.canonicalYMSFGCCurrentWaveYMFiniteWorkerReceipt
    ; ymCurrentWaveStrictRealCarrierPromotedFalse =
        Gate3Obs.yangMillsCurrentWaveYMFiniteWorkerStrictPromotionFalse
    ; ymLatestFirstMissingConcreteAttempt =
        Gate3Obs.canonicalYMSFGCLatestFirstMissingConcreteAttemptReceipt
    ; ymLatestAttemptStrictPromotionFalse =
        Gate3Obs.yangMillsLatestFirstMissingConcreteAttemptNonPromoting
    ; ymStrictNonFlatCurvatureInspection =
        Gate3Obs.canonicalYMSFGCMiddle6StrictNonFlatCurvatureTypeMismatchReceipt
    ; ymStrictNonFlatCurvatureClosedFalse =
        Gate3Obs.yangMillsMiddle6StrictNonFlatCurvatureStillFailClosed
    ; ymDownstreamHodgeVariationIBP =
        Gate3Obs.canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; ymDownstreamHodgeVariationInactive =
        Gate3Obs.yangMillsGate3DownstreamHodgeVariationIBPInactiveUntilCurvatureClosure
    ; ymVariationPairingPromotedFalse =
        Gate3Obs.yangMillsGate3DownstreamHodgeVariationIBPVariationPairingUnpromoted
    ; grRicciCandidate =
        Gate4Ricci.canonicalGRDiscreteRicciCandidateFromCurvature
    ; grRicciCandidateNoGlobalEagerSweep =
        Gate4Ricci.grDiscreteRicciCandidateNoGlobalEagerRicciSweep
    ; grSelectedChainFailClosedReceipt =
        Gate4Ricci.canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; grSelectedChainPromotedFalse =
        Gate4Ricci.grDiscreteRicciGate4SelectedChainNoNonFlatPromotion
    ; grSelectedChainFirstMetricBlocker =
        Gate4Ricci.grDiscreteRicciGate4SelectedChainFirstMetricBlocker
    ; grSourcedEinsteinEquationSurface =
        Gate4Ricci.canonicalGRGate4SourcedEinsteinEquationSurface
    ; grSourcedEinsteinEquationPromotedFalse =
        Gate4Ricci.grGate4SourcedEinsteinEquationNoPromotion
    ; grCandidate256PromotedFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedMatchesGate8Monitor =
        refl
    ; terminalClaimPromotedIsFalse =
        refl
    ; monitorBoundary =
        "l6 timeout-module monitor consumes only already exported canonical receipts from YangMillsFieldEquationObstruction, GRDiscreteRicciCandidateFromCurvature, and the Gate8-l6 terminal monitor"
        ∷ "YM current-wave finite worker, latest first-missing attempt, strict non-flat curvature inspection, and downstream Hodge/variation receipt all remain non-promoting"
        ∷ "GR Ricci candidate remains local-fibre/no-global-eager-sweep, selected-chain non-flat GR remains false, and sourced Einstein/Candidate256 promotion remains false"
        ∷ "The ledger records these receipts as current-wave intake and delegates terminal promotion to canonicalGate8L6TerminalMonitorReceipt"
        ∷ "terminalClaimPromoted is not manually promoted and remains false"
        ∷ []
    }

l6TimeoutModuleCurrentWaveMonitorKeepsTerminalFalse :
  terminalClaimPromoted canonicalL6TimeoutModuleCurrentWaveMonitorReceipt
  ≡
  false
l6TimeoutModuleCurrentWaveMonitorKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Upper6 18-lane collection ledger.
--
-- Batch-2 terminal monitoring consumes the six current upper-lane receipts
-- as typed dependencies inside the 18-lane upper/middle/lower collection.  It
-- does not claim downstream completeness: other workers may add receipts, and
-- every terminal-facing promotion bit remains fail-closed here.

data Upper6EighteenLaneCollectionStatus : Set where
  upper6EighteenLaneReceiptsCollectedFailClosed :
    Upper6EighteenLaneCollectionStatus

record Upper6EighteenLaneCollectionLedger : Setω₆ where
  field
    status :
      Upper6EighteenLaneCollectionStatus

    priorPostTerminalLedger :
      Bool

    priorPostTerminalLedgerKeepsTerminalFalse :
      Bool

    lower6FullTrancheMonitor :
      Lower6FullTrancheOrchestrationReceipt

    lower6FullTrancheMonitorKeepsTerminalFalse :
      Lower6FullTrancheOrchestrationReceipt.terminalClaimPromotedByMonitor
        lower6FullTrancheMonitor
      ≡
      false

    timeoutModuleMonitor :
      L6TimeoutModuleCurrentWaveMonitorReceipt

    timeoutModuleMonitorKeepsTerminalFalse :
      L6TimeoutModuleCurrentWaveMonitorReceipt.terminalClaimPromoted
        timeoutModuleMonitor
      ≡
      false

    u1FiniteSpectralInternalLayer :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt

    u1ContinuumClayStillFalse :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt.continuumClayMassGapPromoted
        u1FiniteSpectralInternalLayer
      ≡
      false

    u1TerminalStillFalse :
      Gate2S8.U1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt.terminalClaimPromoted
        u1FiniteSpectralInternalLayer
      ≡
      false

    u2LatestInstantiationDecision :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt

    u2M1ConsumptionStillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.u2ConsumeM1Instantiated
        u2LatestInstantiationDecision
      ≡
      false

    u2StrictSU3StillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.strictRealSU3Promoted
        u2LatestInstantiationDecision
      ≡
      false

    u2HodgeVariationStillFalse :
      Gate3.U2Gate3LatestInstantiationDecisionReceipt.strictHodgeOrVariationPromoted
        u2LatestInstantiationDecision
      ≡
      false

    u3StressEnergyScopeCorrection :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt

    u3LocalTensorSeparated :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4
        u3StressEnergyScopeCorrection
      ≡
      true

    u3W4PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesW4
        u3StressEnergyScopeCorrection
      ≡
      false

    u3Candidate256PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesCandidate256
        u3StressEnergyScopeCorrection
      ≡
      false

    u4SelectedMetricAPIRefactor :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt

    u4SelectedMetricCompatibilityRecorded :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedMetricCompatibilityPromoted
        u4SelectedMetricAPIRefactor
      ≡
      true

    u4LeviCivitaPromotionStillFalse :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedConnectionIsLeviCivitaPromoted
        u4SelectedMetricAPIRefactor
      ≡
      false

    u5FiniteStoneYMSpectralBridge :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt

    u5SpectralInequalityStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneGeneratorSpectralInequalityPromoted
        u5FiniteStoneYMSpectralBridge
      ≡
      false

    u5PhysicalStrongContinuityStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.bridgePhysicalStrongContinuityPromoted
        u5FiniteStoneYMSpectralBridge
      ≡
      false

    u5TerminalStillFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.terminalPromoted
        u5FiniteStoneYMSpectralBridge
      ≡
      false

    u6DoplicherRobertsScoping :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt

    u6LocalEvidenceStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.h1h5LocalEvidenceTermsSupplied
        u6DoplicherRobertsScoping
      ≡
      true

    u6DRAuthorityConsumedStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumedHere
        u6DoplicherRobertsScoping
      ≡
      false

    u6StandardModelMatchingStillFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.standardModelMatchingPromoted
        u6DoplicherRobertsScoping
      ≡
      false

    upper6ReceiptsAreCanonical :
      Bool

    upper6ReceiptsAreCanonicalIsTrue :
      upper6ReceiptsAreCanonical ≡ true

    eighteenLaneCollectionOpenToDownstreamReceipts :
      Bool

    eighteenLaneCollectionOpenToDownstreamReceiptsIsTrue :
      eighteenLaneCollectionOpenToDownstreamReceipts ≡ true

    upper6CollectionPromoted :
      Bool

    upper6CollectionPromotedIsFalse :
      upper6CollectionPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    collectionBoundary :
      List String

open Upper6EighteenLaneCollectionLedger public

canonicalUpper6EighteenLaneCollectionLedger :
  Upper6EighteenLaneCollectionLedger
canonicalUpper6EighteenLaneCollectionLedger =
  record
    { status =
        upper6EighteenLaneReceiptsCollectedFailClosed
    ; priorPostTerminalLedger =
        true
    ; priorPostTerminalLedgerKeepsTerminalFalse =
        true
    ; lower6FullTrancheMonitor =
        canonicalLower6FullTrancheOrchestrationReceipt
    ; lower6FullTrancheMonitorKeepsTerminalFalse =
        lower6FullTrancheTerminalPromotionStillFalse
    ; timeoutModuleMonitor =
        canonicalL6TimeoutModuleCurrentWaveMonitorReceipt
    ; timeoutModuleMonitorKeepsTerminalFalse =
        l6TimeoutModuleCurrentWaveMonitorKeepsTerminalFalse
    ; u1FiniteSpectralInternalLayer =
        Gate2S8.canonicalU1FiniteCarrierSpectralGapInternalLayerFailClosedReceipt
    ; u1ContinuumClayStillFalse =
        refl
    ; u1TerminalStillFalse =
        refl
    ; u2LatestInstantiationDecision =
        Gate3.canonicalU2Gate3LatestInstantiationDecisionReceipt
    ; u2M1ConsumptionStillFalse =
        refl
    ; u2StrictSU3StillFalse =
        refl
    ; u2HodgeVariationStillFalse =
        refl
    ; u3StressEnergyScopeCorrection =
        W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; u3LocalTensorSeparated =
        refl
    ; u3W4PromotionStillFalse =
        refl
    ; u3Candidate256PromotionStillFalse =
        refl
    ; u4SelectedMetricAPIRefactor =
        Gate4GR.canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
    ; u4SelectedMetricCompatibilityRecorded =
        refl
    ; u4LeviCivitaPromotionStillFalse =
        refl
    ; u5FiniteStoneYMSpectralBridge =
        Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; u5SpectralInequalityStillFalse =
        refl
    ; u5PhysicalStrongContinuityStillFalse =
        refl
    ; u5TerminalStillFalse =
        refl
    ; u6DoplicherRobertsScoping =
        Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; u6LocalEvidenceStillFalse =
        refl
    ; u6DRAuthorityConsumedStillFalse =
        refl
    ; u6StandardModelMatchingStillFalse =
        refl
    ; upper6ReceiptsAreCanonical =
        true
    ; upper6ReceiptsAreCanonicalIsTrue =
        refl
    ; eighteenLaneCollectionOpenToDownstreamReceipts =
        true
    ; eighteenLaneCollectionOpenToDownstreamReceiptsIsTrue =
        refl
    ; upper6CollectionPromoted =
        false
    ; upper6CollectionPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; collectionBoundary =
        "upper6-18-lane collection consumes canonical u1-u6 receipts only as fail-closed terminal-monitor inputs"
        ∷ "u1 keeps continuum Clay and terminal promotion false"
        ∷ "u2 keeps M1 consumption, strict real SU3, and Hodge/variation promotion false"
        ∷ "u3 separates the local stress-energy tensor construction from W4 and keeps W4/Candidate256 promotion false"
        ∷ "u4 records selected-metric compatibility as local API progress while Levi-Civita/source/terminal authority remains outside this collection"
        ∷ "u5 keeps finite Stone/YM spectral inequality, physical strong continuity, and terminal promotion false"
        ∷ "u6 keeps local H1-H5 evidence, Doplicher-Roberts authority consumption, and Standard Model matching false"
        ∷ "downstream workers may add receipts, but this ledger does not promote the upper6 collection or terminal claim"
        ∷ []
    }

upper6EighteenLaneCollectionKeepsTerminalFalse :
  Upper6EighteenLaneCollectionLedger.terminalClaimPromoted
    canonicalUpper6EighteenLaneCollectionLedger
  ≡
  false
upper6EighteenLaneCollectionKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Gate 8 partial composition/status receipt.
--
-- This pass collects the newly concrete DHR/DR axiom packaging, the scoped
-- DR authority receipt, the DR reconstruction authority receipt, finite
-- Stone/YM bridge, finite GR/W4 bridge, and penguin freeze status into one
-- non-promoting Gate 8 receipt.  It is a status receipt, not a terminal
-- theorem.

data Gate8PartialCompositionStatus : Set where
  gate8PartialCompositionRecordedWithConcreteBlockers :
    Gate8PartialCompositionStatus

canonicalGate8PartialCompositionBlockers :
  List String
canonicalGate8PartialCompositionBlockers =
  "Gate8.term1: DR axiom pack and DR reconstruction authority receipt are inhabited, but DR theorem application, compact gauge reconstruction, category equivalence, arbitrary-sector identity action, and G_DHR ~= G_SM remain false"
  ∷ "Gate8.term2: finite GR/W4 local tensor and selected-metric bridges are threaded, but W4/Candidate256 authority and Levi-Civita/source compatibility remain false"
  ∷ "Gate8.term3: DHR/Yukawa compatibility remains blocked by physical mass, generic eigenbasis, absolute Higgs scale, and non-identity DHR action gaps"
  ∷ "Gate8.term4: finite Stone/YM bridge is recorded, but the finite spectral inequality, physical strong continuity, and terminal Stone/YM promotion remain false"
  ∷ "Penguin freeze: projection artifact and pre-registration tuple are typed, but all freeze authorities are not populated and freezeGateOpen remains false"
  ∷ "Paper7: final product remains non-constructible until the upstream Gate 1-7 and Gate 8 blockers are inhabited"
  ∷ []

record Gate8PartialCompositionStatusReceipt : Setω₆ where
  field
    status :
      Gate8PartialCompositionStatus

    gate8TerminalMonitor :
      Gate8L6TerminalMonitorReceipt

    terminalMonitorClaimPromoted :
      Bool

    terminalMonitorClaimPromotedMatchesMonitor :
      terminalMonitorClaimPromoted
      ≡
      Gate8L6TerminalMonitorReceipt.terminalMonitorClaimPromoted
        gate8TerminalMonitor

    terminalMonitorClaimPromotedIsFalse :
      terminalMonitorClaimPromoted ≡ false

    dhrInternalAxiomReceiptPack :
      Gate6DHR.DHRDRInternalAxiomReceiptPack

    dhrAllFiveInternalAxiomReceiptsTyped :
      Gate6DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTyped
        dhrInternalAxiomReceiptPack
      ≡
      true

    dhrAxiomPackDoesNotReconstructGaugeGroup :
      Gate6DHR.DHRDRInternalAxiomReceiptPack.reconstructsGaugeGroupHere
        dhrInternalAxiomReceiptPack
      ≡
      false

    doplicherRobertsAuthorityReceipt :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt

    drLiteratureTheoremRecorded :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.literatureTheoremRecorded
        doplicherRobertsAuthorityReceipt
      ≡
      true

    drAuthorityConsumableAfterEvidence :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumableAfterEvidence
        doplicherRobertsAuthorityReceipt
      ≡
      true

    drAuthorityConsumedHereIsFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumedHere
        doplicherRobertsAuthorityReceipt
      ≡
      false

    drStandardModelMatchingPromotedIsFalse :
      Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.standardModelMatchingPromoted
        doplicherRobertsAuthorityReceipt
      ≡
      false

    doplicherRobertsReconstructionAuthorityReceipt :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt

    drReconstructionFiveAxiomPackConsumed :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.fiveAxiomPackConsumed
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      true

    drReconstructionTheoremAuthorityRecorded :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.theoremAuthorityRecorded
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      true

    drReconstructionTheoremAppliedHereIsFalse :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.drTheoremAppliedHere
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      false

    drCompactGaugeGroupConstructedHereIsFalse :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.compactGaugeGroupConstructedHere
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      false

    drCategoryEquivalenceToRepGPromotedIsFalse :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.categoryEquivalenceToRepGPromoted
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      false

    drSeparateExactSMMatchEvidenceSuppliedIsFalse :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.separateExactSMMatchEvidenceSupplied
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      false

    drGDHREqualsGSMPromotedIsFalse :
      Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.gDHREqualsGSMPromoted
        doplicherRobertsReconstructionAuthorityReceipt
      ≡
      false

    drReconstructionAuthorityBlockers :
      List Gate6.DHRDoplicherRobertsAuthorityReceiptBlocker

    drReconstructionAuthorityBlockersAreCanonical :
      drReconstructionAuthorityBlockers
      ≡
      Gate6.canonicalDHRDoplicherRobertsAuthorityReceiptBlockers

    drReconstructionAuthorityFirstBlocker :
      Gate6.DHRDoplicherRobertsAuthorityReceiptBlocker

    drReconstructionAuthorityFirstBlockerIsLocalCategoryLawInhabitants :
      drReconstructionAuthorityFirstBlocker
      ≡
      Gate6.blockedByNoLocalDHRCategoryLawInhabitants

    finiteStoneYMBridge :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt

    finiteStoneYMBridgeRecorded :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneYMSpectralBoundBridgeRecorded
        finiteStoneYMBridge
      ≡
      true

    finiteStoneYMSpectralInequalityPromotedIsFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneGeneratorSpectralInequalityPromoted
        finiteStoneYMBridge
      ≡
      false

    finiteStoneYMPhysicalStrongContinuityPromotedIsFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.bridgePhysicalStrongContinuityPromoted
        finiteStoneYMBridge
      ≡
      false

    finiteStoneYMTerminalPromotedIsFalse :
      Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.terminalPromoted
        finiteStoneYMBridge
      ≡
      false

    finiteGRW4ScopeCorrection :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt

    finiteGRW4LocalTensorSeparated :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4
        finiteGRW4ScopeCorrection
      ≡
      true

    finiteGRW4PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesW4
        finiteGRW4ScopeCorrection
      ≡
      false

    finiteGRW4Candidate256PromotionStillFalse :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesCandidate256
        finiteGRW4ScopeCorrection
      ≡
      false

    finiteGRSelectedMetricBridge :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt

    finiteGRSelectedMetricCompatibilityRecorded :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedMetricCompatibilityPromoted
        finiteGRSelectedMetricBridge
      ≡
      true

    finiteGRLeviCivitaPromotionStillFalse :
      Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedConnectionIsLeviCivitaPromoted
        finiteGRSelectedMetricBridge
      ≡
      false

    finiteGRW4UniquenessProgress :
      W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt

    finiteGRW4AuthorityBackedTYMEqualsTGRStillFalse :
      W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt.authorityBackedTYMEqualsTGRPromoted
        finiteGRW4UniquenessProgress
      ≡
      false

    penguinProjectionFreezeStatus :
      PenguinArtifact.PenguinDecayProjectionArtifactRequest

    penguinFreezeAuthoritiesPopulatedIsFalse :
      PenguinArtifact.PenguinDecayProjectionArtifactRequest.allFreezeAuthoritiesPopulated
        penguinProjectionFreezeStatus
      ≡
      false

    penguinFreezeGateOpenIsFalse :
      PenguinArtifact.PenguinDecayProjectionArtifactRequest.freezeGateOpen
        penguinProjectionFreezeStatus
      ≡
      false

    penguinPromotionConstructedHereIsFalse :
      PenguinArtifact.PenguinDecayProjectionArtifactRequest.promotionConstructedHere
        penguinProjectionFreezeStatus
      ≡
      false

    penguinFreezeAuthorityPopulationGaps :
      List PenguinArtifact.PenguinFreezeAuthorityPopulationGap

    penguinFreezeAuthorityPopulationGapsAreCanonical :
      penguinFreezeAuthorityPopulationGaps
      ≡
      PenguinArtifact.canonicalPenguinFreezeAuthorityPopulationGaps

    paper7FinalProductReceipt :
      Paper7FinalProductReceipt

    paper7TerminalClaimPromotedIsFalse :
      Paper7FinalProductReceipt.terminalClaimPromoted
        paper7FinalProductReceipt
      ≡
      false

    paper7Constructible :
      Bool

    paper7ConstructibleIsFalse :
      paper7Constructible ≡ false

    exactRemainingGate8Blockers :
      List String

    exactRemainingGate8BlockersAreCanonical :
      exactRemainingGate8Blockers
      ≡
      canonicalGate8PartialCompositionBlockers

    gate8PartialCompositionPromoted :
      Bool

    gate8PartialCompositionPromotedIsFalse :
      gate8PartialCompositionPromoted ≡ false

    statusBoundary :
      List String

canonicalGate8PartialCompositionStatusReceipt :
  Gate8PartialCompositionStatusReceipt
canonicalGate8PartialCompositionStatusReceipt =
  record
    { status =
        gate8PartialCompositionRecordedWithConcreteBlockers
    ; gate8TerminalMonitor =
        canonicalGate8L6TerminalMonitorReceipt
    ; terminalMonitorClaimPromoted =
        Gate8L6TerminalMonitorReceipt.terminalMonitorClaimPromoted
          canonicalGate8L6TerminalMonitorReceipt
    ; terminalMonitorClaimPromotedMatchesMonitor =
        refl
    ; terminalMonitorClaimPromotedIsFalse =
        gate8L6TerminalMonitorKeepsTerminalFalse
    ; dhrInternalAxiomReceiptPack =
        Gate6DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; dhrAllFiveInternalAxiomReceiptsTyped =
        Gate6DHR.DHRDRInternalAxiomReceiptPack.allFiveInternalAxiomReceiptsTypedIsTrue
          Gate6DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; dhrAxiomPackDoesNotReconstructGaugeGroup =
        Gate6DHR.DHRDRInternalAxiomReceiptPack.reconstructsGaugeGroupHereIsFalse
          Gate6DHR.canonicalDHRDRInternalAxiomReceiptPack
    ; doplicherRobertsAuthorityReceipt =
        Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; drLiteratureTheoremRecorded =
        Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.literatureTheoremRecordedIsTrue
          Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; drAuthorityConsumableAfterEvidence =
        Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumableAfterEvidenceIsTrue
          Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; drAuthorityConsumedHereIsFalse =
        Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.drAuthorityConsumedHereIsFalse
          Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; drStandardModelMatchingPromotedIsFalse =
        Gate6DHR.DHRDoplicherRobertsScopingCorrectionReceipt.standardModelMatchingPromotedIsFalse
          Gate6DHR.canonicalDHRDoplicherRobertsScopingCorrectionReceipt
    ; doplicherRobertsReconstructionAuthorityReceipt =
        Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionFiveAxiomPackConsumed =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.fiveAxiomPackConsumedIsTrue
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionTheoremAuthorityRecorded =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.theoremAuthorityRecordedIsTrue
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionTheoremAppliedHereIsFalse =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.drTheoremAppliedHereIsFalse
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drCompactGaugeGroupConstructedHereIsFalse =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.compactGaugeGroupConstructedHereIsFalse
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drCategoryEquivalenceToRepGPromotedIsFalse =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.categoryEquivalenceToRepGPromotedIsFalse
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drSeparateExactSMMatchEvidenceSuppliedIsFalse =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.separateExactSMMatchEvidenceSuppliedIsFalse
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drGDHREqualsGSMPromotedIsFalse =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.gDHREqualsGSMPromotedIsFalse
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionAuthorityBlockers =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.blockers
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionAuthorityBlockersAreCanonical =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.blockersAreCanonical
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionAuthorityFirstBlocker =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.firstBlocker
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; drReconstructionAuthorityFirstBlockerIsLocalCategoryLawInhabitants =
        Gate6.DHRDoplicherRobertsReconstructionAuthorityReceipt.firstBlockerIsLocalCategoryLawInhabitants
          Gate6.canonicalDHRDoplicherRobertsReconstructionAuthorityReceipt
    ; finiteStoneYMBridge =
        Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; finiteStoneYMBridgeRecorded =
        Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneYMSpectralBoundBridgeRecorded-v
          Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; finiteStoneYMSpectralInequalityPromotedIsFalse =
        Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.finiteStoneGeneratorSpectralInequalityPromoted-v
          Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; finiteStoneYMPhysicalStrongContinuityPromotedIsFalse =
        Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.bridgePhysicalStrongContinuityPromoted-v
          Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; finiteStoneYMTerminalPromotedIsFalse =
        Gate5.U5FiniteStoneYMSpectralBoundBridgeReceipt.terminalPromoted-v
          Gate5.canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt
    ; finiteGRW4ScopeCorrection =
        W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; finiteGRW4LocalTensorSeparated =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4IsTrue
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; finiteGRW4PromotionStillFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesW4IsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; finiteGRW4Candidate256PromotionStillFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesCandidate256IsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; finiteGRSelectedMetricBridge =
        Gate4GR.canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
    ; finiteGRSelectedMetricCompatibilityRecorded =
        Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedMetricCompatibilityPromotedIsTrue
          Gate4GR.canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
    ; finiteGRLeviCivitaPromotionStillFalse =
        Gate4GR.GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedConnectionIsLeviCivitaPromotedIsFalse
          Gate4GR.canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
    ; finiteGRW4UniquenessProgress =
        W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt
    ; finiteGRW4AuthorityBackedTYMEqualsTGRStillFalse =
        W4Stress.W4YMGRStressEnergyUniquenessProgressReceipt.authorityBackedTYMEqualsTGRPromotedIsFalse
          W4Stress.canonicalW4YMGRStressEnergyUniquenessProgressReceipt
    ; penguinProjectionFreezeStatus =
        PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; penguinFreezeAuthoritiesPopulatedIsFalse =
        PenguinArtifact.PenguinDecayProjectionArtifactRequest.allFreezeAuthoritiesPopulatedIsFalse
          PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; penguinFreezeGateOpenIsFalse =
        PenguinArtifact.PenguinDecayProjectionArtifactRequest.freezeGateOpenIsFalse
          PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; penguinPromotionConstructedHereIsFalse =
        PenguinArtifact.PenguinDecayProjectionArtifactRequest.promotionConstructedHereIsFalse
          PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; penguinFreezeAuthorityPopulationGaps =
        PenguinArtifact.PenguinDecayProjectionArtifactRequest.freezeAuthorityPopulationGaps
          PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; penguinFreezeAuthorityPopulationGapsAreCanonical =
        PenguinArtifact.PenguinDecayProjectionArtifactRequest.freezeAuthorityPopulationGapsAreCanonical
          PenguinArtifact.canonicalPenguinDecayProjectionArtifactRequest
    ; paper7FinalProductReceipt =
        canonicalPaper7FinalProductReceipt
    ; paper7TerminalClaimPromotedIsFalse =
        Paper7FinalProductReceipt.terminalClaimPromotedIsFalse
          canonicalPaper7FinalProductReceipt
    ; paper7Constructible =
        false
    ; paper7ConstructibleIsFalse =
        refl
    ; exactRemainingGate8Blockers =
        canonicalGate8PartialCompositionBlockers
    ; exactRemainingGate8BlockersAreCanonical =
        refl
    ; gate8PartialCompositionPromoted =
        false
    ; gate8PartialCompositionPromotedIsFalse =
        refl
    ; statusBoundary =
        "Gate 8 partial composition consumes the concrete DHR internal axiom pack, not a placeholder"
        ∷ "Doplicher-Roberts literature authority is recorded and consumable after evidence, but drAuthorityConsumedHere remains false"
        ∷ "Doplicher-Roberts reconstruction authority is consumed as the canonical Gate 6 receipt while DR theorem application, compact gauge reconstruction, category equivalence to Rep(G), and G_DHR ~= G_SM remain false"
        ∷ "The exact DR reconstruction blockers are canonical: no local DHR category law inhabitants, no DR theorem application, no compact gauge-group construction, and no separate exact SM match evidence"
        ∷ "Finite Stone/YM and finite GR/W4 bridge receipts are threaded with their exact false promotion bits"
        ∷ "Penguin projection freeze status is consumed from the canonical artifact request; freezeGateOpen remains false"
        ∷ "terminalMonitorClaimPromoted is read from canonicalGate8L6TerminalMonitorReceipt and remains false"
        ∷ "Paper7Constructible is fixed false because canonicalPaper7FinalProductReceipt remains blocked on upstream receipts"
        ∷ []
    }

gate8PartialCompositionTerminalMonitorStillFalse :
  Gate8PartialCompositionStatusReceipt.terminalMonitorClaimPromoted
    canonicalGate8PartialCompositionStatusReceipt
  ≡
  false
gate8PartialCompositionTerminalMonitorStillFalse =
  gate8L6TerminalMonitorKeepsTerminalFalse

gate8PartialCompositionKeepsPaper7NonConstructible :
  Gate8PartialCompositionStatusReceipt.paper7Constructible
    canonicalGate8PartialCompositionStatusReceipt
  ≡
  false
gate8PartialCompositionKeepsPaper7NonConstructible =
  refl

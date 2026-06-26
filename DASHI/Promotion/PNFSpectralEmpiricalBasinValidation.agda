module DASHI.Promotion.PNFSpectralEmpiricalBasinValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Interop.PNFBraidTransportField as Braid
import DASHI.Interop.PNFSpectralFieldArchitectureReceipt as Arch
import DASHI.Promotion.PNFSpectralTradingSignalBoundary as Trading
open import DASHI.Core.FiniteReceiptList using (listCount)

------------------------------------------------------------------------
-- PNF spectral empirical basin validation.
--
-- This module records the empirical/trading-validation basin surface for
-- sections 24--27 of the working formalism.  It is deliberately
-- fail-closed: feature windows, outcome carriers, basin proximity rows,
-- separator candidates, MDL/cost discipline, holdout gates, and stress
-- gates can be named and linked to receipts, but no empirical adequacy,
-- market prediction, financial advice, production trading authority,
-- manual semantic labelling authority, or threshold-fishing authority is
-- promoted here.

------------------------------------------------------------------------
-- Field-window features and outcome carriers.

data FieldWindowKind : Set where
  eventAlignedFieldWindow :
    FieldWindowKind
  trailingReplayFieldWindow :
    FieldWindowKind
  forwardOutcomeFieldWindow :
    FieldWindowKind
  costStressFieldWindow :
    FieldWindowKind
  holdoutFieldWindow :
    FieldWindowKind
  searchAuditFieldWindow :
    FieldWindowKind

canonicalFieldWindowKinds : List FieldWindowKind
canonicalFieldWindowKinds =
  eventAlignedFieldWindow
  ∷ trailingReplayFieldWindow
  ∷ forwardOutcomeFieldWindow
  ∷ costStressFieldWindow
  ∷ holdoutFieldWindow
  ∷ searchAuditFieldWindow
  ∷ []

data FieldWindowFeatureKind : Set where
  spectralRadiusFeature :
    FieldWindowFeatureKind
  braidCurvatureFeature :
    FieldWindowFeatureKind
  residualLaplacianEnergyFeature :
    FieldWindowFeatureKind
  supportDeformationFeature :
    FieldWindowFeatureKind
  sourceRevisionDriftFeature :
    FieldWindowFeatureKind
  costAdjustedSlippageFeature :
    FieldWindowFeatureKind
  searchMultiplicityFeature :
    FieldWindowFeatureKind

canonicalFieldWindowFeatureKinds :
  List FieldWindowFeatureKind
canonicalFieldWindowFeatureKinds =
  spectralRadiusFeature
  ∷ braidCurvatureFeature
  ∷ residualLaplacianEnergyFeature
  ∷ supportDeformationFeature
  ∷ sourceRevisionDriftFeature
  ∷ costAdjustedSlippageFeature
  ∷ searchMultiplicityFeature
  ∷ []

data OutcomeCarrierKind : Set where
  adverseOutcomeCarrier :
    OutcomeCarrierKind
  favorableOutcomeCarrier :
    OutcomeCarrierKind
  flatOutcomeCarrier :
    OutcomeCarrierKind
  censoredOutcomeCarrier :
    OutcomeCarrierKind
  unknownOutcomeCarrier :
    OutcomeCarrierKind

canonicalOutcomeCarrierKinds :
  List OutcomeCarrierKind
canonicalOutcomeCarrierKinds =
  adverseOutcomeCarrier
  ∷ favorableOutcomeCarrier
  ∷ flatOutcomeCarrier
  ∷ censoredOutcomeCarrier
  ∷ unknownOutcomeCarrier
  ∷ []

record FieldWindowFeature : Set where
  field
    featureId :
      String
    windowKind :
      FieldWindowKind
    featureKind :
      FieldWindowFeatureKind
    sourceSurface :
      Trading.MarketInformationSurface
    braidTransportReceipt :
      Braid.PNFBraidTransportFieldReceipt
    featureArchitectureReceipt :
      Arch.PNFSpectralFieldArchitectureReceipt
    windowLabel :
      String
    featureDigest :
      String
    featureCandidateOnly :
      Bool
    featureCandidateOnlyIsTrue :
      featureCandidateOnly ≡ true
    featureEmpiricalClaim :
      Bool
    featureEmpiricalClaimIsFalse :
      featureEmpiricalClaim ≡ false

open FieldWindowFeature public

record OutcomeCarrier : Set where
  field
    outcomeCarrierId :
      String
    outcomeKind :
      OutcomeCarrierKind
    outcomeWindow :
      FieldWindowKind
    linkedSignalProposal :
      Trading.TradingSignalProposal
    outcomeDigest :
      String
    outcomeReceiptId :
      String
    outcomeObserved :
      Bool
    outcomeObservedIsFalseByDefault :
      outcomeObserved ≡ false
    realizedProfitClaim :
      Bool
    realizedProfitClaimIsFalse :
      realizedProfitClaim ≡ false
    outcomeManualSemanticLabel :
      Bool
    outcomeManualSemanticLabelIsFalse :
      outcomeManualSemanticLabel ≡ false

open OutcomeCarrier public

canonicalFieldWindowFeature :
  FieldWindowFeature
canonicalFieldWindowFeature =
  record
    { featureId =
        "canonical field-window feature candidate"
    ; windowKind =
        eventAlignedFieldWindow
    ; featureKind =
        braidCurvatureFeature
    ; sourceSurface =
        Trading.receiptBackedReplaySurface
    ; braidTransportReceipt =
        Braid.canonicalPNFBraidTransportFieldReceipt
    ; featureArchitectureReceipt =
        Arch.canonicalPNFSpectralFieldArchitectureReceipt
    ; windowLabel =
        "event-aligned spectral braid window pending validation"
    ; featureDigest =
        "feature digest pending replay receipt"
    ; featureCandidateOnly =
        true
    ; featureCandidateOnlyIsTrue =
        refl
    ; featureEmpiricalClaim =
        false
    ; featureEmpiricalClaimIsFalse =
        refl
    }

canonicalOutcomeCarrier :
  OutcomeCarrier
canonicalOutcomeCarrier =
  record
    { outcomeCarrierId =
        "canonical outcome carrier placeholder"
    ; outcomeKind =
        unknownOutcomeCarrier
    ; outcomeWindow =
        forwardOutcomeFieldWindow
    ; linkedSignalProposal =
        Trading.canonicalTradingSignalProposal
    ; outcomeDigest =
        "outcome digest unavailable without holdout replay"
    ; outcomeReceiptId =
        "missing outcome receipt"
    ; outcomeObserved =
        false
    ; outcomeObservedIsFalseByDefault =
        refl
    ; realizedProfitClaim =
        false
    ; realizedProfitClaimIsFalse =
        refl
    ; outcomeManualSemanticLabel =
        false
    ; outcomeManualSemanticLabelIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Good/bad/tail basin proximity rows.

data BasinRegion : Set where
  goodBasinRegion :
    BasinRegion
  badBasinRegion :
    BasinRegion
  tailBasinRegion :
    BasinRegion
  unresolvedBasinRegion :
    BasinRegion

data BasinProximityBand : Set where
  nearProximityBand :
    BasinProximityBand
  boundaryProximityBand :
    BasinProximityBand
  farProximityBand :
    BasinProximityBand
  tailRiskProximityBand :
    BasinProximityBand
  unknownProximityBand :
    BasinProximityBand

record BasinProximityRow : Set where
  field
    basinRowId :
      String
    basinRegion :
      BasinRegion
    proximityBand :
      BasinProximityBand
    rowFeature :
      FieldWindowFeature
    rowOutcomeCarrier :
      OutcomeCarrier
    referenceNeighborhood :
      Trading.HistoricalBraidNeighborhood
    rowDistanceDigest :
      String
    rowReplayReceiptId :
      String
    rowIsCandidate :
      Bool
    rowIsCandidateIsTrue :
      rowIsCandidate ≡ true
    rowOutcomeAsserted :
      Bool
    rowOutcomeAssertedIsFalse :
      rowOutcomeAsserted ≡ false
    rowAdequacyPromoted :
      Bool
    rowAdequacyPromotedIsFalse :
      rowAdequacyPromoted ≡ false

open BasinProximityRow public

canonicalGoodBasinProximityRow :
  BasinProximityRow
canonicalGoodBasinProximityRow =
  record
    { basinRowId =
        "canonical good-basin proximity row"
    ; basinRegion =
        goodBasinRegion
    ; proximityBand =
        nearProximityBand
    ; rowFeature =
        canonicalFieldWindowFeature
    ; rowOutcomeCarrier =
        canonicalOutcomeCarrier
    ; referenceNeighborhood =
        Trading.canonicalFavorableBraidNeighborhood
    ; rowDistanceDigest =
        "good-basin distance digest pending holdout replay"
    ; rowReplayReceiptId =
        "missing good-basin replay receipt"
    ; rowIsCandidate =
        true
    ; rowIsCandidateIsTrue =
        refl
    ; rowOutcomeAsserted =
        false
    ; rowOutcomeAssertedIsFalse =
        refl
    ; rowAdequacyPromoted =
        false
    ; rowAdequacyPromotedIsFalse =
        refl
    }

canonicalBadBasinProximityRow :
  BasinProximityRow
canonicalBadBasinProximityRow =
  record
    { basinRowId =
        "canonical bad-basin proximity row"
    ; basinRegion =
        badBasinRegion
    ; proximityBand =
        boundaryProximityBand
    ; rowFeature =
        canonicalFieldWindowFeature
    ; rowOutcomeCarrier =
        canonicalOutcomeCarrier
    ; referenceNeighborhood =
        Trading.canonicalAdverseBraidNeighborhood
    ; rowDistanceDigest =
        "bad-basin distance digest pending holdout replay"
    ; rowReplayReceiptId =
        "missing bad-basin replay receipt"
    ; rowIsCandidate =
        true
    ; rowIsCandidateIsTrue =
        refl
    ; rowOutcomeAsserted =
        false
    ; rowOutcomeAssertedIsFalse =
        refl
    ; rowAdequacyPromoted =
        false
    ; rowAdequacyPromotedIsFalse =
        refl
    }

canonicalTailBasinProximityRow :
  BasinProximityRow
canonicalTailBasinProximityRow =
  record
    { basinRowId =
        "canonical tail-basin proximity row"
    ; basinRegion =
        tailBasinRegion
    ; proximityBand =
        tailRiskProximityBand
    ; rowFeature =
        canonicalFieldWindowFeature
    ; rowOutcomeCarrier =
        canonicalOutcomeCarrier
    ; referenceNeighborhood =
        Trading.canonicalAdverseBraidNeighborhood
    ; rowDistanceDigest =
        "tail-basin distance digest pending tail stress replay"
    ; rowReplayReceiptId =
        "missing tail-basin replay receipt"
    ; rowIsCandidate =
        true
    ; rowIsCandidateIsTrue =
        refl
    ; rowOutcomeAsserted =
        false
    ; rowOutcomeAssertedIsFalse =
        refl
    ; rowAdequacyPromoted =
        false
    ; rowAdequacyPromotedIsFalse =
        refl
    }

canonicalBasinRows :
  List BasinProximityRow
canonicalBasinRows =
  canonicalGoodBasinProximityRow
  ∷ canonicalBadBasinProximityRow
  ∷ canonicalTailBasinProximityRow
  ∷ []

------------------------------------------------------------------------
-- Stronger trading-side product: three-layer corroboration, still
-- candidate-only pending holdout/replay.

record TradingSideProductCandidateRow : Set where
  field
    tradingSideProductRowId :
      String
    basinSpectralProximityLayer :
      BasinProximityRow
    basinSpectralProximityLayerIsCanonical :
      basinSpectralProximityLayer ≡ canonicalGoodBasinProximityRow
    braidSignatureReferenceNeighborhoodLayer :
      Braid.BraidSignature
    braidSignatureReferenceNeighborhoodLayerIsCanonical :
      braidSignatureReferenceNeighborhoodLayer
      ≡
      Braid.canonicalNewsBraidSignature
    referenceNeighborhoodLayer :
      Trading.HistoricalBraidNeighborhood
    referenceNeighborhoodLayerIsCanonical :
      referenceNeighborhoodLayer ≡ Trading.canonicalFavorableBraidNeighborhood
    residualReceiptCorroborationLayer :
      Arch.PNFSpectralFieldArchitectureReceipt
    residualReceiptCorroborationLayerIsCanonical :
      residualReceiptCorroborationLayer
      ≡
      Arch.canonicalPNFSpectralFieldArchitectureReceipt
    tradingBoundaryCorroborationLayer :
      Trading.TradingSignalProposal
    tradingBoundaryCorroborationLayerIsCanonical :
      tradingBoundaryCorroborationLayer
      ≡
      Trading.canonicalTradingSignalProposal
    threeCorroborationLayersNamed :
      Bool
    threeCorroborationLayersNamedIsTrue :
      threeCorroborationLayersNamed ≡ true
    pendingHoldoutReplay :
      Bool
    pendingHoldoutReplayIsTrue :
      pendingHoldoutReplay ≡ true
    candidateOnlyPendingHoldoutReplay :
      Bool
    candidateOnlyPendingHoldoutReplayIsTrue :
      candidateOnlyPendingHoldoutReplay ≡ true
    empiricalAdequacyGranted :
      Bool
    empiricalAdequacyGrantedIsFalse :
      empiricalAdequacyGranted ≡ false
    marketPredictionAuthorityGranted :
      Bool
    marketPredictionAuthorityGrantedIsFalse :
      marketPredictionAuthorityGranted ≡ false
    financialAdviceAuthorityGranted :
      Bool
    financialAdviceAuthorityGrantedIsFalse :
      financialAdviceAuthorityGranted ≡ false
    productionTradingAuthorityGranted :
      Bool
    productionTradingAuthorityGrantedIsFalse :
      productionTradingAuthorityGranted ≡ false

open TradingSideProductCandidateRow public

canonicalTradingSideProductCandidateRow :
  TradingSideProductCandidateRow
canonicalTradingSideProductCandidateRow =
  record
    { tradingSideProductRowId =
        "canonical trading-side product candidate: basin plus braid neighborhood plus residual receipt corroboration"
    ; basinSpectralProximityLayer =
        canonicalGoodBasinProximityRow
    ; basinSpectralProximityLayerIsCanonical =
        refl
    ; braidSignatureReferenceNeighborhoodLayer =
        Braid.canonicalNewsBraidSignature
    ; braidSignatureReferenceNeighborhoodLayerIsCanonical =
        refl
    ; referenceNeighborhoodLayer =
        Trading.canonicalFavorableBraidNeighborhood
    ; referenceNeighborhoodLayerIsCanonical =
        refl
    ; residualReceiptCorroborationLayer =
        Arch.canonicalPNFSpectralFieldArchitectureReceipt
    ; residualReceiptCorroborationLayerIsCanonical =
        refl
    ; tradingBoundaryCorroborationLayer =
        Trading.canonicalTradingSignalProposal
    ; tradingBoundaryCorroborationLayerIsCanonical =
        refl
    ; threeCorroborationLayersNamed =
        true
    ; threeCorroborationLayersNamedIsTrue =
        refl
    ; pendingHoldoutReplay =
        true
    ; pendingHoldoutReplayIsTrue =
        refl
    ; candidateOnlyPendingHoldoutReplay =
        true
    ; candidateOnlyPendingHoldoutReplayIsTrue =
        refl
    ; empiricalAdequacyGranted =
        false
    ; empiricalAdequacyGrantedIsFalse =
        refl
    ; marketPredictionAuthorityGranted =
        false
    ; marketPredictionAuthorityGrantedIsFalse =
        refl
    ; financialAdviceAuthorityGranted =
        false
    ; financialAdviceAuthorityGrantedIsFalse =
        refl
    ; productionTradingAuthorityGranted =
        false
    ; productionTradingAuthorityGrantedIsFalse =
        refl
    }

canonicalTradingSideProductCandidateRows :
  List TradingSideProductCandidateRow
canonicalTradingSideProductCandidateRows =
  canonicalTradingSideProductCandidateRow ∷ []

------------------------------------------------------------------------
-- Separator candidate lifecycle and collapse/exhaustion flags.

data SeparatorLifecycleState : Set where
  separatorProposed :
    SeparatorLifecycleState
  separatorFeatureBound :
    SeparatorLifecycleState
  separatorHoldoutQueued :
    SeparatorLifecycleState
  separatorCostStressQueued :
    SeparatorLifecycleState
  separatorRejected :
    SeparatorLifecycleState
  separatorExhausted :
    SeparatorLifecycleState

data CollapseFlag : Set where
  noCollapseObserved :
    CollapseFlag
  basinCollapseCandidate :
    CollapseFlag
  separatorCollapseCandidate :
    CollapseFlag
  costCollapseCandidate :
    CollapseFlag
  searchCollapseCandidate :
    CollapseFlag

data ExhaustionFlag : Set where
  noExhaustionObserved :
    ExhaustionFlag
  featureBudgetExhausted :
    ExhaustionFlag
  holdoutBudgetExhausted :
    ExhaustionFlag
  costBudgetExhausted :
    ExhaustionFlag
  searchBudgetExhausted :
    ExhaustionFlag

record SeparatorCandidateLifecycle : Set where
  field
    separatorCandidateId :
      String
    separatorState :
      SeparatorLifecycleState
    separatorFeature :
      FieldWindowFeature
    separatorGoodRow :
      BasinProximityRow
    separatorBadRow :
      BasinProximityRow
    separatorTailRow :
      BasinProximityRow
    separatorCollapseFlag :
      CollapseFlag
    separatorExhaustionFlag :
      ExhaustionFlag
    separatorRuleDigest :
      String
    separatorThresholdDigest :
      String
    separatorCandidateOnly :
      Bool
    separatorCandidateOnlyIsTrue :
      separatorCandidateOnly ≡ true
    separatorAccepted :
      Bool
    separatorAcceptedIsFalse :
      separatorAccepted ≡ false
    separatorPredictiveClaim :
      Bool
    separatorPredictiveClaimIsFalse :
      separatorPredictiveClaim ≡ false

open SeparatorCandidateLifecycle public

canonicalSeparatorCandidateLifecycle :
  SeparatorCandidateLifecycle
canonicalSeparatorCandidateLifecycle =
  record
    { separatorCandidateId =
        "canonical basin separator candidate"
    ; separatorState =
        separatorProposed
    ; separatorFeature =
        canonicalFieldWindowFeature
    ; separatorGoodRow =
        canonicalGoodBasinProximityRow
    ; separatorBadRow =
        canonicalBadBasinProximityRow
    ; separatorTailRow =
        canonicalTailBasinProximityRow
    ; separatorCollapseFlag =
        noCollapseObserved
    ; separatorExhaustionFlag =
        noExhaustionObserved
    ; separatorRuleDigest =
        "candidate separator rule pending validation"
    ; separatorThresholdDigest =
        "threshold digest cannot be selected by fishing"
    ; separatorCandidateOnly =
        true
    ; separatorCandidateOnlyIsTrue =
        refl
    ; separatorAccepted =
        false
    ; separatorAcceptedIsFalse =
        refl
    ; separatorPredictiveClaim =
        false
    ; separatorPredictiveClaimIsFalse =
        refl
    }

------------------------------------------------------------------------
-- MDL/cost discipline and validation gates.

data MDLCostComponent : Set where
  featureEncodingCost :
    MDLCostComponent
  basinEncodingCost :
    MDLCostComponent
  separatorRuleEncodingCost :
    MDLCostComponent
  slippageTransactionCost :
    MDLCostComponent
  searchMultiplicityCost :
    MDLCostComponent
  governanceReviewCost :
    MDLCostComponent

canonicalMDLCostComponents :
  List MDLCostComponent
canonicalMDLCostComponents =
  featureEncodingCost
  ∷ basinEncodingCost
  ∷ separatorRuleEncodingCost
  ∷ slippageTransactionCost
  ∷ searchMultiplicityCost
  ∷ governanceReviewCost
  ∷ []

record MDLCostDisciplineReceipt : Set where
  field
    mdlDisciplineId :
      String
    mdlCostComponents :
      List MDLCostComponent
    mdlCostComponentsAreCanonical :
      mdlCostComponents ≡ canonicalMDLCostComponents
    mdlCostBudgetDigest :
      String
    mdlCostPenaltyDigest :
      String
    mdlComplexityPenaltyRequired :
      Bool
    mdlComplexityPenaltyRequiredIsTrue :
      mdlComplexityPenaltyRequired ≡ true
    mdlTradingCostsRequired :
      Bool
    mdlTradingCostsRequiredIsTrue :
      mdlTradingCostsRequired ≡ true
    mdlSearchCostRequired :
      Bool
    mdlSearchCostRequiredIsTrue :
      mdlSearchCostRequired ≡ true
    mdlCostReceiptSupplied :
      Bool
    mdlCostReceiptSuppliedIsFalse :
      mdlCostReceiptSupplied ≡ false
    mdlCostAdequacyPromoted :
      Bool
    mdlCostAdequacyPromotedIsFalse :
      mdlCostAdequacyPromoted ≡ false

open MDLCostDisciplineReceipt public

canonicalMDLCostDisciplineReceipt :
  MDLCostDisciplineReceipt
canonicalMDLCostDisciplineReceipt =
  record
    { mdlDisciplineId =
        "canonical MDL and cost discipline"
    ; mdlCostComponents =
        canonicalMDLCostComponents
    ; mdlCostComponentsAreCanonical =
        refl
    ; mdlCostBudgetDigest =
        "feature, separator, slippage, search, and review costs required"
    ; mdlCostPenaltyDigest =
        "cost penalty digest pending receipt"
    ; mdlComplexityPenaltyRequired =
        true
    ; mdlComplexityPenaltyRequiredIsTrue =
        refl
    ; mdlTradingCostsRequired =
        true
    ; mdlTradingCostsRequiredIsTrue =
        refl
    ; mdlSearchCostRequired =
        true
    ; mdlSearchCostRequiredIsTrue =
        refl
    ; mdlCostReceiptSupplied =
        false
    ; mdlCostReceiptSuppliedIsFalse =
        refl
    ; mdlCostAdequacyPromoted =
        false
    ; mdlCostAdequacyPromotedIsFalse =
        refl
    }

data EmpiricalValidationGate : Set where
  resolverReceiptGate :
    EmpiricalValidationGate
  selectorReceiptGate :
    EmpiricalValidationGate
  itirReplayReceiptGate :
    EmpiricalValidationGate
  outcomeReceiptGate :
    EmpiricalValidationGate
  holdoutGate :
    EmpiricalValidationGate
  costStressGate :
    EmpiricalValidationGate
  searchCostGate :
    EmpiricalValidationGate
  mdlComplexityGate :
    EmpiricalValidationGate
  tailBasinGate :
    EmpiricalValidationGate
  antiThresholdFishingGate :
    EmpiricalValidationGate

canonicalEmpiricalValidationGates :
  List EmpiricalValidationGate
canonicalEmpiricalValidationGates =
  resolverReceiptGate
  ∷ selectorReceiptGate
  ∷ itirReplayReceiptGate
  ∷ outcomeReceiptGate
  ∷ holdoutGate
  ∷ costStressGate
  ∷ searchCostGate
  ∷ mdlComplexityGate
  ∷ tailBasinGate
  ∷ antiThresholdFishingGate
  ∷ []

record HoldoutCostStressSearchGateReceipt : Set where
  field
    validationGateId :
      String
    validationGates :
      List EmpiricalValidationGate
    validationGatesAreCanonical :
      validationGates ≡ canonicalEmpiricalValidationGates
    holdoutReceiptId :
      String
    costStressReceiptId :
      String
    searchCostReceiptId :
      String
    holdoutRequired :
      Bool
    holdoutRequiredIsTrue :
      holdoutRequired ≡ true
    costStressRequired :
      Bool
    costStressRequiredIsTrue :
      costStressRequired ≡ true
    searchCostRequired :
      Bool
    searchCostRequiredIsTrue :
      searchCostRequired ≡ true
    holdoutPassed :
      Bool
    holdoutPassedIsFalse :
      holdoutPassed ≡ false
    costStressPassed :
      Bool
    costStressPassedIsFalse :
      costStressPassed ≡ false
    searchCostPassed :
      Bool
    searchCostPassedIsFalse :
      searchCostPassed ≡ false
    thresholdFishingBlocked :
      Bool
    thresholdFishingBlockedIsTrue :
      thresholdFishingBlocked ≡ true
    manualSemanticLabelsBlocked :
      Bool
    manualSemanticLabelsBlockedIsTrue :
      manualSemanticLabelsBlocked ≡ true

open HoldoutCostStressSearchGateReceipt public

canonicalHoldoutCostStressSearchGateReceipt :
  HoldoutCostStressSearchGateReceipt
canonicalHoldoutCostStressSearchGateReceipt =
  record
    { validationGateId =
        "canonical holdout cost-stress search-cost gate"
    ; validationGates =
        canonicalEmpiricalValidationGates
    ; validationGatesAreCanonical =
        refl
    ; holdoutReceiptId =
        "missing holdout receipt"
    ; costStressReceiptId =
        "missing cost stress receipt"
    ; searchCostReceiptId =
        "missing search cost receipt"
    ; holdoutRequired =
        true
    ; holdoutRequiredIsTrue =
        refl
    ; costStressRequired =
        true
    ; costStressRequiredIsTrue =
        refl
    ; searchCostRequired =
        true
    ; searchCostRequiredIsTrue =
        refl
    ; holdoutPassed =
        false
    ; holdoutPassedIsFalse =
        refl
    ; costStressPassed =
        false
    ; costStressPassedIsFalse =
        refl
    ; searchCostPassed =
        false
    ; searchCostPassedIsFalse =
        refl
    ; thresholdFishingBlocked =
        true
    ; thresholdFishingBlockedIsTrue =
        refl
    ; manualSemanticLabelsBlocked =
        true
    ; manualSemanticLabelsBlockedIsTrue =
        refl
    }

------------------------------------------------------------------------
-- Explicit false gates.

data EmpiricalBasinFalseGate : Set where
  empiricalAdequacyFalseGate :
    EmpiricalBasinFalseGate
  financialAdviceFalseGate :
    EmpiricalBasinFalseGate
  productionTradingFalseGate :
    EmpiricalBasinFalseGate
  marketPredictionFalseGate :
    EmpiricalBasinFalseGate
  manualSemanticLabelsFalseGate :
    EmpiricalBasinFalseGate
  thresholdFishingFalseGate :
    EmpiricalBasinFalseGate

canonicalEmpiricalBasinFalseGates :
  List EmpiricalBasinFalseGate
canonicalEmpiricalBasinFalseGates =
  empiricalAdequacyFalseGate
  ∷ financialAdviceFalseGate
  ∷ productionTradingFalseGate
  ∷ marketPredictionFalseGate
  ∷ manualSemanticLabelsFalseGate
  ∷ thresholdFishingFalseGate
  ∷ []

data EmpiricalBasinPromotion : Set where

empiricalBasinPromotionImpossible :
  EmpiricalBasinPromotion →
  ⊥
empiricalBasinPromotionImpossible ()

record EmpiricalBasinFalseGateReceipt : Set where
  field
    falseGateId :
      String
    falseGates :
      List EmpiricalBasinFalseGate
    falseGatesAreCanonical :
      falseGates ≡ canonicalEmpiricalBasinFalseGates
    empiricalAdequacy :
      Bool
    empiricalAdequacyIsFalse :
      empiricalAdequacy ≡ false
    financialAdviceAuthority :
      Bool
    financialAdviceAuthorityIsFalse :
      financialAdviceAuthority ≡ false
    productionTradingAuthority :
      Bool
    productionTradingAuthorityIsFalse :
      productionTradingAuthority ≡ false
    marketPredictionAuthority :
      Bool
    marketPredictionAuthorityIsFalse :
      marketPredictionAuthority ≡ false
    manualSemanticLabelAuthority :
      Bool
    manualSemanticLabelAuthorityIsFalse :
      manualSemanticLabelAuthority ≡ false
    thresholdFishingAuthority :
      Bool
    thresholdFishingAuthorityIsFalse :
      thresholdFishingAuthority ≡ false
    promoted :
      Bool
    promotedIsFalse :
      promoted ≡ false
    promotionFlags :
      List EmpiricalBasinPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotion :
      EmpiricalBasinPromotion → ⊥

open EmpiricalBasinFalseGateReceipt public

canonicalEmpiricalBasinFalseGateReceipt :
  EmpiricalBasinFalseGateReceipt
canonicalEmpiricalBasinFalseGateReceipt =
  record
    { falseGateId =
        "canonical empirical basin false gates"
    ; falseGates =
        canonicalEmpiricalBasinFalseGates
    ; falseGatesAreCanonical =
        refl
    ; empiricalAdequacy =
        false
    ; empiricalAdequacyIsFalse =
        refl
    ; financialAdviceAuthority =
        false
    ; financialAdviceAuthorityIsFalse =
        refl
    ; productionTradingAuthority =
        false
    ; productionTradingAuthorityIsFalse =
        refl
    ; marketPredictionAuthority =
        false
    ; marketPredictionAuthorityIsFalse =
        refl
    ; manualSemanticLabelAuthority =
        false
    ; manualSemanticLabelAuthorityIsFalse =
        refl
    ; thresholdFishingAuthority =
        false
    ; thresholdFishingAuthorityIsFalse =
        refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        empiricalBasinPromotionImpossible
    }

------------------------------------------------------------------------
-- Canonical fail-closed validation receipt.

data EmpiricalBasinValidationStatus : Set where
  empiricalBasinValidationRecorded_failClosed :
    EmpiricalBasinValidationStatus

record PNFSpectralEmpiricalBasinValidationReceipt : Set where
  field
    validationStatus :
      EmpiricalBasinValidationStatus
    validationStatusIsCanonical :
      validationStatus
      ≡
      empiricalBasinValidationRecorded_failClosed
    validationReceiptName :
      String
    tradingBoundaryReceipt :
      Trading.PNFSpectralTradingSignalBoundaryReceipt
    tradingBoundaryReceiptIsCanonical :
      tradingBoundaryReceipt
      ≡
      Trading.canonicalPNFSpectralTradingSignalBoundaryReceipt
    braidFieldReceipt :
      Braid.PNFBraidTransportFieldReceipt
    braidFieldReceiptIsCanonical :
      braidFieldReceipt
      ≡
      Braid.canonicalPNFBraidTransportFieldReceipt
    architectureReceipt :
      Arch.PNFSpectralFieldArchitectureReceipt
    architectureReceiptIsCanonical :
      architectureReceipt
      ≡
      Arch.canonicalPNFSpectralFieldArchitectureReceipt
    fieldWindowKinds :
      List FieldWindowKind
    fieldWindowKindsAreCanonical :
      fieldWindowKinds ≡ canonicalFieldWindowKinds
    fieldWindowFeatureKinds :
      List FieldWindowFeatureKind
    fieldWindowFeatureKindsAreCanonical :
      fieldWindowFeatureKinds
      ≡
      canonicalFieldWindowFeatureKinds
    outcomeCarrierKinds :
      List OutcomeCarrierKind
    outcomeCarrierKindsAreCanonical :
      outcomeCarrierKinds ≡ canonicalOutcomeCarrierKinds
    canonicalFeature :
      FieldWindowFeature
    canonicalFeatureIsCanonical :
      canonicalFeature ≡ canonicalFieldWindowFeature
    canonicalOutcome :
      OutcomeCarrier
    canonicalOutcomeIsCanonical :
      canonicalOutcome ≡ canonicalOutcomeCarrier
    basinRows :
      List BasinProximityRow
    basinRowsAreCanonical :
      basinRows ≡ canonicalBasinRows
    goodBasinRow :
      BasinProximityRow
    goodBasinRowIsCanonical :
      goodBasinRow ≡ canonicalGoodBasinProximityRow
    badBasinRow :
      BasinProximityRow
    badBasinRowIsCanonical :
      badBasinRow ≡ canonicalBadBasinProximityRow
    tailBasinRow :
      BasinProximityRow
    tailBasinRowIsCanonical :
      tailBasinRow ≡ canonicalTailBasinProximityRow
    tradingSideProductCandidateRows :
      List TradingSideProductCandidateRow
    tradingSideProductCandidateRowsAreCanonical :
      tradingSideProductCandidateRows
      ≡
      canonicalTradingSideProductCandidateRows
    tradingSideProductCandidateRow :
      TradingSideProductCandidateRow
    tradingSideProductCandidateRowIsCanonical :
      tradingSideProductCandidateRow
      ≡
      canonicalTradingSideProductCandidateRow
    separatorLifecycle :
      SeparatorCandidateLifecycle
    separatorLifecycleIsCanonical :
      separatorLifecycle ≡ canonicalSeparatorCandidateLifecycle
    mdlCostDiscipline :
      MDLCostDisciplineReceipt
    mdlCostDisciplineIsCanonical :
      mdlCostDiscipline ≡ canonicalMDLCostDisciplineReceipt
    validationGateReceipt :
      HoldoutCostStressSearchGateReceipt
    validationGateReceiptIsCanonical :
      validationGateReceipt
      ≡
      canonicalHoldoutCostStressSearchGateReceipt
    falseGateReceipt :
      EmpiricalBasinFalseGateReceipt
    falseGateReceiptIsCanonical :
      falseGateReceipt ≡ canonicalEmpiricalBasinFalseGateReceipt
    collapseFlag :
      CollapseFlag
    exhaustionFlag :
      ExhaustionFlag
    collapseFlagIsCanonical :
      collapseFlag ≡ noCollapseObserved
    exhaustionFlagIsCanonical :
      exhaustionFlag ≡ noExhaustionObserved
    validationSummary :
      String
    failClosedBoundary :
      String
    empiricalAdequacyAllowed :
      Bool
    empiricalAdequacyAllowedIsFalse :
      empiricalAdequacyAllowed ≡ false
    financialAdviceAllowed :
      Bool
    financialAdviceAllowedIsFalse :
      financialAdviceAllowed ≡ false
    productionTradingAllowed :
      Bool
    productionTradingAllowedIsFalse :
      productionTradingAllowed ≡ false
    marketPredictionAllowed :
      Bool
    marketPredictionAllowedIsFalse :
      marketPredictionAllowed ≡ false
    manualSemanticLabelsAllowed :
      Bool
    manualSemanticLabelsAllowedIsFalse :
      manualSemanticLabelsAllowed ≡ false
    thresholdFishingAllowed :
      Bool
    thresholdFishingAllowedIsFalse :
      thresholdFishingAllowed ≡ false

open PNFSpectralEmpiricalBasinValidationReceipt public

canonicalPNFSpectralEmpiricalBasinValidationReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt
canonicalPNFSpectralEmpiricalBasinValidationReceipt =
  record
    { validationStatus =
        empiricalBasinValidationRecorded_failClosed
    ; validationStatusIsCanonical =
        refl
    ; validationReceiptName =
        "canonicalPNFSpectralEmpiricalBasinValidationReceipt"
    ; tradingBoundaryReceipt =
        Trading.canonicalPNFSpectralTradingSignalBoundaryReceipt
    ; tradingBoundaryReceiptIsCanonical =
        refl
    ; braidFieldReceipt =
        Braid.canonicalPNFBraidTransportFieldReceipt
    ; braidFieldReceiptIsCanonical =
        refl
    ; architectureReceipt =
        Arch.canonicalPNFSpectralFieldArchitectureReceipt
    ; architectureReceiptIsCanonical =
        refl
    ; fieldWindowKinds =
        canonicalFieldWindowKinds
    ; fieldWindowKindsAreCanonical =
        refl
    ; fieldWindowFeatureKinds =
        canonicalFieldWindowFeatureKinds
    ; fieldWindowFeatureKindsAreCanonical =
        refl
    ; outcomeCarrierKinds =
        canonicalOutcomeCarrierKinds
    ; outcomeCarrierKindsAreCanonical =
        refl
    ; canonicalFeature =
        canonicalFieldWindowFeature
    ; canonicalFeatureIsCanonical =
        refl
    ; canonicalOutcome =
        canonicalOutcomeCarrier
    ; canonicalOutcomeIsCanonical =
        refl
    ; basinRows =
        canonicalBasinRows
    ; basinRowsAreCanonical =
        refl
    ; goodBasinRow =
        canonicalGoodBasinProximityRow
    ; goodBasinRowIsCanonical =
        refl
    ; badBasinRow =
        canonicalBadBasinProximityRow
    ; badBasinRowIsCanonical =
        refl
    ; tailBasinRow =
        canonicalTailBasinProximityRow
    ; tailBasinRowIsCanonical =
        refl
    ; tradingSideProductCandidateRows =
        canonicalTradingSideProductCandidateRows
    ; tradingSideProductCandidateRowsAreCanonical =
        refl
    ; tradingSideProductCandidateRow =
        canonicalTradingSideProductCandidateRow
    ; tradingSideProductCandidateRowIsCanonical =
        refl
    ; separatorLifecycle =
        canonicalSeparatorCandidateLifecycle
    ; separatorLifecycleIsCanonical =
        refl
    ; mdlCostDiscipline =
        canonicalMDLCostDisciplineReceipt
    ; mdlCostDisciplineIsCanonical =
        refl
    ; validationGateReceipt =
        canonicalHoldoutCostStressSearchGateReceipt
    ; validationGateReceiptIsCanonical =
        refl
    ; falseGateReceipt =
        canonicalEmpiricalBasinFalseGateReceipt
    ; falseGateReceiptIsCanonical =
        refl
    ; collapseFlag =
        noCollapseObserved
    ; exhaustionFlag =
        noExhaustionObserved
    ; collapseFlagIsCanonical =
        refl
    ; exhaustionFlagIsCanonical =
        refl
    ; validationSummary =
        "Records field-window features, outcome carriers, good/bad/tail basin proximity, the trading-side product candidate with basin spectral proximity plus braid signature/reference neighborhood plus residual/receipt corroboration, separator lifecycle, collapse/exhaustion flags, MDL/cost discipline, and holdout/cost/search gates."
    ; failClosedBoundary =
        "Trading-side product remains candidate-only pending holdout/replay; empirical adequacy, market prediction authority, financial advice authority, and production trading authority remain false until external resolver, selector, ITIR replay, outcome, holdout, cost-stress, search-cost, MDL, tail-risk, and anti-fishing receipts are supplied."
    ; empiricalAdequacyAllowed =
        false
    ; empiricalAdequacyAllowedIsFalse =
        refl
    ; financialAdviceAllowed =
        false
    ; financialAdviceAllowedIsFalse =
        refl
    ; productionTradingAllowed =
        false
    ; productionTradingAllowedIsFalse =
        refl
    ; marketPredictionAllowed =
        false
    ; marketPredictionAllowedIsFalse =
        refl
    ; manualSemanticLabelsAllowed =
        false
    ; manualSemanticLabelsAllowedIsFalse =
        refl
    ; thresholdFishingAllowed =
        false
    ; thresholdFishingAllowedIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Projections and canonical lemmas.

projectTradingBoundaryReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt →
  Trading.PNFSpectralTradingSignalBoundaryReceipt
projectTradingBoundaryReceipt receipt =
  tradingBoundaryReceipt receipt

projectBraidFieldReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt →
  Braid.PNFBraidTransportFieldReceipt
projectBraidFieldReceipt receipt =
  braidFieldReceipt receipt

projectArchitectureReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt →
  Arch.PNFSpectralFieldArchitectureReceipt
projectArchitectureReceipt receipt =
  architectureReceipt receipt

projectGoodBasinRow :
  PNFSpectralEmpiricalBasinValidationReceipt →
  BasinProximityRow
projectGoodBasinRow receipt =
  goodBasinRow receipt

projectBadBasinRow :
  PNFSpectralEmpiricalBasinValidationReceipt →
  BasinProximityRow
projectBadBasinRow receipt =
  badBasinRow receipt

projectTailBasinRow :
  PNFSpectralEmpiricalBasinValidationReceipt →
  BasinProximityRow
projectTailBasinRow receipt =
  tailBasinRow receipt

projectTradingSideProductCandidateRow :
  PNFSpectralEmpiricalBasinValidationReceipt →
  TradingSideProductCandidateRow
projectTradingSideProductCandidateRow receipt =
  tradingSideProductCandidateRow receipt

projectSeparatorLifecycle :
  PNFSpectralEmpiricalBasinValidationReceipt →
  SeparatorCandidateLifecycle
projectSeparatorLifecycle receipt =
  separatorLifecycle receipt

projectMDLCostDiscipline :
  PNFSpectralEmpiricalBasinValidationReceipt →
  MDLCostDisciplineReceipt
projectMDLCostDiscipline receipt =
  mdlCostDiscipline receipt

projectValidationGateReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt →
  HoldoutCostStressSearchGateReceipt
projectValidationGateReceipt receipt =
  validationGateReceipt receipt

projectFalseGateReceipt :
  PNFSpectralEmpiricalBasinValidationReceipt →
  EmpiricalBasinFalseGateReceipt
projectFalseGateReceipt receipt =
  falseGateReceipt receipt

canonicalTradingBoundaryProjection :
  projectTradingBoundaryReceipt
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  Trading.canonicalPNFSpectralTradingSignalBoundaryReceipt
canonicalTradingBoundaryProjection =
  refl

canonicalBraidFieldProjection :
  projectBraidFieldReceipt
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  Braid.canonicalPNFBraidTransportFieldReceipt
canonicalBraidFieldProjection =
  refl

canonicalArchitectureProjection :
  projectArchitectureReceipt
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  Arch.canonicalPNFSpectralFieldArchitectureReceipt
canonicalArchitectureProjection =
  refl

canonicalGoodBasinProjection :
  projectGoodBasinRow
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalGoodBasinProximityRow
canonicalGoodBasinProjection =
  refl

canonicalBadBasinProjection :
  projectBadBasinRow
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalBadBasinProximityRow
canonicalBadBasinProjection =
  refl

canonicalTailBasinProjection :
  projectTailBasinRow
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalTailBasinProximityRow
canonicalTailBasinProjection =
  refl

canonicalTradingSideProductCandidateProjection :
  projectTradingSideProductCandidateRow
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalTradingSideProductCandidateRow
canonicalTradingSideProductCandidateProjection =
  refl

canonicalSeparatorLifecycleProjection :
  projectSeparatorLifecycle
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalSeparatorCandidateLifecycle
canonicalSeparatorLifecycleProjection =
  refl

canonicalMDLCostDisciplineProjection :
  projectMDLCostDiscipline
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalMDLCostDisciplineReceipt
canonicalMDLCostDisciplineProjection =
  refl

canonicalValidationGateProjection :
  projectValidationGateReceipt
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalHoldoutCostStressSearchGateReceipt
canonicalValidationGateProjection =
  refl

canonicalFalseGateProjection :
  projectFalseGateReceipt
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡
  canonicalEmpiricalBasinFalseGateReceipt
canonicalFalseGateProjection =
  refl

canonicalFieldWindowKindCountIs6 :
  listCount
    (fieldWindowKinds
      canonicalPNFSpectralEmpiricalBasinValidationReceipt)
  ≡ 6
canonicalFieldWindowKindCountIs6 =
  refl

canonicalFieldWindowFeatureKindCountIs7 :
  listCount
    (fieldWindowFeatureKinds
      canonicalPNFSpectralEmpiricalBasinValidationReceipt)
  ≡ 7
canonicalFieldWindowFeatureKindCountIs7 =
  refl

canonicalOutcomeCarrierKindCountIs5 :
  listCount
    (outcomeCarrierKinds
      canonicalPNFSpectralEmpiricalBasinValidationReceipt)
  ≡ 5
canonicalOutcomeCarrierKindCountIs5 =
  refl

canonicalBasinRowCountIs3 :
  listCount
    (basinRows
      canonicalPNFSpectralEmpiricalBasinValidationReceipt)
  ≡ 3
canonicalBasinRowCountIs3 =
  refl

canonicalTradingSideProductCandidateRowCountIs1 :
  listCount
    (tradingSideProductCandidateRows
      canonicalPNFSpectralEmpiricalBasinValidationReceipt)
  ≡ 1
canonicalTradingSideProductCandidateRowCountIs1 =
  refl

canonicalEmpiricalValidationGateCountIs10 :
  listCount
    (validationGates canonicalHoldoutCostStressSearchGateReceipt)
  ≡ 10
canonicalEmpiricalValidationGateCountIs10 =
  refl

canonicalFalseGateCountIs6 :
  listCount
    (falseGates canonicalEmpiricalBasinFalseGateReceipt)
  ≡ 6
canonicalFalseGateCountIs6 =
  refl

canonicalNoEmpiricalAdequacyAllowed :
  empiricalAdequacyAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoEmpiricalAdequacyAllowed =
  refl

canonicalNoFinancialAdviceAllowed :
  financialAdviceAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoFinancialAdviceAllowed =
  refl

canonicalNoProductionTradingAllowed :
  productionTradingAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoProductionTradingAllowed =
  refl

canonicalNoMarketPredictionAllowed :
  marketPredictionAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoMarketPredictionAllowed =
  refl

canonicalTradingSideProductNamesThreeLayers :
  threeCorroborationLayersNamed
    canonicalTradingSideProductCandidateRow
  ≡ true
canonicalTradingSideProductNamesThreeLayers =
  refl

canonicalTradingSideProductPendingHoldoutReplay :
  pendingHoldoutReplay
    canonicalTradingSideProductCandidateRow
  ≡ true
canonicalTradingSideProductPendingHoldoutReplay =
  refl

canonicalTradingSideProductNoEmpiricalAdequacy :
  empiricalAdequacyGranted
    canonicalTradingSideProductCandidateRow
  ≡ false
canonicalTradingSideProductNoEmpiricalAdequacy =
  refl

canonicalTradingSideProductNoMarketPrediction :
  marketPredictionAuthorityGranted
    canonicalTradingSideProductCandidateRow
  ≡ false
canonicalTradingSideProductNoMarketPrediction =
  refl

canonicalTradingSideProductNoFinancialAdvice :
  financialAdviceAuthorityGranted
    canonicalTradingSideProductCandidateRow
  ≡ false
canonicalTradingSideProductNoFinancialAdvice =
  refl

canonicalTradingSideProductNoProductionTrading :
  productionTradingAuthorityGranted
    canonicalTradingSideProductCandidateRow
  ≡ false
canonicalTradingSideProductNoProductionTrading =
  refl

canonicalNoManualSemanticLabelsAllowed :
  manualSemanticLabelsAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoManualSemanticLabelsAllowed =
  refl

canonicalNoThresholdFishingAllowed :
  thresholdFishingAllowed
    canonicalPNFSpectralEmpiricalBasinValidationReceipt
  ≡ false
canonicalNoThresholdFishingAllowed =
  refl

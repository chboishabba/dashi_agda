module DASHI.Crypto.BlueTeamSearchObservationRound17 where

------------------------------------------------------------------------
-- ROUND 17: BLUE-TEAM SEARCH GEOMETRY + OBSERVATION VALUE
------------------------------------------------------------------------

import DASHI.Crypto.BlueTeamAdversaryClosureRound16

-- FIPS-203 NTT structural dependency, conditioned equations, actual CBD slices,
-- representation-locality geometry, and the symmetry/uncertainty lift.
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact
import DASHI.Crypto.MLKEMNTTPriorCutNoGoExact
import DASHI.Crypto.MLKEMNTTParityBlockPriorExact
import DASHI.Crypto.MLKEMNTTCombinedCouplingConnectivityExact
import DASHI.Crypto.MLKEMCandidateMoveFanoutExact
import DASHI.Crypto.MLKEMLocalityAreaInvariantExact
import DASHI.Crypto.MLKEMButterflyStageLocalityInvariantExact
import DASHI.Crypto.MLKEMNTTSingularBudgetUncertaintyExact
import DASHI.Crypto.MLKEMNTTLocalOutcomeBudgetExact
import DASHI.Crypto.MLKEMNTTLocalMatrixOutcomeClassifierExact
import DASHI.Crypto.MLKEMNTTLocalLeftInverseZeroReflectionExact
import DASHI.Crypto.MLKEMBaseCaseAdjugateInverseExact
import DASHI.Crypto.MLKEMBaseCaseNormInverseBridgeExact
import DASHI.Crypto.MLKEMBaseCaseNonsquareNormSeparationExact
import DASHI.Crypto.MLKEMFIPS203GammaNonsquareTransportExact
import DASHI.Crypto.MLKEMUncertaintyTransitionCostBridgeExact
import DASHI.Crypto.MLKEMProtectedLabelUncertaintyEdgeExact
import DASHI.Crypto.MLKEMSupportUncertaintyRuntimeNoGoExact
import DASHI.Crypto.MLKEMButterflyUncertaintyWorkFrontierExact
import DASHI.Crypto.MLKEMExactResidualTouchLowerBoundExact
import DASHI.Crypto.MLKEMResidualTouchPathLowerBoundExact
import DASHI.Crypto.MLKEMUncertaintyDecisionTreeStrengthBoundaryExact
import DASHI.Crypto.MLKEMTouchInformationNoGoExact
import DASHI.Crypto.MLKEMBoundedReadoutInformationFrontierExact
import DASHI.Crypto.MLKEMProtectedLabelReadoutFactorisationExact
import DASHI.Crypto.MLKEMFiniteStateTranscriptCapacityExact
import DASHI.Crypto.MLKEMBoundedCellTranscriptCapacityExact
import DASHI.Crypto.MLKEMUpdateCapacityDichotomyExact
import DASHI.Crypto.MLKEMBaseCaseConditionedResidualExact
import DASHI.Crypto.ConditionedResidualAmbiguityRegressionExact
import DASHI.Crypto.ConditionalMateAmbiguityExact
import DASHI.Crypto.ConditionalReconciliationSearchExact
import DASHI.Crypto.MLKEMNTTActualCBD2ScalarCollisionExact
import DASHI.Crypto.MLKEMNTTActualCBD2SliceCouplingExact
import DASHI.Crypto.MLKEMNTTActualCBD2TwoScalarRefinementExact
import DASHI.Crypto.MLKEMNTTActualCBD2FullTripleListProfileExact
import DASHI.Crypto.MLKEMNTTActualCBD2ConditionalListMassExact
import DASHI.Crypto.FiniteMLWEListDecodingGeometryExact

-- Observation acquisition, threat-language refinement, and protocol-visible
-- split surfaces.
import DASHI.Crypto.ObservationAcquisitionCostExact
import DASHI.Crypto.KeyConfirmationObservationRefinementExact
import DASHI.Crypto.MLKEMImplicitRejectProtocolObservationExact
import DASHI.Crypto.MLKEMImplicitRejectTimingCompositionExact
import DASHI.Crypto.FiniteMLWEConfirmationObservationExact
import DASHI.Crypto.ObservationSeparatorGeometryExact
import DASHI.Crypto.AttackerObservationLanguageRefinementExact
import DASHI.Crypto.RepresentationSecurityGameExact

-- Protected-label transition geometry / representation geometry.
import DASHI.Crypto.ProtectedLabelSearchGeometryExact
import DASHI.Crypto.SearchGraphEmbeddingDistortionExact
import DASHI.Crypto.GrayPathTransitionOptimalExact
import DASHI.Crypto.CBD2MixedRadixGrayTraversalExact
import DASHI.Crypto.FiniteMLWETransitionGeometryExact
import DASHI.Crypto.IncrementalResidualTraversalExact
import DASHI.Crypto.CryptoRepresentationParetoExact
import DASHI.Crypto.AdaptiveCandidateResidualWidthExact
import DASHI.Crypto.ConditionalResidualRateExact
import DASHI.Crypto.FiniteGuessingProbabilityExact
import DASHI.Crypto.RepresentationLeakageGeometryExact

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record Round17ClaimBoundary : Set where
  constructor round17ClaimBoundary
  field
    nttLocalMultiplicationProvesIndependentSecretSearch : Bool
    nttLocalMultiplicationProvesIndependentSecretSearchIsFalse :
      nttLocalMultiplicationProvesIndependentSecretSearch ≡ false
    sameParityDataflowProvesStatisticalDependence : Bool
    sameParityDataflowProvesStatisticalDependenceIsFalse :
      sameParityDataflowProvesStatisticalDependence ≡ false
    visibleConfirmationAlwaysLeaks : Bool
    visibleConfirmationAlwaysLeaksIsFalse :
      visibleConfirmationAlwaysLeaks ≡ false
    internalImplicitRejectRouteAlwaysExternallyVisible : Bool
    internalImplicitRejectRouteAlwaysExternallyVisibleIsFalse :
      internalImplicitRejectRouteAlwaysExternallyVisible ≡ false
    candidateShrinkAloneIsNetAttackProgress : Bool
    candidateShrinkAloneIsNetAttackProgressIsFalse :
      candidateShrinkAloneIsNetAttackProgress ≡ false
    connectedNTTGraphRulesOutConditionalSearch : Bool
    connectedNTTGraphRulesOutConditionalSearchIsFalse :
      connectedNTTGraphRulesOutConditionalSearch ≡ false
    conditioningOneBlockProvesUniqueMate : Bool
    conditioningOneBlockProvesUniqueMateIsFalse :
      conditioningOneBlockProvesUniqueMate ≡ false
    oneLocalNTTScalarUniquelyDeterminesCBD2SourceSlice : Bool
    oneLocalNTTScalarUniquelyDeterminesCBD2SourceSliceIsFalse :
      oneLocalNTTScalarUniquelyDeterminesCBD2SourceSlice ≡ false
    twoScalarSliceResultProvesWholeSecretRecovery : Bool
    twoScalarSliceResultProvesWholeSecretRecoveryIsFalse :
      twoScalarSliceResultProvesWholeSecretRecovery ≡ false
    equalRateMeansEqualSearchGeometry : Bool
    equalRateMeansEqualSearchGeometryIsFalse :
      equalRateMeansEqualSearchGeometry ≡ false
    statisticalGainMeansSearchCostGain : Bool
    statisticalGainMeansSearchCostGainIsFalse :
      statisticalGainMeansSearchCostGain ≡ false
    betterTransitionGeometryMeansLessPhysicalLeakage : Bool
    betterTransitionGeometryMeansLessPhysicalLeakageIsFalse :
      betterTransitionGeometryMeansLessPhysicalLeakage ≡ false
    coefficientLocalMoveMeansNTTLocalUpdate : Bool
    coefficientLocalMoveMeansNTTLocalUpdateIsFalse :
      coefficientLocalMoveMeansNTTLocalUpdate ≡ false
    equalLocalityAreaIsUniversalUncertaintyTheorem : Bool
    equalLocalityAreaIsUniversalUncertaintyTheoremIsFalse :
      equalLocalityAreaIsUniversalUncertaintyTheorem ≡ false
    butterflyStageIdentityIsUniversalRepresentationLowerBound : Bool
    butterflyStageIdentityIsUniversalRepresentationLowerBoundIsFalse :
      butterflyStageIdentityIsUniversalRepresentationLowerBound ≡ false

open Round17ClaimBoundary public

canonicalRound17ClaimBoundary : Round17ClaimBoundary
canonicalRound17ClaimBoundary =
  round17ClaimBoundary
    false refl false refl false refl false refl false refl false refl
    false refl false refl false refl false refl false refl false refl false refl
    false refl false refl

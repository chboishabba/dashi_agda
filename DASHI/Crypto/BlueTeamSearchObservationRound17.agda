module DASHI.Crypto.BlueTeamSearchObservationRound17 where

------------------------------------------------------------------------
-- ROUND 17: BLUE-TEAM SEARCH GEOMETRY + OBSERVATION VALUE
--
-- Continues Round 16 along both remaining programmes:
--
--   A. transported MLWE/NTT prior geometry and reconciliation;
--   B. hidden-dependent observation refinement and net acquisition value.
--
-- Round 17 now adds the third coordinate exposed by the future-quotient/Gray
-- thread: candidate fibres carry a transition/search geometry, so equal rate or
-- equal cardinality does not imply equal recovery cost.
------------------------------------------------------------------------

import DASHI.Crypto.BlueTeamAdversaryClosureRound16

-- FIPS-203 NTT structural dependency, conditioned equations, and prior geometry.
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact
import DASHI.Crypto.MLKEMNTTPriorCutNoGoExact
import DASHI.Crypto.MLKEMNTTParityBlockPriorExact
import DASHI.Crypto.MLKEMNTTCombinedCouplingConnectivityExact
import DASHI.Crypto.MLKEMCandidateMoveFanoutExact
import DASHI.Crypto.MLKEMBaseCaseConditionedResidualExact
import DASHI.Crypto.ConditionedResidualAmbiguityRegressionExact
import DASHI.Crypto.ConditionalMateAmbiguityExact
import DASHI.Crypto.ConditionalReconciliationSearchExact

-- Observation acquisition and protocol-visible split surfaces.
import DASHI.Crypto.ObservationAcquisitionCostExact
import DASHI.Crypto.KeyConfirmationObservationRefinementExact
import DASHI.Crypto.MLKEMImplicitRejectProtocolObservationExact
import DASHI.Crypto.MLKEMImplicitRejectTimingCompositionExact
import DASHI.Crypto.FiniteMLWEConfirmationObservationExact
import DASHI.Crypto.ObservationSeparatorGeometryExact

-- Protected-label transition geometry / representation geometry.
import DASHI.Crypto.ProtectedLabelSearchGeometryExact
import DASHI.Crypto.SearchGraphEmbeddingDistortionExact
import DASHI.Crypto.GrayPathTransitionOptimalExact
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

open Round17ClaimBoundary public

canonicalRound17ClaimBoundary : Round17ClaimBoundary
canonicalRound17ClaimBoundary =
  round17ClaimBoundary
    false refl false refl false refl false refl false refl false refl
    false refl false refl false refl false refl false refl

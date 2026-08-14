module DASHI.Crypto.BlueTeamSearchObservationRound17 where

------------------------------------------------------------------------
-- ROUND 17: BLUE-TEAM SEARCH GEOMETRY + OBSERVATION VALUE
--
-- Continues Round 16 along both remaining programmes:
--
--   A. transported MLWE/NTT prior geometry and reconciliation;
--   B. hidden-dependent observation refinement and net acquisition value.
--
-- The tranche deliberately proves structural/cost statements rather than
-- promoting them into an ML-KEM break or a security proof.
------------------------------------------------------------------------

import DASHI.Crypto.BlueTeamAdversaryClosureRound16

-- FIPS-203 NTT structural dependency and prior geometry.
import DASHI.Crypto.MLKEMNTTDataflowCouplingExact
import DASHI.Crypto.MLKEMNTTPriorCutNoGoExact
import DASHI.Crypto.MLKEMNTTParityBlockPriorExact
import DASHI.Crypto.MLKEMNTTCombinedCouplingConnectivityExact

-- Observation acquisition and protocol-visible split surfaces.
import DASHI.Crypto.ObservationAcquisitionCostExact
import DASHI.Crypto.KeyConfirmationObservationRefinementExact
import DASHI.Crypto.MLKEMImplicitRejectProtocolObservationExact
import DASHI.Crypto.MLKEMImplicitRejectTimingCompositionExact
import DASHI.Crypto.FiniteMLWEConfirmationObservationExact

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

open Round17ClaimBoundary public

canonicalRound17ClaimBoundary : Round17ClaimBoundary
canonicalRound17ClaimBoundary =
  round17ClaimBoundary false refl false refl false refl false refl false refl

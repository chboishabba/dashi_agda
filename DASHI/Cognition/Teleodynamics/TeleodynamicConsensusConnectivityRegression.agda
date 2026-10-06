module DASHI.Cognition.Teleodynamics.TeleodynamicConsensusConnectivityRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicConsensusConnectivityExact as Consensus

connectedStationaryImpliesConsensus :
  Consensus.connectedStationaryStateIsConsensus Consensus.canonicalConsensusConnectivityBoundary ≡ true
connectedStationaryImpliesConsensus = refl

flowConvergenceStillSeparate :
  Consensus.connectivityAloneProvesFlowConvergence Consensus.canonicalConsensusConnectivityBoundary ≡ false
flowConvergenceStillSeparate = refl

noPhysicalPromotion :
  Consensus.consensusCreatesNonlocalTransmission Consensus.canonicalConsensusConnectivityBoundary ≡ false
noPhysicalPromotion = refl

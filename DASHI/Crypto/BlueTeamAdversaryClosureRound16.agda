module DASHI.Crypto.BlueTeamAdversaryClosureRound16 where

------------------------------------------------------------------------
-- ROUND 16: BLUE-TEAM ADVERSARY / OBSERVATION / FIBRE / SEARCH / GAME CLOSURE
--
-- The cumulative crypto lane now has one explicit path:
--
-- candidate test
--   -> observation refinement
--   -> finite candidate cardinality
--   -> local/reconciliation search accounting
--   -> protected-label recovery boundary
--   -> finite distinguishing-game boundary.
--
-- This is defensive cryptanalytic infrastructure.  It does not assert a break
-- of ML-KEM or any other standardized primitive.
------------------------------------------------------------------------

import DASHI.Crypto.BlueTeamAdversaryObservationExact
import DASHI.Crypto.FiniteCandidateFibreCardinalityExact
import DASHI.Crypto.TranscriptProtectedLabelExact
import DASHI.Crypto.IndexedSearchCostExact
import DASHI.Crypto.FiniteSecurityGameBoundaryExact
import DASHI.Crypto.FiniteMLWEVectorLabExact
import DASHI.Crypto.FiniteMLWEGameRegressionExact
import DASHI.Crypto.MLKEMFIPS203SourceExact
import DASHI.Crypto.MLKEMFIPS203SearchGeometryExact

-- Existing theorem-bearing search/observation machinery reused rather than
-- duplicated.
import DASHI.Crypto.ChosenCiphertextObservationRefinementExact
import DASHI.Crypto.ResidualConstraintDecompositionExact
import DASHI.Crypto.ConstraintCouplingSearchExact
import DASHI.Crypto.SearchFactorisationExact
import DASHI.Crypto.AdaptiveFibreShrinkExact
import DASHI.Crypto.TimingObservationSideChannelExact
import DASHI.Crypto.MLWEKeyStateResidualExact
import DASHI.Crypto.PassiveEncapsulationFibreInvariantExact
import DASHI.Crypto.PublicSecretFactorisationAttackExact
import DASHI.Crypto.MLKEMSecurityDependencyGraphExact
import DASHI.Crypto.MLKEMLocalSearchGeometryExact

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record Round16ClaimBoundary : Set where
  constructor round16ClaimBoundary
  field
    finiteLabIsMLKEM : Bool
    finiteLabIsMLKEMIsFalse : finiteLabIsMLKEM ≡ false
    exactFIPS203BitImplementationComplete : Bool
    exactFIPS203BitImplementationCompleteIsFalse :
      exactFIPS203BitImplementationComplete ≡ false
    round16ClaimsMLKEMBroken : Bool
    round16ClaimsMLKEMBrokenIsFalse : round16ClaimsMLKEMBroken ≡ false
    observationSplitRequiresWitness : Bool
    observationSplitRequiresWitnessIsTrue :
      observationSplitRequiresWitness ≡ true
    protectedLabelRecoveryIsSufficientBreakWitness : Bool
    protectedLabelRecoveryIsSufficientBreakWitnessIsTrue :
      protectedLabelRecoveryIsSufficientBreakWitness ≡ true

open Round16ClaimBoundary public

canonicalRound16ClaimBoundary : Round16ClaimBoundary
canonicalRound16ClaimBoundary =
  round16ClaimBoundary false refl false refl false refl true refl true refl

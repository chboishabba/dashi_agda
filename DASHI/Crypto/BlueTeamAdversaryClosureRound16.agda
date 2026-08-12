module DASHI.Crypto.BlueTeamAdversaryClosureRound16 where

------------------------------------------------------------------------
-- ROUND 16: BLUE-TEAM ADVERSARY / OBSERVATION / FIBRE / SEARCH / GAME CLOSURE
------------------------------------------------------------------------

import DASHI.Crypto.BlueTeamAdversaryObservationExact
import DASHI.Crypto.BlueTeamThreatModelExact
import DASHI.Crypto.ComputationalCandidateFibreExact
import DASHI.Crypto.FiniteCandidateFibreCardinalityExact
import DASHI.Crypto.TranscriptProtectedLabelExact
import DASHI.Crypto.IndexedSearchCostExact
import DASHI.Crypto.FiniteSecurityGameBoundaryExact
import DASHI.Crypto.FiniteAdvantageAccountingExact
import DASHI.Crypto.PriorScoreSearchFactorisationExact
import DASHI.Crypto.PublicFactoredObservationTraceInvariantExact
import DASHI.Crypto.AlgorithmRelativeRecoveryCostExact
import DASHI.Crypto.FiniteMLWEVectorLabExact
import DASHI.Crypto.FiniteMLWEGameRegressionExact
import DASHI.Crypto.FiniteMLWEPriorScoreSearchRegressionExact
import DASHI.Crypto.InvertibleTransformPriorCouplingRegressionExact
import DASHI.Crypto.MLKEMFIPS203SourceExact
import DASHI.Crypto.MLKEMFIPS203SearchGeometryExact
import DASHI.Crypto.MLKEMNTTLocalPriorCouplingExact

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
    observationSplitRequiresWitnessIsTrue : observationSplitRequiresWitness ≡ true
    protectedLabelRecoveryIsSufficientBreakWitness : Bool
    protectedLabelRecoveryIsSufficientBreakWitnessIsTrue :
      protectedLabelRecoveryIsSufficientBreakWitness ≡ true
    exactPublicFibreMustBeBroadForComputationalHardness : Bool
    exactPublicFibreMustBeBroadForComputationalHardnessIsFalse :
      exactPublicFibreMustBeBroadForComputationalHardness ≡ false
    invertibleNTTAloneCollapsesSearch : Bool
    invertibleNTTAloneCollapsesSearchIsFalse :
      invertibleNTTAloneCollapsesSearch ≡ false
    candidateShrinkAloneProvesCostReduction : Bool
    candidateShrinkAloneProvesCostReductionIsFalse :
      candidateShrinkAloneProvesCostReduction ≡ false

open Round16ClaimBoundary public

canonicalRound16ClaimBoundary : Round16ClaimBoundary
canonicalRound16ClaimBoundary =
  round16ClaimBoundary
    false refl false refl false refl true refl true refl false refl false refl false refl

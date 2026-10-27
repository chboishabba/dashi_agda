{-# OPTIONS --safe #-}
module DASHI.Unified.YMGoal1TOECompatibilityValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel)

import DASHI.Unified.YMGoal1TOECompatibilityExact as Goal1
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as U

toeFiniteAMatchesAdapter :
  TOE.toe369YangMillsGoal1FiniteASourceLevel
  ≡ Goal1.goal1FiniteASourceLevel
toeFiniteAMatchesAdapter = refl

toeCanonicalBMatchesAdapter :
  TOE.toe369YangMillsGoal1CanonicalSelectedBSourceLevel
  ≡ Goal1.goal1CanonicalSelectedBSourceLevel
toeCanonicalBMatchesAdapter = refl

toeLocalCMatchesAdapter :
  TOE.toe369YangMillsGoal1LocalQFTCSourceLevel
  ≡ Goal1.goal1LocalQFTCSourceLevel
toeLocalCMatchesAdapter = refl

unifierFiniteAMatchesAdapter :
  U.unifierYangMillsGoal1FiniteASourceLevel
  ≡ Goal1.goal1FiniteASourceLevel
unifierFiniteAMatchesAdapter = refl

unifierCanonicalBMatchesAdapter :
  U.unifierYangMillsGoal1CanonicalSelectedBSourceLevel
  ≡ Goal1.goal1CanonicalSelectedBSourceLevel
unifierCanonicalBMatchesAdapter = refl

unifierLocalCMatchesAdapter :
  U.unifierYangMillsGoal1LocalQFTCSourceLevel
  ≡ Goal1.goal1LocalQFTCSourceLevel
unifierLocalCMatchesAdapter = refl

toeContinuumStillBlocked :
  Goal1.flat4DContinuumTransferProvedHere ≡ false
toeContinuumStillBlocked =
  TOE.toe369YangMillsFlat4DContinuumStillOpen

toeMassGapStillBlocked :
  Goal1.continuumMassGapPromoted ≡ false
toeMassGapStillBlocked =
  TOE.toe369YangMillsContinuumMassGapStillNotPromoted

toeClayStillBlocked :
  Goal1.clayYangMillsPromoted ≡ false
toeClayStillBlocked =
  TOE.toe369YangMillsClayStillNotPromoted

unifierContinuumStillBlocked :
  Goal1.flat4DContinuumTransferProvedHere ≡ false
unifierContinuumStillBlocked =
  U.unifierYangMillsFlat4DContinuumStillOpen

unifierMassGapStillBlocked :
  Goal1.continuumMassGapPromoted ≡ false
unifierMassGapStillBlocked =
  U.unifierYangMillsContinuumMassGapStillNotPromoted

unifierClayStillBlocked :
  Goal1.clayYangMillsPromoted ≡ false
unifierClayStillBlocked =
  U.unifierYangMillsClayStillNotPromoted


------------------------------------------------------------------------
-- Preferred R440--R444 route regressions.
------------------------------------------------------------------------

preferredVariableDomainBMatchesAdapter :
  TOE.toe369YangMillsGoal1PreferredVariableDomainBSourceLevel
  ≡ Goal1.goal1PreferredVariableDomainBSourceLevel
preferredVariableDomainBMatchesAdapter = refl

rootedTraceEncodingMatchesAdapter :
  TOE.toe369YangMillsGoal1R429RootedTraceEncodingLevel
  ≡ Goal1.goal1R429RootedTraceEncodingLevel
rootedTraceEncodingMatchesAdapter = refl

rootedTraceCountCompilerMatchesAdapter :
  TOE.toe369YangMillsGoal1R429RootedTraceCountCompilerLevel
  ≡ Goal1.goal1R429RootedTraceCountCompilerLevel
rootedTraceCountCompilerMatchesAdapter = refl

entropyReserveMatchesAdapter :
  TOE.toe369YangMillsGoal1R429SourceDecayReserveLevel
  ≡ Goal1.goal1R429SourceDecayReserveLevel
entropyReserveMatchesAdapter = refl

entropyCompilerMatchesAdapter :
  TOE.toe369YangMillsGoal1R429EntropyBudgetCompilerLevel
  ≡ Goal1.goal1R429EntropyBudgetCompilerLevel
entropyCompilerMatchesAdapter = refl

finiteA1WilsonMatchesAdapter :
  TOE.toe369YangMillsGoal1FiniteA1WilsonActionInvarianceLevel
  ≡ Goal1.goal1FiniteA1WilsonActionInvarianceLevel
finiteA1WilsonMatchesAdapter = refl

finiteA1HaarMatchesAdapter :
  TOE.toe369YangMillsGoal1FiniteA1ProductHaarInvarianceLevel
  ≡ Goal1.goal1FiniteA1ProductHaarInvarianceLevel
finiteA1HaarMatchesAdapter = refl

finiteA2PeterWeylMatchesAdapter :
  TOE.toe369YangMillsGoal1FiniteA2PeterWeylWilsonIdentificationLevel
  ≡ Goal1.goal1FiniteA2PeterWeylWilsonIdentificationLevel
finiteA2PeterWeylMatchesAdapter = refl

legacyGlobalTreeMetricCannotRegainPreference :
  Goal1.legacyGlobalTreeMetricPreferred ≡ false
legacyGlobalTreeMetricCannotRegainPreference =
  TOE.toe369YangMillsGoal1LegacyGlobalTreeMetricNotPreferred

unifierPreferredVariableDomainBMatchesAdapter :
  U.unifierYangMillsGoal1PreferredVariableDomainBSourceLevel
  ≡ Goal1.goal1PreferredVariableDomainBSourceLevel
unifierPreferredVariableDomainBMatchesAdapter = refl

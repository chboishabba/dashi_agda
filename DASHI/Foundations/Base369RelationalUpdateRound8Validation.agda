module DASHI.Foundations.Base369RelationalUpdateRound8Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.SSPTritCarrier using
  ( sspNegOne
  ; sspZero
  ; sspPosOne
  )

import DASHI.Foundations.Base369CalculationFibreClosureExact as Calculation
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Foundations.Base369PropositionResponseTransportExact as Response
import DASHI.Foundations.Base369RelationalFailureOperatorsExact as Failure
import DASHI.Foundations.Base369SharedStateWeaveIntegrityExact as Weave
import DASHI.Foundations.Base369RelationalUpdateKernelExact as Kernel

interactionCubeHasTwentySevenStates :
  Cube.interactionStateCount ≡ 27
interactionCubeHasTwentySevenStates = Cube.interactionStateCountIs27

appraisalFibreHasSevenHundredTwentyNineStates :
  Cube.appraisalFibreStateCount ≡ 729
appraisalFibreHasSevenHundredTwentyNineStates =
  Cube.appraisalFibreStateCountIs729

oneRoundStateHasNineteenThousandSixHundredEightyThreeStates :
  Cube.oneRoundStateCount ≡ 19683
oneRoundStateHasNineteenThousandSixHundredEightyThreeStates =
  Cube.oneRoundStateCountIs19683

pointedAppraisalDecompositionIsSevenHundredTwentyNine :
  Pointed.pointedAppraisalAddressCount ≡ 729
pointedAppraisalDecompositionIsSevenHundredTwentyNine =
  Pointed.pointedAppraisalAddressCountIs729

appraisalTimesMultiplicityIsSixtyFiveThousandSixHundredTen :
  Pointed.appraisalMultiplicityCount ≡ 65610
appraisalTimesMultiplicityIsSixtyFiveThousandSixHundredTen =
  Pointed.appraisalMultiplicityCountIs65610

ceasedConversationRemainsUncompleted :
  Weave.repairCompletion Weave.ceasedWithoutRepair
  ≡ Weave.uninstantiated
ceasedConversationRemainsUncompleted = refl

completedRepairCarriesCompletionWitness :
  Weave.repairCompletion Weave.completedRepair
  ≡ Weave.instantiated
completedRepairCarriesCompletionWitness = refl

behaviourProjectionIsNonInjective :
  Failure.observeChoice Failure.willing
  ≡ Failure.observeChoice Failure.complyingUnderPressure
behaviourProjectionIsNonInjective =
  Failure.performedObservationIsNonInjective

considerAndCommitRemainDistinctModalities :
  Response.deliberative Response.considerModality ≡ Response.mightConsider
considerAndCommitRemainDistinctModalities = refl

commitCarriesObligation :
  Response.obligation Response.commitModality
  ≡ Response.commitmentToAnother
commitCarriesObligation = refl

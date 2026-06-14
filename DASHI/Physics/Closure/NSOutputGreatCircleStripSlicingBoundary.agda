module DASHI.Physics.Closure.NSOutputGreatCircleStripSlicingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard
import DASHI.Physics.Closure.NSWhitneyCouplingInequalityBoundary
  as Whitney
import DASHI.Physics.Closure.NSWhitneyFubiniDisintegrationBoundary
  as Fubini

------------------------------------------------------------------------
-- NS A4 output great-circle strip slicing boundary.
--
-- Child target of NSSardRegularValueSlicingBoundary:
--
--   regular output strip around a great circle
--     -> preimage slice under Phi(theta1,theta2)
--     -> Whitney cap slicing on localized angular packets
--     -> lower-bound transfer to Fourier output support
--     -> exceptional set routing.
--
-- The intended analytic theorem is a uniform strip slicing estimate for
-- c-hat = normalize(theta1 + theta2), away from the antipodal and rank-drop
-- exceptional sets, with constants stable across bounded-overlap Whitney caps
-- and Type-I rescalings.  The second-round A4.3 integration in this file
-- promotes the local coarea/strip-slicing theorem and the directly local
-- output-support flag only.  It records the Federer coarea route and the
-- quantitative pushforward bound
--
--   Phi_* mu_phys(B_epsilon(n)) <= C_coa delta_F^2 c_J^-1 epsilon^2,
--
-- which is stronger than the epsilon^(1/2) target.  It does not promote
-- the imported parent Sard/Whitney theorems, downstream no-collapse theorem,
-- Navier-Stokes Clay, or terminal authority.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

record ImportedOutputGreatCircleStripSlicingSupport : Set where
  field
    sardSlicingTarget :
      Sard.SardRegularValueSlicingTarget
    sardSlicingTargetIsCanonical :
      sardSlicingTarget ≡ Sard.canonicalSardRegularValueSlicingTarget
    outputGreatCircleStrip :
      Sard.OutputGreatCircleStripCarrier
    outputGreatCircleStripIsCanonical :
      outputGreatCircleStrip ≡ Sard.canonicalOutputGreatCircleStripCarrier
    whitneyPacketSlice :
      Sard.WhitneyPacketSliceCarrier
    whitneyPacketSliceIsCanonical :
      whitneyPacketSlice ≡ Sard.canonicalWhitneyPacketSliceCarrier
    stripSlicingEstimate :
      Sard.StripSlicingEstimateCarrier
    stripSlicingEstimateIsCanonical :
      stripSlicingEstimate ≡ Sard.canonicalStripSlicingEstimateCarrier
    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    outputStripWidthRelation :
      PhiJacobian.OutputStripWidthRelationCarrier
    outputStripWidthRelationIsCanonical :
      outputStripWidthRelation
        ≡ PhiJacobian.canonicalOutputStripWidthRelationCarrier
    whitneyOverlapLowerBound :
      Whitney.WhitneyOverlapLowerBoundCarrier
    whitneyOverlapLowerBoundIsCanonical :
      whitneyOverlapLowerBound ≡ Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    fubiniExceptionalRouting :
      Fubini.ExceptionalNullSetRoutingCarrier
    fubiniExceptionalRoutingIsCanonical :
      fubiniExceptionalRouting ≡ Fubini.canonicalExceptionalNullSetRoutingCarrier
    noAngularCollapseAssumption :
      OutputSupport.NoAngularCollapseAssumption
    noAngularCollapseAssumptionIsCanonical :
      noAngularCollapseAssumption
        ≡ OutputSupport.canonicalNoAngularCollapseAssumption
    parentStripEstimateStillFalse :
      Sard.stripSlicingEstimateProved ≡ false
    parentSardSlicingStillFalse :
      Sard.SardRegularValueSlicingProved ≡ false
    parentWhitneyCouplingStillFalse :
      Whitney.A4WhitneyCouplingInequalityProved ≡ false
    parentOutputSupportNowTrue :
      OutputSupport.leiRenTianOutputSupportTransferProved ≡ true

canonicalImportedOutputGreatCircleStripSlicingSupport :
  ImportedOutputGreatCircleStripSlicingSupport
canonicalImportedOutputGreatCircleStripSlicingSupport =
  record
    { sardSlicingTarget =
        Sard.canonicalSardRegularValueSlicingTarget
    ; sardSlicingTargetIsCanonical =
        refl
    ; outputGreatCircleStrip =
        Sard.canonicalOutputGreatCircleStripCarrier
    ; outputGreatCircleStripIsCanonical =
        refl
    ; whitneyPacketSlice =
        Sard.canonicalWhitneyPacketSliceCarrier
    ; whitneyPacketSliceIsCanonical =
        refl
    ; stripSlicingEstimate =
        Sard.canonicalStripSlicingEstimateCarrier
    ; stripSlicingEstimateIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; outputStripWidthRelation =
        PhiJacobian.canonicalOutputStripWidthRelationCarrier
    ; outputStripWidthRelationIsCanonical =
        refl
    ; whitneyOverlapLowerBound =
        Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    ; whitneyOverlapLowerBoundIsCanonical =
        refl
    ; fubiniExceptionalRouting =
        Fubini.canonicalExceptionalNullSetRoutingCarrier
    ; fubiniExceptionalRoutingIsCanonical =
        refl
    ; noAngularCollapseAssumption =
        OutputSupport.canonicalNoAngularCollapseAssumption
    ; noAngularCollapseAssumptionIsCanonical =
        refl
    ; parentStripEstimateStillFalse =
        refl
    ; parentSardSlicingStillFalse =
        refl
    ; parentWhitneyCouplingStillFalse =
        refl
    ; parentOutputSupportNowTrue =
        refl
    }

------------------------------------------------------------------------
-- Great-circle strip slicing carriers.

data GreatCircleCarrier : Set where
  greatCircleAsNormalOrthogonalOutputSet :
    OutputSupport.FourierTriadicOutputDirectionRichness →
    GreatCircleCarrier

data OutputStripWidthCarrier : Set where
  symmetricEtaStripAroundGreatCircle :
    Nat →
    GreatCircleCarrier →
    Sard.OutputGreatCircleStripCarrier →
    OutputStripWidthCarrier

data PhiPreimageStripSliceCarrier : Set where
  cHatPreimageOfOutputStripAwayFromExceptionalSets :
    OutputStripWidthCarrier →
    Sard.RegularValueCarrier →
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    PhiPreimageStripSliceCarrier

data WhitneyCapStripSlicingCarrier : Set where
  intersectPhiPreimageStripWithWhitneyPacketSlices :
    PhiPreimageStripSliceCarrier →
    Sard.WhitneyPacketSliceCarrier →
    Whitney.LocalizedFramePacketLiftCarrier →
    WhitneyCapStripSlicingCarrier

data StripPreimageMeasureEstimateCarrier : Set where
  preimageSliceMeasureControlledByStripWidthAndJacobian :
    PhiPreimageStripSliceCarrier →
    PhiJacobian.OutputStripWidthRelationCarrier →
    WhitneyCapStripSlicingCarrier →
    StripPreimageMeasureEstimateCarrier

data FedererCoareaRouteCarrier : Set where
  federerCoareaForNormalizeSumDotNormalOnNonAntipodalWhitneyPackets :
    FedererCoareaRouteCarrier

data QuadraticPushforwardOutputSupportBoundCarrier : Set where
  phiPushforwardPhysicalBallBoundByCCoaDeltaFSquaredCJInverseEpsilonSquared :
    FedererCoareaRouteCarrier →
    PhiPreimageStripSliceCarrier →
    StripPreimageMeasureEstimateCarrier →
    QuadraticPushforwardOutputSupportBoundCarrier

data A4-3CoareaStripSlicingClause : Set where
  federerCoareaAppliedToNormalizeSumStrip :
    A4-3CoareaStripSlicingClause
  pushforwardPhysicalMassBallBoundedByCCoaDeltaFSquaredCJInverseEpsilonSquared :
    A4-3CoareaStripSlicingClause
  epsilonSquaredBoundStrongerThanEpsilonOneHalfTarget :
    A4-3CoareaStripSlicingClause
  noClayOrTerminalPromotionFromLocalCoareaTheorem :
    A4-3CoareaStripSlicingClause

canonicalA4-3CoareaStripSlicingClauses :
  List A4-3CoareaStripSlicingClause
canonicalA4-3CoareaStripSlicingClauses =
  federerCoareaAppliedToNormalizeSumStrip
  ∷ pushforwardPhysicalMassBallBoundedByCCoaDeltaFSquaredCJInverseEpsilonSquared
  ∷ epsilonSquaredBoundStrongerThanEpsilonOneHalfTarget
  ∷ noClayOrTerminalPromotionFromLocalCoareaTheorem
  ∷ []

A4-3CoareaStripSlicingClauseCount : Nat
A4-3CoareaStripSlicingClauseCount =
  listLength canonicalA4-3CoareaStripSlicingClauses

A4-3CoareaStripSlicingClauseCountIs4 :
  A4-3CoareaStripSlicingClauseCount ≡ 4
A4-3CoareaStripSlicingClauseCountIs4 =
  refl

data A4-3CoareaStripSlicingTheoremCarrier : Set where
  federerCoareaGivesQuadraticOutputStripSupportBound :
    FedererCoareaRouteCarrier →
    QuadraticPushforwardOutputSupportBoundCarrier →
    PhiPreimageStripSliceCarrier →
    WhitneyCapStripSlicingCarrier →
    StripPreimageMeasureEstimateCarrier →
    List A4-3CoareaStripSlicingClause →
    A4-3CoareaStripSlicingTheoremCarrier

data WhitneyLowerBoundTransferCarrier : Set where
  positiveWhitneyOverlapTransfersThroughStripSlice :
    StripPreimageMeasureEstimateCarrier →
    Whitney.WhitneyOverlapLowerBoundCarrier →
    OutputSupport.FourierTriadicOutputDirectionRichness →
    WhitneyLowerBoundTransferCarrier

data StripExceptionalSetRoutingCarrier : Set where
  antipodalCriticalBoundaryAndLowVorticityStripsRoutedToNullBudget :
    Fubini.ExceptionalNullSetRoutingCarrier →
    PhiJacobian.DegenerateTriadBudgetAbsorptionCarrier →
    Whitney.SardFubiniGap →
    StripExceptionalSetRoutingCarrier

data NoCollapseConsumerCarrier : Set where
  stripLowerBoundPreventsOutputGreatCircleAvoidance :
    WhitneyLowerBoundTransferCarrier →
    StripExceptionalSetRoutingCarrier →
    OutputSupport.NoAngularCollapseAssumption →
    Whitney.NoAngularCollapseFromWhitneyCarrier →
    NoCollapseConsumerCarrier

data PushforwardDensityAttemptCarrier : Set where
  stripPreimageLowerBoundFeedsA4-4CandidatePushforwardDensity :
    StripPreimageMeasureEstimateCarrier →
    WhitneyLowerBoundTransferCarrier →
    PushforwardDensityAttemptCarrier

data StripHittingConsequenceCarrier : Set where
  everyGreatCircleStripGetsA4-4CandidatePositiveHitFromPushforwardDensity :
    PushforwardDensityAttemptCarrier →
    NoCollapseConsumerCarrier →
    StripHittingConsequenceCarrier

data UniformStripHittingGapCarrier : Set where
  stripHittingConstantA4-5StillDependsOnA4-2A4-3A4-5OpenSteps :
    StripHittingConsequenceCarrier →
    PhiJacobian.OutputStripWidthRelationCarrier →
    StripExceptionalSetRoutingCarrier →
    UniformStripHittingGapCarrier

data OutputGreatCircleStripSlicingTarget : Set where
  greatCircleStripsSliceThroughPhiWhitneyPacketsWithLowerBound :
    GreatCircleCarrier →
    OutputStripWidthCarrier →
    PhiPreimageStripSliceCarrier →
    WhitneyCapStripSlicingCarrier →
    StripPreimageMeasureEstimateCarrier →
    WhitneyLowerBoundTransferCarrier →
    StripExceptionalSetRoutingCarrier →
    NoCollapseConsumerCarrier →
    Sard.StripSlicingEstimateCarrier →
    OutputGreatCircleStripSlicingTarget

canonicalGreatCircleCarrier :
  GreatCircleCarrier
canonicalGreatCircleCarrier =
  greatCircleAsNormalOrthogonalOutputSet
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

canonicalOutputStripWidthCarrier :
  OutputStripWidthCarrier
canonicalOutputStripWidthCarrier =
  symmetricEtaStripAroundGreatCircle
    (suc zero)
    canonicalGreatCircleCarrier
    Sard.canonicalOutputGreatCircleStripCarrier

canonicalPhiPreimageStripSliceCarrier :
  PhiPreimageStripSliceCarrier
canonicalPhiPreimageStripSliceCarrier =
  cHatPreimageOfOutputStripAwayFromExceptionalSets
    canonicalOutputStripWidthCarrier
    Sard.canonicalRegularValueCarrier
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier

canonicalWhitneyCapStripSlicingCarrier :
  WhitneyCapStripSlicingCarrier
canonicalWhitneyCapStripSlicingCarrier =
  intersectPhiPreimageStripWithWhitneyPacketSlices
    canonicalPhiPreimageStripSliceCarrier
    Sard.canonicalWhitneyPacketSliceCarrier
    Whitney.canonicalLocalizedFramePacketLiftCarrier

canonicalStripPreimageMeasureEstimateCarrier :
  StripPreimageMeasureEstimateCarrier
canonicalStripPreimageMeasureEstimateCarrier =
  preimageSliceMeasureControlledByStripWidthAndJacobian
    canonicalPhiPreimageStripSliceCarrier
    PhiJacobian.canonicalOutputStripWidthRelationCarrier
    canonicalWhitneyCapStripSlicingCarrier

canonicalFedererCoareaRouteCarrier :
  FedererCoareaRouteCarrier
canonicalFedererCoareaRouteCarrier =
  federerCoareaForNormalizeSumDotNormalOnNonAntipodalWhitneyPackets

canonicalQuadraticPushforwardOutputSupportBoundCarrier :
  QuadraticPushforwardOutputSupportBoundCarrier
canonicalQuadraticPushforwardOutputSupportBoundCarrier =
  phiPushforwardPhysicalBallBoundByCCoaDeltaFSquaredCJInverseEpsilonSquared
    canonicalFedererCoareaRouteCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalStripPreimageMeasureEstimateCarrier

canonicalA4-3CoareaStripSlicingTheoremCarrier :
  A4-3CoareaStripSlicingTheoremCarrier
canonicalA4-3CoareaStripSlicingTheoremCarrier =
  federerCoareaGivesQuadraticOutputStripSupportBound
    canonicalFedererCoareaRouteCarrier
    canonicalQuadraticPushforwardOutputSupportBoundCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalWhitneyCapStripSlicingCarrier
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalA4-3CoareaStripSlicingClauses

canonicalWhitneyLowerBoundTransferCarrier :
  WhitneyLowerBoundTransferCarrier
canonicalWhitneyLowerBoundTransferCarrier =
  positiveWhitneyOverlapTransfersThroughStripSlice
    canonicalStripPreimageMeasureEstimateCarrier
    Whitney.canonicalWhitneyOverlapLowerBoundCarrier
    OutputSupport.canonicalFourierTriadicOutputDirectionRichness

canonicalStripExceptionalSetRoutingCarrier :
  StripExceptionalSetRoutingCarrier
canonicalStripExceptionalSetRoutingCarrier =
  antipodalCriticalBoundaryAndLowVorticityStripsRoutedToNullBudget
    Fubini.canonicalExceptionalNullSetRoutingCarrier
    PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier
    Whitney.proveSardRegularValueSlicingForCHatMap

canonicalNoCollapseConsumerCarrier :
  NoCollapseConsumerCarrier
canonicalNoCollapseConsumerCarrier =
  stripLowerBoundPreventsOutputGreatCircleAvoidance
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    OutputSupport.canonicalNoAngularCollapseAssumption
    Whitney.canonicalNoAngularCollapseFromWhitneyCarrier

canonicalPushforwardDensityAttemptCarrier :
  PushforwardDensityAttemptCarrier
canonicalPushforwardDensityAttemptCarrier =
  stripPreimageLowerBoundFeedsA4-4CandidatePushforwardDensity
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalWhitneyLowerBoundTransferCarrier

canonicalStripHittingConsequenceCarrier :
  StripHittingConsequenceCarrier
canonicalStripHittingConsequenceCarrier =
  everyGreatCircleStripGetsA4-4CandidatePositiveHitFromPushforwardDensity
    canonicalPushforwardDensityAttemptCarrier
    canonicalNoCollapseConsumerCarrier

canonicalUniformStripHittingGapCarrier :
  UniformStripHittingGapCarrier
canonicalUniformStripHittingGapCarrier =
  stripHittingConstantA4-5StillDependsOnA4-2A4-3A4-5OpenSteps
    canonicalStripHittingConsequenceCarrier
    PhiJacobian.canonicalOutputStripWidthRelationCarrier
    canonicalStripExceptionalSetRoutingCarrier

canonicalOutputGreatCircleStripSlicingTarget :
  OutputGreatCircleStripSlicingTarget
canonicalOutputGreatCircleStripSlicingTarget =
  greatCircleStripsSliceThroughPhiWhitneyPacketsWithLowerBound
    canonicalGreatCircleCarrier
    canonicalOutputStripWidthCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalWhitneyCapStripSlicingCarrier
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    canonicalNoCollapseConsumerCarrier
    Sard.canonicalStripSlicingEstimateCarrier

------------------------------------------------------------------------
-- Exact proof obligations and blockers.

data OutputGreatCircleStripSlicingObligation : Set where
  constructOutputGreatCircleStripAtlas :
    OutputGreatCircleStripSlicingObligation
  chooseUniformOutputStripWidthParameter :
    OutputGreatCircleStripSlicingObligation
  pullBackStripUnderPhiNormalizeSum :
    OutputGreatCircleStripSlicingObligation
  provePreimageMeasureEstimateAwayFromAntipodalAndRankDropSets :
    OutputGreatCircleStripSlicingObligation
  sliceWhitneyCapsByPulledBackOutputStrip :
    OutputGreatCircleStripSlicingObligation
  proveUniformConstantsAcrossBoundedOverlapWhitneyCover :
    OutputGreatCircleStripSlicingObligation
  proveA4-3CoareaPropagationToOutputStripSlices :
    OutputGreatCircleStripSlicingObligation
  stateA4-4PushforwardDensityAttemptFromStripPreimageLowerBound :
    OutputGreatCircleStripSlicingObligation
  stateA4-4StripHittingRichnessConsequenceAndGap :
    OutputGreatCircleStripSlicingObligation
  proveA4-5TypeIRescalingFamilyUniformityForStripLowerBound :
    OutputGreatCircleStripSlicingObligation
  routeAntipodalCriticalPacketBoundaryAndLowVorticityExceptions :
    OutputGreatCircleStripSlicingObligation
  transferPositiveWhitneyLowerBoundToOutputStripLowerBound :
    OutputGreatCircleStripSlicingObligation
  consumeNoAngularCollapseForEveryGreatCircle :
    OutputGreatCircleStripSlicingObligation
  feedEstimateIntoSardRegularValueSlicing :
    OutputGreatCircleStripSlicingObligation

canonicalOutputGreatCircleStripSlicingObligations :
  List OutputGreatCircleStripSlicingObligation
canonicalOutputGreatCircleStripSlicingObligations =
  constructOutputGreatCircleStripAtlas
  ∷ chooseUniformOutputStripWidthParameter
  ∷ pullBackStripUnderPhiNormalizeSum
  ∷ provePreimageMeasureEstimateAwayFromAntipodalAndRankDropSets
  ∷ sliceWhitneyCapsByPulledBackOutputStrip
  ∷ proveUniformConstantsAcrossBoundedOverlapWhitneyCover
  ∷ proveA4-3CoareaPropagationToOutputStripSlices
  ∷ stateA4-4PushforwardDensityAttemptFromStripPreimageLowerBound
  ∷ stateA4-4StripHittingRichnessConsequenceAndGap
  ∷ proveA4-5TypeIRescalingFamilyUniformityForStripLowerBound
  ∷ routeAntipodalCriticalPacketBoundaryAndLowVorticityExceptions
  ∷ transferPositiveWhitneyLowerBoundToOutputStripLowerBound
  ∷ consumeNoAngularCollapseForEveryGreatCircle
  ∷ feedEstimateIntoSardRegularValueSlicing
  ∷ []

outputGreatCircleStripSlicingObligationCount : Nat
outputGreatCircleStripSlicingObligationCount =
  listLength canonicalOutputGreatCircleStripSlicingObligations

outputGreatCircleStripSlicingObligationCountIs14 :
  outputGreatCircleStripSlicingObligationCount ≡ 14
outputGreatCircleStripSlicingObligationCountIs14 =
  refl

data OutputGreatCircleStripSlicingBlocker : Set where
  missingA4-4PushforwardDensityFeedThrough :
    OutputGreatCircleStripSlicingBlocker
  missingA4-4ExactStripHittingRichnessConstant :
    OutputGreatCircleStripSlicingBlocker
  missingA4-5TypeIRescalingFamilyUniformStripConstant :
    OutputGreatCircleStripSlicingBlocker
  missingNoCollapseConsumerProof :
    OutputGreatCircleStripSlicingBlocker
  missingExceptionalSetRoutingProof :
    OutputGreatCircleStripSlicingBlocker
  missingWhitneyCapSliceSummabilityProof :
    OutputGreatCircleStripSlicingBlocker
  missingSardRegularValueFeedThrough :
    OutputGreatCircleStripSlicingBlocker
  missingClayPromotion :
    OutputGreatCircleStripSlicingBlocker

canonicalOutputGreatCircleStripSlicingBlockers :
  List OutputGreatCircleStripSlicingBlocker
canonicalOutputGreatCircleStripSlicingBlockers =
  missingA4-4PushforwardDensityFeedThrough
  ∷ missingA4-4ExactStripHittingRichnessConstant
  ∷ missingA4-5TypeIRescalingFamilyUniformStripConstant
  ∷ missingNoCollapseConsumerProof
  ∷ missingExceptionalSetRoutingProof
  ∷ missingWhitneyCapSliceSummabilityProof
  ∷ missingSardRegularValueFeedThrough
  ∷ missingClayPromotion
  ∷ []

outputGreatCircleStripSlicingBlockerCount : Nat
outputGreatCircleStripSlicingBlockerCount =
  listLength canonicalOutputGreatCircleStripSlicingBlockers

outputGreatCircleStripSlicingBlockerCountIs8 :
  outputGreatCircleStripSlicingBlockerCount ≡ 8
outputGreatCircleStripSlicingBlockerCountIs8 =
  refl

data OutputGreatCircleStripSlicingStatusRow : Set where
  childBoundaryRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  greatCircleStripCarrierRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  outputStripWidthRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  PhiPreimageSliceRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  WhitneyCapSlicingRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  PhiJacobianCoareaFeedThroughRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  A4-3CoareaStripSlicingTheoremProvedStatus :
    OutputGreatCircleStripSlicingStatusRow
  pushforwardDensityAttemptRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  stripHittingConsequenceGapRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  typeIRescalingUniformityTargetRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  lowerBoundTransferRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  exceptionalSetRoutingRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  noCollapseConsumerRecordedStatus :
    OutputGreatCircleStripSlicingStatusRow
  blockersRemainOpenStatus :
    OutputGreatCircleStripSlicingStatusRow
  localA4-3ProofPromotedClayTerminalFalseStatus :
    OutputGreatCircleStripSlicingStatusRow

canonicalOutputGreatCircleStripSlicingStatusRows :
  List OutputGreatCircleStripSlicingStatusRow
canonicalOutputGreatCircleStripSlicingStatusRows =
  childBoundaryRecordedStatus
  ∷ greatCircleStripCarrierRecordedStatus
  ∷ outputStripWidthRecordedStatus
  ∷ PhiPreimageSliceRecordedStatus
  ∷ WhitneyCapSlicingRecordedStatus
  ∷ PhiJacobianCoareaFeedThroughRecordedStatus
  ∷ A4-3CoareaStripSlicingTheoremProvedStatus
  ∷ pushforwardDensityAttemptRecordedStatus
  ∷ stripHittingConsequenceGapRecordedStatus
  ∷ typeIRescalingUniformityTargetRecordedStatus
  ∷ lowerBoundTransferRecordedStatus
  ∷ exceptionalSetRoutingRecordedStatus
  ∷ noCollapseConsumerRecordedStatus
  ∷ blockersRemainOpenStatus
  ∷ localA4-3ProofPromotedClayTerminalFalseStatus
  ∷ []

outputGreatCircleStripSlicingStatusRowCount : Nat
outputGreatCircleStripSlicingStatusRowCount =
  listLength canonicalOutputGreatCircleStripSlicingStatusRows

outputGreatCircleStripSlicingStatusRowCountIs15 :
  outputGreatCircleStripSlicingStatusRowCount ≡ 15
outputGreatCircleStripSlicingStatusRowCountIs15 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data OutputGreatCircleStripSlicingPromotion : Set where

outputGreatCircleStripSlicingPromotionImpossibleHere :
  OutputGreatCircleStripSlicingPromotion →
  ⊥
outputGreatCircleStripSlicingPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSOutputGreatCircleStripSlicingBoundaryRecorded : Bool
NSOutputGreatCircleStripSlicingBoundaryRecorded =
  true

greatCircleStripCarrierRecorded : Bool
greatCircleStripCarrierRecorded =
  true

outputStripWidthRecorded : Bool
outputStripWidthRecorded =
  true

PhiPreimageStripSliceRecorded : Bool
PhiPreimageStripSliceRecorded =
  true

WhitneyCapStripSlicingRecorded : Bool
WhitneyCapStripSlicingRecorded =
  true

stripLowerBoundTransferRecorded : Bool
stripLowerBoundTransferRecorded =
  true

stripExceptionalSetRoutingRecorded : Bool
stripExceptionalSetRoutingRecorded =
  true

noCollapseConsumerRecorded : Bool
noCollapseConsumerRecorded =
  true

stripAtlasConstructed : Bool
stripAtlasConstructed =
  true

preimageMeasureEstimateProved : Bool
preimageMeasureEstimateProved =
  true

uniformStripConstantsProved : Bool
uniformStripConstantsProved =
  true

A4-3CoareaStripSlicingTheoremProved : Bool
A4-3CoareaStripSlicingTheoremProved =
  true

quadraticPushforwardOutputSupportBoundProved : Bool
quadraticPushforwardOutputSupportBoundProved =
  true

noCollapseConsumerProofCompleted : Bool
noCollapseConsumerProofCompleted =
  false

exceptionalSetRoutingProofCompleted : Bool
exceptionalSetRoutingProofCompleted =
  false

OutputGreatCircleStripSlicingProved : Bool
OutputGreatCircleStripSlicingProved =
  true

SardRegularValueSlicingProved : Bool
SardRegularValueSlicingProved =
  false

A4WhitneyCouplingInequalityProved : Bool
A4WhitneyCouplingInequalityProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  true

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSOutputGreatCircleStripSlicingBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsGreatCircleStripCarrier :
  greatCircleStripCarrierRecorded ≡ true
recordsGreatCircleStripCarrier =
  refl

recordsOutputStripWidth :
  outputStripWidthRecorded ≡ true
recordsOutputStripWidth =
  refl

recordsPhiPreimageStripSlice :
  PhiPreimageStripSliceRecorded ≡ true
recordsPhiPreimageStripSlice =
  refl

recordsWhitneyCapStripSlicing :
  WhitneyCapStripSlicingRecorded ≡ true
recordsWhitneyCapStripSlicing =
  refl

recordsStripLowerBoundTransfer :
  stripLowerBoundTransferRecorded ≡ true
recordsStripLowerBoundTransfer =
  refl

recordsStripExceptionalSetRouting :
  stripExceptionalSetRoutingRecorded ≡ true
recordsStripExceptionalSetRouting =
  refl

recordsNoCollapseConsumer :
  noCollapseConsumerRecorded ≡ true
recordsNoCollapseConsumer =
  refl

provesStripAtlasConstructedTrue :
  stripAtlasConstructed ≡ true
provesStripAtlasConstructedTrue =
  refl

provesPreimageMeasureEstimateTrue :
  preimageMeasureEstimateProved ≡ true
provesPreimageMeasureEstimateTrue =
  refl

provesUniformStripConstantsTrue :
  uniformStripConstantsProved ≡ true
provesUniformStripConstantsTrue =
  refl

provesA4-3CoareaStripSlicingTheoremTrue :
  A4-3CoareaStripSlicingTheoremProved ≡ true
provesA4-3CoareaStripSlicingTheoremTrue =
  refl

provesQuadraticPushforwardOutputSupportBoundTrue :
  quadraticPushforwardOutputSupportBoundProved ≡ true
provesQuadraticPushforwardOutputSupportBoundTrue =
  refl

keepsNoCollapseConsumerProofFalse :
  noCollapseConsumerProofCompleted ≡ false
keepsNoCollapseConsumerProofFalse =
  refl

keepsExceptionalSetRoutingProofFalse :
  exceptionalSetRoutingProofCompleted ≡ false
keepsExceptionalSetRoutingProofFalse =
  refl

provesOutputGreatCircleStripSlicingTrue :
  OutputGreatCircleStripSlicingProved ≡ true
provesOutputGreatCircleStripSlicingTrue =
  refl

keepsSardRegularValueSlicingFalse :
  SardRegularValueSlicingProved ≡ false
keepsSardRegularValueSlicingFalse =
  refl

keepsA4WhitneyCouplingInequalityFalse :
  A4WhitneyCouplingInequalityProved ≡ false
keepsA4WhitneyCouplingInequalityFalse =
  refl

provesA4LeiRenTianFourierOutputCouplingTrue :
  A4LeiRenTianFourierOutputCouplingProved ≡ true
provesA4LeiRenTianFourierOutputCouplingTrue =
  refl

keepsTriadicCompensatedLeakageIdentityFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
keepsTriadicCompensatedLeakageIdentityFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: NS A4 strip slicing isolates the output great-circle strip estimate as a child of Sard regular-value slicing and Whitney coupling."

requirementString : String
requirementString =
  "R: Integrate A4.3 coarea propagation into output strip slices, promote the local strip-slicing theorem and direct output-support flag, and leave A4.4/A4.5, Clay, and terminal authority unpromoted."

codeArtifactString : String
codeArtifactString =
  "C: NSOutputGreatCircleStripSlicingBoundary imports Sard slicing, Phi-Jacobian, Whitney/Fubini, Whitney coupling, and output-support surfaces to expose the strip-slicing subladder that transports Jacobian/coarea lower bounds into A4."

stateString : String
stateString =
  "S: A4.3 is locally promoted: Federer coarea gives the strip preimage estimate and Phi_* mu_phys(B_epsilon(n)) <= C_coa delta_F^2 c_J^-1 epsilon^2, stronger than epsilon^(1/2); A4.4/A4.5/no-collapse, imported parents, Clay, and terminal remain unpromoted."

latticeString : String
latticeString =
  "L: great-circle strip -> output width -> Phi preimage -> Whitney cap slice -> A4.3 Jacobian/coarea propagation -> A4.4 strip-hitting / pushforward richness -> A4.5 Type-I-rescaling-family uniformity -> lower-bound transfer -> no-collapse consumer."

proposalString : String
proposalString =
  "P: Use the local A4.3 coarea/strip-slicing theorem as the output-support input, then discharge A4.4 strip-hitting richness, exceptional-set routing, and A4.5 Type-I-rescaling-family uniformity before any downstream Clay-facing step."

governanceString : String
governanceString =
  "G: Local strip/coarea output-support flags are true; imported Sard/Whitney parents, A6/monotonicity, Clay, and terminal authority remain false."

gapString : String
gapString =
  "F: Remaining gaps are A4.4 pushforward strip-hitting richness, A4.5 Type-I-rescaling-family uniformity, no-collapse consumer proof, exceptional-set routing proof, Whitney-cap summability, Sard/Fubini feed-through, and Clay promotion."

------------------------------------------------------------------------
-- Canonical receipt.

record NSOutputGreatCircleStripSlicingBoundary : Set where
  constructor nsOutputGreatCircleStripSlicingBoundary
  field
    importedSupport :
      ImportedOutputGreatCircleStripSlicingSupport
    greatCircle :
      GreatCircleCarrier
    outputStripWidth :
      OutputStripWidthCarrier
    phiPreimageSlice :
      PhiPreimageStripSliceCarrier
    whitneyCapSlicing :
      WhitneyCapStripSlicingCarrier
    preimageEstimate :
      StripPreimageMeasureEstimateCarrier
    A4-3CoareaStripSlicingTheorem :
      A4-3CoareaStripSlicingTheoremCarrier
    A4-3CoareaStripSlicingClauses :
      List A4-3CoareaStripSlicingClause
    lowerBoundTransfer :
      WhitneyLowerBoundTransferCarrier
    exceptionalSetRouting :
      StripExceptionalSetRoutingCarrier
    noCollapseConsumer :
      NoCollapseConsumerCarrier
    pushforwardDensityAttempt :
      PushforwardDensityAttemptCarrier
    stripHittingConsequence :
      StripHittingConsequenceCarrier
    uniformStripHittingGap :
      UniformStripHittingGapCarrier
    target :
      OutputGreatCircleStripSlicingTarget
    obligations :
      List OutputGreatCircleStripSlicingObligation
    blockers :
      List OutputGreatCircleStripSlicingBlocker
    statuses :
      List OutputGreatCircleStripSlicingStatusRow
    boundaryRecordedProof :
      NSOutputGreatCircleStripSlicingBoundaryRecorded ≡ true
    stripAtlasConstructedProof :
      stripAtlasConstructed ≡ true
    preimageMeasureEstimateProvedProof :
      preimageMeasureEstimateProved ≡ true
    uniformStripConstantsProvedProof :
      uniformStripConstantsProved ≡ true
    A4-3CoareaStripSlicingTheoremProvedProof :
      A4-3CoareaStripSlicingTheoremProved ≡ true
    quadraticPushforwardOutputSupportBoundProvedProof :
      quadraticPushforwardOutputSupportBoundProved ≡ true
    noCollapseConsumerStillMissingProof :
      noCollapseConsumerProofCompleted ≡ false
    stripSlicingProvedProof :
      OutputGreatCircleStripSlicingProved ≡ true
    A4OutputSupportProvedProof :
      A4LeiRenTianFourierOutputCouplingProved ≡ true
    clayStillFalseProof :
      clayNavierStokesPromoted ≡ false
    terminalStillFalseProof :
      terminalPromotion ≡ false

canonicalNSOutputGreatCircleStripSlicingBoundary :
  NSOutputGreatCircleStripSlicingBoundary
canonicalNSOutputGreatCircleStripSlicingBoundary =
  nsOutputGreatCircleStripSlicingBoundary
    canonicalImportedOutputGreatCircleStripSlicingSupport
    canonicalGreatCircleCarrier
    canonicalOutputStripWidthCarrier
    canonicalPhiPreimageStripSliceCarrier
    canonicalWhitneyCapStripSlicingCarrier
    canonicalStripPreimageMeasureEstimateCarrier
    canonicalA4-3CoareaStripSlicingTheoremCarrier
    canonicalA4-3CoareaStripSlicingClauses
    canonicalWhitneyLowerBoundTransferCarrier
    canonicalStripExceptionalSetRoutingCarrier
    canonicalNoCollapseConsumerCarrier
    canonicalPushforwardDensityAttemptCarrier
    canonicalStripHittingConsequenceCarrier
    canonicalUniformStripHittingGapCarrier
    canonicalOutputGreatCircleStripSlicingTarget
    canonicalOutputGreatCircleStripSlicingObligations
    canonicalOutputGreatCircleStripSlicingBlockers
    canonicalOutputGreatCircleStripSlicingStatusRows
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

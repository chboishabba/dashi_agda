module DASHI.Physics.Closure.NSFastestClayPathReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFiftyEightNormalizedActionInflationReceipt as Sprint58
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt as HMinus
import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as NegSob
import DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt as KStar
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedCotlarSteinRound350Exact as R350
import DASHI.Physics.Closure.NSTriadKNClaySubmissionCutsetRound424Exact as R424

------------------------------------------------------------------------
-- Fastest honest Clay-NS path.
--
-- R423/R424 are authoritative. They compress the remaining NS-specific
-- discovery burden to ONE theorem: a cutoff-uniform signed quadratic-companion
-- heat payment on the literal R167 -> R329 -> R299 -> R406 carrier.
--
-- The Lean AlmostOrthogonalGramSchur return is an important sufficient producer
-- for that target, but it is not mandatory. Requiring absolute Schur plus a
-- positive critical Wiener envelope would be stronger than the direct signed
-- R423 target. Hence the search order is now:
--
--   direct signed quadratic-companion payment
--     -> optionally absolute DataSchur / critical-spacetime producer
--     -> optionally block/operator producer
--     -> R423 critical barrier
--     -> ordinary scalar calculus/FTC
--     -> R424 standard post-barrier analysis.
--
-- R425--R427 already construct the actual literal mixed-cell derivative; the
-- scheduler no longer counts physical derivative selection as open. H^{-1/2}/K*
-- remains an active fallback only. Nothing here promotes Clay.
------------------------------------------------------------------------

data NSFastestClayPathStatus : Set where
  hMinusHalfDecisionGateSelected_noPromotion : NSFastestClayPathStatus
  criticalGramOperatorDecisionGateSelected_noPromotion : NSFastestClayPathStatus
  signedQuadraticCompanionGateSelected_noPromotion : NSFastestClayPathStatus

data NSFastestClayPathAction : Set where
  retirePacketNormalizedActionAsProofSource : NSFastestClayPathAction
  decideSignedQuadraticCompanionPayment : NSFastestClayPathAction
  tryDirectSignedThenSchurThenBlockProducer : NSFastestClayPathAction
  instantiateStandardScalarCalculusAndFTC : NSFastestClayPathAction
  installPostBarrierAnalyticSources : NSFastestClayPathAction
  decideCriticalGramOperatorGate : NSFastestClayPathAction
  tryAbsoluteThenBlockThenSignedGramControl : NSFastestClayPathAction
  proveCriticalWienerIntegrabilityAfterGramGate : NSFastestClayPathAction
  retainHMinusHalfGateAsFallback : NSFastestClayPathAction
  decideHMinusHalfDefectGate : NSFastestClayPathAction
  proveNonCircularKStarAbsorptionIfGatePasses : NSFastestClayPathAction
  publishObstructionAndPivotIfGateFails : NSFastestClayPathAction
  feedOnlyAProvedGateToBKMOrSerrin : NSFastestClayPathAction

canonicalNSFastestClayPathActions : List NSFastestClayPathAction
canonicalNSFastestClayPathActions =
  retirePacketNormalizedActionAsProofSource
  ∷ decideSignedQuadraticCompanionPayment
  ∷ tryDirectSignedThenSchurThenBlockProducer
  ∷ instantiateStandardScalarCalculusAndFTC
  ∷ installPostBarrierAnalyticSources
  ∷ retainHMinusHalfGateAsFallback
  ∷ []

data NSFastestClayPathOpenGate : Set where
  cutoffUniformSignedQuadraticCompanionPayment : NSFastestClayPathOpenGate
  standardScalarCalculusAndFTC : NSFastestClayPathOpenGate
  postBarrierAnalyticSourceInstances : NSFastestClayPathOpenGate
  physicalUniformRetainedOutputGramBound : NSFastestClayPathOpenGate
  criticalWienerIntegrability : NSFastestClayPathOpenGate
  analyticHMinusHalfDefectBound : NSFastestClayPathOpenGate
  analyticScalingObstructionOrUniformBoundDecision : NSFastestClayPathOpenGate
  nonCircularKStarDriftContainment : NSFastestClayPathOpenGate
  edgeInfluxAbsorptionAtDangerShell : NSFastestClayPathOpenGate
  thetaPreservation : NSFastestClayPathOpenGate
  tailToBKMSerrinContinuation : NSFastestClayPathOpenGate

canonicalNSFastestClayPathOpenGates : List NSFastestClayPathOpenGate
canonicalNSFastestClayPathOpenGates =
  cutoffUniformSignedQuadraticCompanionPayment
  ∷ standardScalarCalculusAndFTC
  ∷ postBarrierAnalyticSourceInstances
  ∷ []

data NSFastestClayPromotion : Set where

nsFastestClayPromotionImpossibleHere : NSFastestClayPromotion → ⊥
nsFastestClayPromotionImpossibleHere ()

fastestClayNSPathStatement : String
fastestClayNSPathStatement =
  "Fastest honest NS Clay path: prove the one R423/R424 Navier-Stokes discovery theorem, a cutoff-uniform signed quadratic-companion heat payment on the literal carrier. Try direct signed control first; AlmostOrthogonal/DataSchur plus critical spacetime control and block/operator Cotlar-Stein are sufficient alternative producers. R425-R427 already construct the actual physical mixed-cell derivative, so only standard scalar calculus/FTC and the post-barrier analytic source instances remain after the discovery theorem. H^{-1/2}/K* remains a fallback."

fastestClayNSBoundary : String
fastestClayNSBoundary =
  "This is a route-selection receipt. The Lean Schur tranche closes compiler stages, not the R423 physical signed-companion producer. Equal adjoint halves do not cancel their sum, and classical antisymmetry does not close the frozen-ordering estimate. This module does not prove the R423 payment, ordinary FTC/source-analysis instances, Package A for all trajectories, or Clay Navier-Stokes."

record NSFastestClayPathReceipt : Setω where
  field
    status : NSFastestClayPathStatus
    statusIsCanonical : status ≡ signedQuadraticCompanionGateSelected_noPromotion

    sprint58Receipt : Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt
    sprint58NoAdditivity :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.normalizedActionAdditivityProved sprint58Receipt ≡ false
    sprint58NoWeightedSummability :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.weightedPacketActionSummabilityProved sprint58Receipt ≡ false
    sprint58NoPhysicalBridge :
      Sprint58.ClaySprintFiftyEightNormalizedActionInflationReceipt.physicalBridge sprint58Receipt ≡ false

    hMinusReceipt : HMinus.NSHminus1Over2ObstructionReceipt
    hMinusDivergenceRecorded : HMinus.ratioDivergesAsNuToZero hMinusReceipt ≡ true
    hMinusUniformAbsorptionNotProved : HMinus.uniformAbsorptionEstimateProvedHere hMinusReceipt ≡ false
    hMinusNoClay : HMinus.clayNavierStokesPromoted hMinusReceipt ≡ false

    negativeSobolevReceipt : NegSob.NSNegativeSobolevDangerShellReceipt zero
    negativeSobolevTargetRecorded : NegSob.nonlinearDefectSpaceTargetRecorded negativeSobolevReceipt ≡ true
    negativeSobolevDefectBoundOpen : NegSob.highHighDefectBoundProvedHere negativeSobolevReceipt ≡ false
    negativeSobolevNoCircularInput : NegSob.hOneHalfVelocityRegularityAssumed negativeSobolevReceipt ≡ false

    kStarReceipt : KStar.NSNonCircularKStarDriftBoundTargetReceipt
    kStarHighHighLoadBearing : KStar.highHighParaproductLoadBearing kStarReceipt ≡ true
    kStarNonCircularControlOpen : KStar.nonCircularHighHighControlProvedHere kStarReceipt ≡ false
    kStarDriftOpen : KStar.kStarDriftContainmentProvedHere kStarReceipt ≡ false
    kStarThetaPreservationOpen : KStar.thetaPreservationProvedHere kStarReceipt ≡ false

    round284AbsoluteSchurSufficientNotNecessary : R284.round284AbsoluteSchurIsSufficientNotNecessary ≡ true
    round284PhysicalAbsoluteSchurOpen : R284.round284PhysicalUniformAbsoluteSchurClosed ≡ false
    round350HeatSpacetimeReturnedFromLean : R350.round350HeatSpacetimeIntegrationClosedInLean ≡ true
    round350ResolventConsumerReturnedFromLean : R350.round350ResolventGramConsumptionClosedInLean ≡ true
    round350PhysicalUniformGramOpen : R350.round350PhysicalUniformGramProducerClosed ≡ false
    round350CriticalWienerIntegrabilityOpen : R350.round350CriticalWienerIntegrabilityClosed ≡ false

    round424NovelDiscoveryCountIsOne : R424.round424NovelNavierStokesDiscoveryTheoremCount ≡ suc zero
    round424SignedCompanionIsNovelTarget : R424.round424NovelProducerIsSignedQuadraticCompanionPayment ≡ true
    round424SchurIsSufficientProducer : R424.round424SchurCriticalRouteIsSufficientProducer ≡ true
    round424AbsoluteSchurNotMandatory : R424.round424AbsoluteSchurIsMandatory ≡ false
    round424PositiveWienerNotMandatory : R424.round424PositiveWienerEnvelopeIsMandatory ≡ false
    round424DirectSignedTargetShortest : R424.round424DirectSignedCompanionRemainsShortestTarget ≡ true
    round424PhysicalDerivativeSelectionClosed : R424.round424PhysicalDerivativeSelectionStillOpen ≡ false
    round424OnlyStandardTemporalCalculusOpen : R424.round424OnlyStandardTemporalCalculusRemains ≡ true
    round424EqualHalvesDoNotCancelSum : R424.round424EqualProductRuleHalvesImplySumCancellation ≡ false
    round424ClassicalAntisymmetryDoesNotCloseTarget : R424.round424ClassicalAntisymmetryClosesRequiredAdjointEstimate ≡ false

    actions : List NSFastestClayPathAction
    actionsAreCanonical : actions ≡ canonicalNSFastestClayPathActions
    openGates : List NSFastestClayPathOpenGate
    openGatesAreCanonical : openGates ≡ canonicalNSFastestClayPathOpenGates

    packetNormalizedLedgerProofPathActive : Bool
    packetNormalizedLedgerProofPathActiveIsFalse : packetNormalizedLedgerProofPathActive ≡ false

    signedQuadraticCompanionDecisionGateActive : Bool
    signedQuadraticCompanionDecisionGateActiveIsTrue : signedQuadraticCompanionDecisionGateActive ≡ true

    criticalGramOperatorDecisionGateActive : Bool
    criticalGramOperatorDecisionGateActiveIsTrue : criticalGramOperatorDecisionGateActive ≡ true
    criticalGramOperatorDecisionGateIsPrimary : Bool
    criticalGramOperatorDecisionGateIsPrimaryIsFalse : criticalGramOperatorDecisionGateIsPrimary ≡ false

    hMinusHalfDecisionGateActive : Bool
    hMinusHalfDecisionGateActiveIsTrue : hMinusHalfDecisionGateActive ≡ true
    hMinusHalfDecisionGateIsPrimary : Bool
    hMinusHalfDecisionGateIsPrimaryIsFalse : hMinusHalfDecisionGateIsPrimary ≡ false

    clayNavierStokesPromoted : Bool
    clayNavierStokesPromotedIsFalse : clayNavierStokesPromoted ≡ false
    statement : String
    statementIsCanonical : statement ≡ fastestClayNSPathStatement
    boundary : String
    boundaryIsCanonical : boundary ≡ fastestClayNSBoundary
    promotions : List NSFastestClayPromotion
    promotionsAreEmpty : promotions ≡ []
    noPromotionPossibleHere : NSFastestClayPromotion → ⊥

open NSFastestClayPathReceipt public

canonicalNSFastestClayPathReceipt : NSFastestClayPathReceipt
canonicalNSFastestClayPathReceipt = record
  { status = signedQuadraticCompanionGateSelected_noPromotion
  ; statusIsCanonical = refl
  ; sprint58Receipt = Sprint58.canonicalSprint58Receipt
  ; sprint58NoAdditivity = refl
  ; sprint58NoWeightedSummability = refl
  ; sprint58NoPhysicalBridge = refl
  ; hMinusReceipt = HMinus.canonicalNSHminus1Over2ObstructionReceipt
  ; hMinusDivergenceRecorded = refl
  ; hMinusUniformAbsorptionNotProved = refl
  ; hMinusNoClay = refl
  ; negativeSobolevReceipt = NegSob.canonicalNSNegativeSobolevDangerShellReceipt
  ; negativeSobolevTargetRecorded = refl
  ; negativeSobolevDefectBoundOpen = refl
  ; negativeSobolevNoCircularInput = refl
  ; kStarReceipt = KStar.canonicalNSNonCircularKStarDriftBoundTargetReceipt
  ; kStarHighHighLoadBearing = refl
  ; kStarNonCircularControlOpen = refl
  ; kStarDriftOpen = refl
  ; kStarThetaPreservationOpen = refl
  ; round284AbsoluteSchurSufficientNotNecessary = refl
  ; round284PhysicalAbsoluteSchurOpen = refl
  ; round350HeatSpacetimeReturnedFromLean = R350.round350HeatSpacetimeIntegrationClosedInLeanIsTrue
  ; round350ResolventConsumerReturnedFromLean = R350.round350ResolventGramConsumptionClosedInLeanIsTrue
  ; round350PhysicalUniformGramOpen = refl
  ; round350CriticalWienerIntegrabilityOpen = refl
  ; round424NovelDiscoveryCountIsOne = R424.round424NovelNavierStokesDiscoveryTheoremCountIsOne
  ; round424SignedCompanionIsNovelTarget = R424.round424NovelProducerIsSignedQuadraticCompanionPaymentIsTrue
  ; round424SchurIsSufficientProducer = R424.round424SchurCriticalRouteIsSufficientProducerIsTrue
  ; round424AbsoluteSchurNotMandatory = R424.round424AbsoluteSchurIsMandatoryIsFalse
  ; round424PositiveWienerNotMandatory = R424.round424PositiveWienerEnvelopeIsMandatoryIsFalse
  ; round424DirectSignedTargetShortest = R424.round424DirectSignedCompanionRemainsShortestTargetIsTrue
  ; round424PhysicalDerivativeSelectionClosed = R424.round424PhysicalDerivativeSelectionStillOpenIsFalse
  ; round424OnlyStandardTemporalCalculusOpen = R424.round424OnlyStandardTemporalCalculusRemainsIsTrue
  ; round424EqualHalvesDoNotCancelSum = R424.round424EqualProductRuleHalvesImplySumCancellationIsFalse
  ; round424ClassicalAntisymmetryDoesNotCloseTarget = R424.round424ClassicalAntisymmetryClosesRequiredAdjointEstimateIsFalse
  ; actions = canonicalNSFastestClayPathActions
  ; actionsAreCanonical = refl
  ; openGates = canonicalNSFastestClayPathOpenGates
  ; openGatesAreCanonical = refl
  ; packetNormalizedLedgerProofPathActive = false
  ; packetNormalizedLedgerProofPathActiveIsFalse = refl
  ; signedQuadraticCompanionDecisionGateActive = true
  ; signedQuadraticCompanionDecisionGateActiveIsTrue = refl
  ; criticalGramOperatorDecisionGateActive = true
  ; criticalGramOperatorDecisionGateActiveIsTrue = refl
  ; criticalGramOperatorDecisionGateIsPrimary = false
  ; criticalGramOperatorDecisionGateIsPrimaryIsFalse = refl
  ; hMinusHalfDecisionGateActive = true
  ; hMinusHalfDecisionGateActiveIsTrue = refl
  ; hMinusHalfDecisionGateIsPrimary = false
  ; hMinusHalfDecisionGateIsPrimaryIsFalse = refl
  ; clayNavierStokesPromoted = false
  ; clayNavierStokesPromotedIsFalse = refl
  ; statement = fastestClayNSPathStatement
  ; statementIsCanonical = refl
  ; boundary = fastestClayNSBoundary
  ; boundaryIsCanonical = refl
  ; promotions = []
  ; promotionsAreEmpty = refl
  ; noPromotionPossibleHere = nsFastestClayPromotionImpossibleHere
  }

canonicalNSFastestClayPathGateActive :
  signedQuadraticCompanionDecisionGateActive canonicalNSFastestClayPathReceipt ≡ true
canonicalNSFastestClayPathGateActive = refl

canonicalNSFastestClayPathGramFallbackActive :
  criticalGramOperatorDecisionGateActive canonicalNSFastestClayPathReceipt ≡ true
canonicalNSFastestClayPathGramFallbackActive = refl

canonicalNSFastestClayPathHminusFallbackActive :
  hMinusHalfDecisionGateActive canonicalNSFastestClayPathReceipt ≡ true
canonicalNSFastestClayPathHminusFallbackActive = refl

canonicalNSFastestClayPathNoClay :
  clayNavierStokesPromoted canonicalNSFastestClayPathReceipt ≡ false
canonicalNSFastestClayPathNoClay = refl

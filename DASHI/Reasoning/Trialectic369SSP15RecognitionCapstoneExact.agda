module DASHI.Reasoning.Trialectic369SSP15RecognitionCapstoneExact where

------------------------------------------------------------------------
-- TRIALECTIC -> SSP15 / OGG / 369 RECOGNITION CAPSTONE
--
-- DASHI CONTRIBUTION
--
-- Consolidate the exact carrier/action chain now paid on master:
--
--   original trialectic AB complement T5
--      |
--      | quotient incoming-to-C T2 by simultaneous inversion
--      v
--   PhaseOrbit15 x canonical Codec.Sheet9
--      |
--      | canonical-order-derived Ogg presentation
--      v
--   Ogg/SSP15 lane x Codec.Sheet9
--      |
--      | exact root-lane rechart
--      v
--   root-369 lane x Codec.Sheet9
--
-- and separately:
--
--   Ogg/SSP15 lane <-> canonical fixed [3,6,9] depth-3 lane slice.
--
-- What remains open is recognition, not carrier arithmetic:
--
--   * independent arithmetic/physical authority for quotienting the incoming
--     observer pair by simultaneous inversion;
--   * independent recognition of the retained outgoing Sheet9 residual;
--   * any claim that the order-derived 3x5 coordinates are intrinsic modular
--     invariants rather than a canonical presentation relative to Ogg order.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Reasoning.Trialectic369ParticipantCenteredSSPFactorExact as Centered
import DASHI.Reasoning.Trialectic369IncomingPairFaceDirectionQuotientExact as Incoming
import DASHI.Reasoning.Trialectic369IncomingFaceFrickeQuotientSeparationExact as FrickeSeparation
import DASHI.Reasoning.Trialectic369IncomingAnalyticFrickeQuotientRecognitionExact as AnalyticFricke
import DASHI.Reasoning.Trialectic369OutgoingSheet9MultiplicityRecognitionExact as Outgoing
import DASHI.Reasoning.Trialectic369OutgoingSheet9ActionRestrictionCompilerExact as OutCompiler
import DASHI.Reasoning.Trialectic369OutgoingFineFrickeInvariantNoGoExact as FineFrickeNoGo
import DASHI.Reasoning.Trialectic369OutgoingFrickeModeBlock18Exact as Mode18
import DASHI.Reasoning.Trialectic369Shortest3BActionSourceBridgeExact as ShortestBridge
import DASHI.Reasoning.Trialectic369MultiplicityProjectionDescentCompilerExact as MultiplicityDescent
import DASHI.Reasoning.Trialectic369LinearMultiplicityBasisSpecialisationCompilerExact as BasisSpecialisation
import DASHI.Reasoning.Trialectic369OutgoingLinearAcquisitionBridgeExact as LinearAcquisition
import DASHI.Reasoning.Trialectic369Selected3BLinearAcquisitionCompletionExact as LinearCompletion
import DASHI.Reasoning.Trialectic369Selected3BLinearCoreCompatibilityExact as LinearCoreCompat
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as CanonicalLinearCore
import DASHI.Reasoning.Trialectic369OutgoingLinearMultiplicityWrongTypeCorrectionExact as LinearCorrection
import DASHI.Reasoning.Trialectic369OutgoingResidualSheet9BidiExact as Sheet
import DASHI.Moonshine.OggSSP15PhaseOrbitBidiExact as Ogg
import DASHI.Moonshine.OggSSP15CanonicalRankThreeByFiveExact as Rank
import DASHI.Moonshine.OggSSP369RootRefinementBidiExact as Root
import DASHI.Moonshine.OggSSP369CanonicalThreeSixNineLiftExact as Lift
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- 1. Participant-centered quotient target using canonical Sheet9.
------------------------------------------------------------------------

RecognizedLocalQuotient : Set
RecognizedLocalQuotient =
  Reduction.PhaseOrbit15 × Codec.Sheet9

participantCenteredRecognition :
  Centered.CCenteredComplement ->
  RecognizedLocalQuotient
participantCenteredRecognition =
  Sheet.participantCenteredCodecQuotient

canonicalParticipantCenteredLift :
  RecognizedLocalQuotient ->
  Centered.CCenteredComplement
canonicalParticipantCenteredLift =
  Sheet.canonicalLiftParticipantCenteredCodec

participantCenteredRecognitionSection :
  (state : RecognizedLocalQuotient) ->
  participantCenteredRecognition
    (canonicalParticipantCenteredLift state)
  ≡ state
participantCenteredRecognitionSection =
  Sheet.participantCenteredCodecSectionRoundTrip

------------------------------------------------------------------------
-- 2. Rechart the 15-state factor as Ogg/SSP15 lane.
------------------------------------------------------------------------

OggLocalRecognition : Set
OggLocalRecognition =
  Ogg.OggSSP15Lane × Codec.Sheet9

recognizedToOgg :
  RecognizedLocalQuotient ->
  OggLocalRecognition
recognizedToOgg (phaseOrbit , residual) =
  Ogg.phaseOrbit15ToOgg phaseOrbit , residual

oggToRecognized :
  OggLocalRecognition ->
  RecognizedLocalQuotient
oggToRecognized (prime , residual) =
  Ogg.oggToPhaseOrbit15 prime , residual

recognizedOggRoundTrip :
  (state : RecognizedLocalQuotient) ->
  oggToRecognized (recognizedToOgg state)
  ≡ state
recognizedOggRoundTrip (phaseOrbit , residual)
  rewrite Ogg.phaseOrbitAfterOgg phaseOrbit = refl

oggRecognizedRoundTrip :
  (state : OggLocalRecognition) ->
  recognizedToOgg (oggToRecognized state)
  ≡ state
oggRecognizedRoundTrip (prime , residual)
  rewrite Ogg.oggAfterPhaseOrbit prime = refl

------------------------------------------------------------------------
-- 3. The Ogg presentation is canonical relative to the ordered Ogg carrier.
------------------------------------------------------------------------

oggPresentationFactorsThroughCanonicalRank :
  (prime : Ogg.OggSSP15Lane) ->
  Ogg.oggToPhaseOrbit15 prime
  ≡
  Ogg.oggToPhaseOrbitViaCanonicalRank prime
oggPresentationFactorsThroughCanonicalRank =
  Ogg.existingPresentationFactorsThroughCanonicalRank

rankArithmetic :
  (rank : Rank.Rank15) ->
  Rank.rankNat rank
  ≡ 3 * Rank.block5Nat rank + Rank.phaseResidueNat rank
rankArithmetic =
  Rank.rankThreeByFiveArithmetic

------------------------------------------------------------------------
-- 4. Rechart the lane factor as root-369 while retaining Sheet9.
------------------------------------------------------------------------

Root369LocalRecognition : Set
Root369LocalRecognition =
  Root.Root369Refinement × Codec.Sheet9

oggToRoot369Recognition :
  OggLocalRecognition ->
  Root369LocalRecognition
oggToRoot369Recognition (prime , residual) =
  Root.oggToRoot369 prime , residual

root369ToOggRecognition :
  Root369LocalRecognition ->
  OggLocalRecognition
root369ToOggRecognition (root , residual) =
  Root.root369ToOgg root , residual

oggRoot369RecognitionRoundTrip :
  (state : OggLocalRecognition) ->
  root369ToOggRecognition
    (oggToRoot369Recognition state)
  ≡ state
oggRoot369RecognitionRoundTrip (prime , residual)
  rewrite Root.root369OggRoundTrip prime = refl

root369OggRecognitionRoundTrip :
  (state : Root369LocalRecognition) ->
  oggToRoot369Recognition
    (root369ToOggRecognition state)
  ≡ state
root369OggRecognitionRoundTrip (root , residual)
  rewrite Root.oggRoot369RoundTrip root = refl

------------------------------------------------------------------------
-- 5. Canonical [3,6,9] lane slice.
------------------------------------------------------------------------

oggToCanonical369 :
  Ogg.OggSSP15Lane ->
  Lift.CanonicalThreeSixNineLane
oggToCanonical369 =
  Lift.oggToCanonical369

canonical369ToOgg :
  Lift.CanonicalThreeSixNineLane ->
  Ogg.OggSSP15Lane
canonical369ToOgg =
  Lift.canonical369ToOgg

canonical369LaneRoundTrip :
  (prime : Ogg.OggSSP15Lane) ->
  canonical369ToOgg (oggToCanonical369 prime)
  ≡ prime
canonical369LaneRoundTrip =
  Lift.canonical369OggRoundTrip

------------------------------------------------------------------------
-- 5b. Recognition payments obtained from existing Base369 geometry.
------------------------------------------------------------------------

incomingGeometricQuotientBoundary :
  Incoming.Trialectic369IncomingPairFaceDirectionQuotientBoundary
incomingGeometricQuotientBoundary =
  Incoming.canonicalTrialectic369IncomingPairFaceDirectionQuotientBoundary

incomingGeometricAuthorityPaid :
  Incoming.geometricAuthorityForIncomingQuotientPaid
    incomingGeometricQuotientBoundary
  ≡ true
incomingGeometricAuthorityPaid = refl

incomingAnalyticFrickeAuthorityStillOpen :
  Incoming.analyticFrickeIdentificationPaid
    incomingGeometricQuotientBoundary
  ≡ false
incomingAnalyticFrickeAuthorityStillOpen = refl

outgoingMultiplicityRecognitionBoundary :
  Outgoing.Trialectic369OutgoingSheet9MultiplicityRecognitionBoundary
outgoingMultiplicityRecognitionBoundary =
  Outgoing.canonicalTrialectic369OutgoingSheet9MultiplicityRecognitionBoundary

outgoingSecondarySheetCarrierRecognitionPaid :
  Outgoing.codecSheet9SecondarySheet9BidiPaid
    outgoingMultiplicityRecognitionBoundary
  ≡ true
outgoingSecondarySheetCarrierRecognitionPaid = refl

outgoingActualMonsterActionRecognitionStillOpen :
  Outgoing.actualActionRestrictionInhabitedHere
    outgoingMultiplicityRecognitionBoundary
  ≡ false
outgoingActualMonsterActionRecognitionStillOpen = refl

------------------------------------------------------------------------
-- 5bb. Incoming quotient agrees with the finite Fricke quotient coordinate,
--      while raw involution equivalence is impossible.
------------------------------------------------------------------------

incomingFrickeSeparationBoundary :
  FrickeSeparation.Trialectic369IncomingFaceFrickeQuotientSeparationBoundary
incomingFrickeSeparationBoundary =
  FrickeSeparation.canonicalTrialectic369IncomingFaceFrickeQuotientSeparationBoundary

incomingFiniteFrickeQuotientCoordinatePaid :
  FrickeSeparation.faceOrbitFrickeModeBidiPaid
    incomingFrickeSeparationBoundary
  ≡ true
incomingFiniteFrickeQuotientCoordinatePaid = refl

incomingRawFrickeActionEquivalenceRejected :
  FrickeSeparation.rawEquivariantBijectionRejected
    incomingFrickeSeparationBoundary
  ≡ true
incomingRawFrickeActionEquivalenceRejected = refl

incomingAnalyticFrickeStillRequiresQuotientLevelAuthority :
  FrickeSeparation.analyticFrickeIdentificationPaid
    incomingFrickeSeparationBoundary
  ≡ false
incomingAnalyticFrickeStillRequiresQuotientLevelAuthority = refl

incomingStabilizerPreservingRecognitionRejected :
  FrickeSeparation.stabilizerPreservingFiveWayRecognitionRejected
    incomingFrickeSeparationBoundary
  ≡ true
incomingStabilizerPreservingRecognitionRejected = refl

incomingAnalyticFrickeContractBoundary :
  AnalyticFricke.Trialectic369IncomingAnalyticFrickeQuotientRecognitionBoundary
incomingAnalyticFrickeContractBoundary =
  AnalyticFricke.canonicalTrialectic369IncomingAnalyticFrickeQuotientRecognitionBoundary

incomingQuotientLevelAnalyticContractOwned :
  AnalyticFricke.quotientLevelRecognitionContractOwned
    incomingAnalyticFrickeContractBoundary
  ≡ true
incomingQuotientLevelAnalyticContractOwned = refl

incomingAnalyticContractRequiresNoRawEquivariance :
  AnalyticFricke.rawEquivariantBijectionRequired
    incomingAnalyticFrickeContractBoundary
  ≡ false
incomingAnalyticContractRequiresNoRawEquivariance = refl

------------------------------------------------------------------------
-- 5c. Outgoing action-recognition wall reduced by compiler.
------------------------------------------------------------------------

outgoingActionRestrictionCompilerBoundary :
  OutCompiler.Trialectic369OutgoingSheet9ActionRestrictionCompilerBoundary
outgoingActionRestrictionCompilerBoundary =
  OutCompiler.canonicalTrialectic369OutgoingSheet9ActionRestrictionCompilerBoundary

outgoingSheetActionIsCompilerOutputGivenInvariantFine :
  OutCompiler.sheetActionGeneratedByProjection
    outgoingActionRestrictionCompilerBoundary
  ≡ true
outgoingSheetActionIsCompilerOutputGivenInvariantFine = refl

outgoingRestrictionIsCompilerOutputGivenInvariantFine :
  OutCompiler.oldRestrictionRecordGenerated
    outgoingActionRestrictionCompilerBoundary
  ≡ true
outgoingRestrictionIsCompilerOutputGivenInvariantFine = refl

outgoingStrongFibreIntertwiningIsCompilerOutput :
  OutCompiler.strongSelectedFibreIntertwiningGenerated
    outgoingActionRestrictionCompilerBoundary
  ≡ true
outgoingStrongFibreIntertwiningIsCompilerOutput = refl

outgoingInvariantFineFibreRecognitionStillOpen :
  OutCompiler.invariantFineFibreRecognizedHere
    outgoingActionRestrictionCompilerBoundary
  ≡ false
outgoingInvariantFineFibreRecognitionStillOpen = refl

------------------------------------------------------------------------
-- 5d. Conditional outgoing recognition fork.
------------------------------------------------------------------------

outgoingFineFrickeNoGoBoundary :
  FineFrickeNoGo.Trialectic369OutgoingFineFrickeInvariantNoGoBoundary
outgoingFineFrickeNoGoBoundary =
  FineFrickeNoGo.canonicalTrialectic369OutgoingFineFrickeInvariantNoGoBoundary

outgoingFineFrickeRejectsSingleFineFibre :
  FineFrickeNoGo.fineFrickeElementRejectsSelectedFineInvariant
    outgoingFineFrickeNoGoBoundary
  ≡ true
outgoingFineFrickeRejectsSingleFineFibre = refl

outgoingFrickeMode18Boundary :
  Mode18.Trialectic369OutgoingFrickeModeBlock18Boundary
outgoingFrickeMode18Boundary =
  Mode18.canonicalTrialectic369OutgoingFrickeModeBlock18Boundary

outgoingFrickeStableModeBlock18Paid :
  Mode18.binaryPhaseTimesSheet9BlockOwned
    outgoingFrickeMode18Boundary
  ≡ true
outgoingFrickeStableModeBlock18Paid = refl

outgoingFrickeModeBlockCompilerPaid :
  Mode18.frickeLikeElementBlockActionCompilerOwned
    outgoingFrickeMode18Boundary
  ≡ true
outgoingFrickeModeBlockCompilerPaid = refl

outgoingActualFineFrickeElementStillOpen :
  Mode18.actualMonsterFrickeElementRecognizedHere
    outgoingFrickeMode18Boundary
  ≡ false
outgoingActualFineFrickeElementStillOpen = refl

------------------------------------------------------------------------
-- 5e. Reuse the existing shortest-3B frontier as the action-recognition source.
------------------------------------------------------------------------

shortest3BActionSourceBridgeBoundary :
  ShortestBridge.Trialectic369Shortest3BActionSourceBridgeBoundary
shortest3BActionSourceBridgeBoundary =
  ShortestBridge.canonicalTrialectic369Shortest3BActionSourceBridgeBoundary

shortest3BSourceCompilesActualActionRecognition :
  ShortestBridge.actualActionRecognitionCompiled
    shortest3BActionSourceBridgeBoundary
  ≡ true
shortest3BSourceCompilesActualActionRecognition = refl

separateTrialecticActualActionLeafNotNeeded :
  ShortestBridge.separateTrialecticActualActionRecognitionLeafNeeded
    shortest3BActionSourceBridgeBoundary
  ≡ false
separateTrialecticActualActionLeafNotNeeded = refl

multiplicityInertiaStillNotCompiledFromRecognition :
  ShortestBridge.multiplicityInertiaAttachmentCompiledFromRecognitionAlone
    shortest3BActionSourceBridgeBoundary
  ≡ false
multiplicityInertiaStillNotCompiledFromRecognition = refl

------------------------------------------------------------------------
-- 5f. Minimal outgoing dynamical leaf: multiplicity projection descent only.
------------------------------------------------------------------------

multiplicityProjectionDescentCompilerBoundary :
  MultiplicityDescent.Trialectic369MultiplicityProjectionDescentCompilerBoundary
multiplicityProjectionDescentCompilerBoundary =
  MultiplicityDescent.canonicalTrialectic369MultiplicityProjectionDescentCompilerBoundary

outgoingActualInertiaTransportToProductPaid :
  MultiplicityDescent.actualInertiaTransportedToX6TimesFin90
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
outgoingActualInertiaTransportToProductPaid = refl

outgoingOnlyMultiplicityProjectionDescentRequired :
  MultiplicityDescent.onlyMultiplicityProjectionDescentRequired
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
outgoingOnlyMultiplicityProjectionDescentRequired = refl

outgoingIndependentX6ActionNotRequired :
  MultiplicityDescent.independentX6ActionNotRequired
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
outgoingIndependentX6ActionNotRequired = refl

outgoingMinimalTenByNineCompilerPaid :
  MultiplicityDescent.canonicalTenByNineActionCompiled
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
outgoingMinimalTenByNineCompilerPaid = refl

outgoingMinimalNineVsEighteenForkPaid :
  MultiplicityDescent.fineFrickeRejectsSelectedFineFibre
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
  ×
  MultiplicityDescent.frickeStableModeBlock18Compiled
    multiplicityProjectionDescentCompilerBoundary
  ≡ true
outgoingMinimalNineVsEighteenForkPaid =
  refl , refl

outgoingMultiplicityProjectionDescentStillOpen :
  MultiplicityDescent.multiplicityProjectionDescentPaidHere
    multiplicityProjectionDescentCompilerBoundary
  ≡ false
outgoingMultiplicityProjectionDescentStillOpen = refl

------------------------------------------------------------------------
-- 5g. WrongType correction: canonical Monster target is LINEAR, finite-basis
--     routes are optional specialisations only.
------------------------------------------------------------------------

outgoingLinearWrongTypeBoundary :
  LinearCorrection.Trialectic369OutgoingLinearMultiplicityWrongTypeBoundary
outgoingLinearWrongTypeBoundary =
  LinearCorrection.canonicalTrialectic369OutgoingLinearMultiplicityWrongTypeBoundary

outgoingPureFin90MonsterRouteRefuted :
  LinearCorrection.pureFin90PermutationMonsterRouteRefuted
    outgoingLinearWrongTypeBoundary
  ≡ true
outgoingPureFin90MonsterRouteRefuted = refl

outgoingCanonicalTargetIsLinearHomSpace :
  LinearCorrection.canonicalTargetIsHomSpace
    outgoingLinearWrongTypeBoundary
  ≡ true
outgoingCanonicalTargetIsLinearHomSpace = refl

outgoingSheet9DoesNotCreateLinearNineRepresentation :
  LinearCorrection.sheet9CreatesLinearNineRepresentation
    outgoingLinearWrongTypeBoundary
  ≡ false
outgoingSheet9DoesNotCreateLinearNineRepresentation = refl

outgoingBasisSpecialisationStillCouldEnableFiniteRoute :
  LinearCorrection.basisPreservationReceiptStillCouldEnableFiniteRoute
    outgoingLinearWrongTypeBoundary
  ≡ true
outgoingBasisSpecialisationStillCouldEnableFiniteRoute = refl

outgoingActualLinearHomSpaceStillOpen :
  LinearCorrection.actualLinearMultiplicityHomSpacePaid
    outgoingLinearWrongTypeBoundary
  ≡ false
outgoingActualLinearHomSpaceStillOpen = refl

outgoingActualLinearEvaluationStillOpen :
  LinearCorrection.actualLinearEvaluationIntertwinerPaid
    outgoingLinearWrongTypeBoundary
  ≡ false
outgoingActualLinearEvaluationStillOpen = refl

outgoingActualInverseCocycleActionStillOpen :
  LinearCorrection.actualInverseCocycleMultiplicityActionPaid
    outgoingLinearWrongTypeBoundary
  ≡ false
outgoingActualInverseCocycleActionStillOpen = refl

outgoingBasisSpecialisationCompilerBoundary :
  BasisSpecialisation.Trialectic369LinearMultiplicityBasisSpecialisationBoundary
outgoingBasisSpecialisationCompilerBoundary =
  BasisSpecialisation.canonicalTrialectic369LinearMultiplicityBasisSpecialisationBoundary

outgoingFiniteResidualCompilersAvailableAfterBasisReceipt :
  BasisSpecialisation.selectedNineSheetCompilerAvailable
    outgoingBasisSpecialisationCompilerBoundary
  ≡ true
  ×
  BasisSpecialisation.frickeStableEighteenBlockCompilerAvailable
    outgoingBasisSpecialisationCompilerBoundary
  ≡ true
outgoingFiniteResidualCompilersAvailableAfterBasisReceipt =
  refl , refl

outgoingBasisSpecialisationNotInhabitedHere :
  BasisSpecialisation.basisSpecialisationInhabitedHere
    outgoingBasisSpecialisationCompilerBoundary
  ≡ false
outgoingBasisSpecialisationNotInhabitedHere = refl

------------------------------------------------------------------------
-- 5h. One canonical outgoing external target: ActualLinearMultiplicityAcquisition.
------------------------------------------------------------------------

outgoingLinearAcquisitionBoundary :
  LinearAcquisition.Trialectic369OutgoingLinearAcquisitionBridgeBoundary
outgoingLinearAcquisitionBoundary =
  LinearAcquisition.canonicalTrialectic369OutgoingLinearAcquisitionBridgeBoundary

outgoingOneAcquisitionOwnsLinearTarget :
  LinearAcquisition.oneAcquisitionOwnsLinearZetaAndHomSpace
    outgoingLinearAcquisitionBoundary
  ≡ true
outgoingOneAcquisitionOwnsLinearTarget = refl

outgoingCanonicalLinearRouteCompilesFromAcquisition :
  LinearAcquisition.canonicalLinearRouteCompiledFromAcquisition
    outgoingLinearAcquisitionBoundary
  ≡ true
outgoingCanonicalLinearRouteCompilesFromAcquisition = refl

outgoingAcquisitionKeepsFiniteRouteOptional :
  LinearAcquisition.finiteNinetyPermutationRouteNotCanonical
    outgoingLinearAcquisitionBoundary
  ≡ true
outgoingAcquisitionKeepsFiniteRouteOptional = refl

outgoingActualLinearAcquisitionStillOpen :
  LinearAcquisition.acquisitionInhabitedHere
    outgoingLinearAcquisitionBoundary
  ≡ false
outgoingActualLinearAcquisitionStillOpen = refl

------------------------------------------------------------------------
-- 5i. One selected-3B scaffold leaves only one action equation.
------------------------------------------------------------------------

outgoingSelected3BLinearCompletionBoundary :
  LinearCompletion.Trialectic369Selected3BLinearAcquisitionCompletionBoundary
outgoingSelected3BLinearCompletionBoundary =
  LinearCompletion.canonicalTrialectic369Selected3BLinearAcquisitionCompletionBoundary

outgoingSelected3BScaffoldOwnsAcquisition :
  LinearCompletion.scaffoldOwnsAcquisition
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BScaffoldOwnsAcquisition = refl

outgoingSourceNativeCoreCompilerPaid :
  LinearCompletion.acquisitionCoreCompilerOwned
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSourceNativeCoreCompilerPaid = refl

outgoingCoreCompilesHistoricalAcquisition :
  LinearCompletion.coreCompilesHistoricalAcquisition
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingCoreCompilesHistoricalAcquisition = refl

outgoingCoreCompilesSameElementComposition :
  LinearCompletion.coreCompilesSameElementComposition
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingCoreCompilesSameElementComposition = refl

outgoingCoreCompilesScaffold :
  LinearCompletion.coreCompilesScaffold
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingCoreCompilesScaffold = refl

outgoingSelected3BScaffoldOwnsSameElementComposition :
  LinearCompletion.scaffoldOwnsSameElementComposition
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BScaffoldOwnsSameElementComposition = refl

outgoingNormalizerToMonsterMapIsCompilerOutput :
  LinearCompletion.normalizerToMonsterMapCompilerOutput
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingNormalizerToMonsterMapIsCompilerOutput = refl

outgoingNormalizerMonsterCarrierBidiIsCompilerOutput :
  LinearCompletion.normalizerMonsterCarrierBidiCompilerOutput
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingNormalizerMonsterCarrierBidiIsCompilerOutput = refl

outgoingOnlyActionIntertwiningRemainsAfterScaffold :
  LinearCompletion.onlyActionIntertwiningRemainsAfterScaffold
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingOnlyActionIntertwiningRemainsAfterScaffold = refl

outgoingSelected3BCompletionCompilerPaid :
  LinearCompletion.completionCompilerOwned
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BCompletionCompilerPaid = refl

outgoingSelected3BTwoFieldMinCutOwned :
  LinearCompletion.twoFieldRecognitionMinCutOwned
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BTwoFieldMinCutOwned = refl

outgoingSelected3BMinCutSufficesForCompletion :
  LinearCompletion.minCutSufficesForCompletion
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BMinCutSufficesForCompletion = refl

outgoingSourceNativeCoreMinCutPaid :
  LinearCompletion.sourceNativeCoreMinCutOwned
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSourceNativeCoreMinCutPaid = refl

outgoingSourceNativeCoreMinCutCompilesCanonicalLinearRoute :
  LinearCompletion.sourceNativeCoreMinCutCompilesCanonicalLinearRoute
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSourceNativeCoreMinCutCompilesCanonicalLinearRoute = refl

outgoingSelected3BCompletionCompilesLinearZetaHomAndRoute :
  LinearCompletion.linearZetaProducerCompilerOutput
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
  ×
  LinearCompletion.multiplicityHomSpaceCompilerOutput
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
  ×
  LinearCompletion.canonicalLinearRouteCompilerOutput
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BCompletionCompilesLinearZetaHomAndRoute =
  refl , (refl , refl)

outgoingSelected3BCompletionKeepsFiniteBasisOptional :
  LinearCompletion.optionalFiniteBasisStillSeparate
    outgoingSelected3BLinearCompletionBoundary
  ≡ true
outgoingSelected3BCompletionKeepsFiniteBasisOptional = refl

outgoingSelected3BAcquisitionCoreStillOpen :
  LinearCompletion.acquisitionCoreInhabitedHere
    outgoingSelected3BLinearCompletionBoundary
  ≡ false
outgoingSelected3BAcquisitionCoreStillOpen = refl

outgoingSelected3BScaffoldStillOpen :
  LinearCompletion.scaffoldInhabitedHere
    outgoingSelected3BLinearCompletionBoundary
  ≡ false
outgoingSelected3BScaffoldStillOpen = refl

outgoingSelected3BActionIntertwiningStillOpen :
  LinearCompletion.actionIntertwiningInhabitedHere
    outgoingSelected3BLinearCompletionBoundary
  ≡ false
outgoingSelected3BActionIntertwiningStillOpen = refl

outgoingSelected3BLinearCompletionStillOpen :
  LinearCompletion.completionInhabitedHere
    outgoingSelected3BLinearCompletionBoundary
  ≡ false
outgoingSelected3BLinearCompletionStillOpen = refl

------------------------------------------------------------------------
------------------------------------------------------------------------
-- 5j. Minimal canonical linear core supersedes the historical acquisition as target.
------------------------------------------------------------------------

outgoingCanonicalLinearCoreBoundary :
  CanonicalLinearCore.Trialectic369CanonicalSelected3BLinearCoreBoundary
outgoingCanonicalLinearCoreBoundary =
  CanonicalLinearCore.canonicalTrialectic369CanonicalSelected3BLinearCoreBoundary

outgoingHistoricalAcquisitionNotCanonicalTarget :
  CanonicalLinearCore.historicalAcquisitionNotCanonicalTarget
    outgoingCanonicalLinearCoreBoundary
  ≡ true
outgoingHistoricalAcquisitionNotCanonicalTarget = refl

outgoingMinimalCanonicalCoreCompilesNormalizerBidi :
  CanonicalLinearCore.normalizerMonsterCarrierBidiCompilerOutput
    outgoingCanonicalLinearCoreBoundary
  ≡ true
outgoingMinimalCanonicalCoreCompilesNormalizerBidi = refl

outgoingMinimalCanonicalCoreCompilesLinearRoute :
  CanonicalLinearCore.canonicalLinearRouteCompilerOutput
    outgoingCanonicalLinearCoreBoundary
  ≡ true
outgoingMinimalCanonicalCoreCompilesLinearRoute = refl

outgoingOnlyOneActionEquationRemainsAfterMinimalCore :
  CanonicalLinearCore.onlyOneActionEquationRemainsAfterCore
    outgoingCanonicalLinearCoreBoundary
  ≡ true
outgoingOnlyOneActionEquationRemainsAfterMinimalCore = refl

outgoingMinimalCanonicalCoreStillOpen :
  CanonicalLinearCore.canonicalCoreInhabitedHere
    outgoingCanonicalLinearCoreBoundary
  ≡ false
outgoingMinimalCanonicalCoreStillOpen = refl

outgoingMinimalCoreActionEquationStillOpen :
  CanonicalLinearCore.actionIntertwiningInhabitedHere
    outgoingCanonicalLinearCoreBoundary
  ≡ false
outgoingMinimalCoreActionEquationStillOpen = refl

linearCoreCompatibilityBoundary :
  LinearCoreCompat.Trialectic369Selected3BLinearCoreCompatibilityBoundary
linearCoreCompatibilityBoundary =
  LinearCoreCompat.canonicalTrialectic369Selected3BLinearCoreCompatibilityBoundary

historicalCoreForgetsExactlyToCanonicalCore :
  LinearCoreCompat.historicalCoreForgetsToCanonicalCore
    linearCoreCompatibilityBoundary
  ≡ true
historicalCoreForgetsExactlyToCanonicalCore = refl

historicalCoreAndCanonicalCoreCompileSameRoute :
  LinearCoreCompat.historicalCoreSufficesForCanonicalRoute
    linearCoreCompatibilityBoundary
  ≡ true
historicalCoreAndCanonicalCoreCompileSameRoute = refl

------------------------------------------------------------------------
-- 6. Machine-readable remaining recognition wall.
------------------------------------------------------------------------

data IncomingAnalyticFrickeAuthority : Set where
data OptionalFiniteBasisMultiplicityProjectionDescentRecognition : Set where
data OutgoingMultiplicityInertiaAttachmentRecognition : Set where
data OutgoingInvariantFineFibreRecognition : Set where
data OutgoingMinimalSelected3BLinearCoreRecognition : Set where
data OutgoingSelected3BLinearCoreMinCutRecognition : Set where
data OutgoingSelected3BLinearCompletionRecognition : Set where
data OutgoingActualLinearMultiplicityAcquisitionRecognition : Set where
data OutgoingActualLinearHomSpaceRecognition : Set where
data OutgoingActualLinearEvaluationRecognition : Set where
data OutgoingActualInverseCocycleActionRecognition : Set where
data OrderedRankIsIntrinsicModularInvariant : Set where
data ResidualMayBeDiscarded : Set where

incomingAnalyticFrickeAuthorityStillOpenToken :
  IncomingAnalyticFrickeAuthority -> ⊥
incomingAnalyticFrickeAuthorityStillOpenToken ()

optionalFiniteBasisMultiplicityProjectionDescentStillOpenToken :
  OptionalFiniteBasisMultiplicityProjectionDescentRecognition -> ⊥
optionalFiniteBasisMultiplicityProjectionDescentStillOpenToken ()

outgoingMultiplicityInertiaAttachmentStillOpenToken :
  OutgoingMultiplicityInertiaAttachmentRecognition -> ⊥
outgoingMultiplicityInertiaAttachmentStillOpenToken ()

outgoingInvariantFineFibreRecognitionStillOpenToken :
  OutgoingInvariantFineFibreRecognition -> ⊥
outgoingInvariantFineFibreRecognitionStillOpenToken ()

outgoingMinimalSelected3BLinearCoreStillOpenToken :
  OutgoingMinimalSelected3BLinearCoreRecognition -> ⊥
outgoingMinimalSelected3BLinearCoreStillOpenToken ()

outgoingSelected3BLinearCoreMinCutStillOpenToken :
  OutgoingSelected3BLinearCoreMinCutRecognition -> ⊥
outgoingSelected3BLinearCoreMinCutStillOpenToken ()

outgoingSelected3BLinearCompletionStillOpenToken :
  OutgoingSelected3BLinearCompletionRecognition -> ⊥
outgoingSelected3BLinearCompletionStillOpenToken ()

outgoingActualLinearAcquisitionStillOpenToken :
  OutgoingActualLinearMultiplicityAcquisitionRecognition -> ⊥
outgoingActualLinearAcquisitionStillOpenToken ()

outgoingActualLinearHomSpaceStillOpenToken :
  OutgoingActualLinearHomSpaceRecognition -> ⊥
outgoingActualLinearHomSpaceStillOpenToken ()

outgoingActualLinearEvaluationStillOpenToken :
  OutgoingActualLinearEvaluationRecognition -> ⊥
outgoingActualLinearEvaluationStillOpenToken ()

outgoingActualInverseCocycleActionStillOpenToken :
  OutgoingActualInverseCocycleActionRecognition -> ⊥
outgoingActualInverseCocycleActionStillOpenToken ()

orderedRankNotPromotedToIntrinsicModularInvariant :
  OrderedRankIsIntrinsicModularInvariant -> ⊥
orderedRankNotPromotedToIntrinsicModularInvariant ()

sheet9ResidualNotDiscarded :
  ResidualMayBeDiscarded -> ⊥
sheet9ResidualNotDiscarded ()

record Trialectic369SSP15RecognitionCapstoneBoundary : Set where
  constructor trialectic-369-ssp15-recognition-capstone-boundary
  field
    participantCenteredT5QuotientPaid : Bool
    quotientTargetPhaseOrbit15TimesCanonicalSheet9 : Bool
    phaseOrbitOggBidiPaid : Bool
    presentationFactorsThroughCanonicalOggRank : Bool
    oggRoot369BidiPaid : Bool
    oggCanonical369SliceBidiPaid : Bool
    outgoingResidualIsCanonicalSheet9 : Bool
    incomingGeometricInversionAuthorityPaid : Bool
    incomingFiniteFrickeQuotientCoordinatePaid : Bool
    incomingRawFrickeActionEquivalenceRejected : Bool
    incomingStabilizerPreservingRecognitionRejected : Bool
    incomingQuotientLevelAnalyticContractOwned : Bool
    incomingAnalyticFrickeAuthorityPaid : Bool
    outgoingSecondarySheetCarrierRecognitionPaid : Bool
    outgoingActionRestrictionCompilerPaid : Bool
    outgoingInvariantFineFibreRecognitionPaid : Bool
    outgoingFineFrickeSingleFibreNoGoPaid : Bool
    outgoingFrickeStableModeBlock18CompilerPaid : Bool
    outgoingActualFineFrickeElementRecognitionPaid : Bool
    shortest3BSourceCompilesActualActionRecognition : Bool
    separateTrialecticActualActionLeafNeeded : Bool
    outgoingMultiplicityProjectionDescentCompilerPaid : Bool
    outgoingMultiplicityProjectionDescentPaid : Bool
    outgoingIndependentX6ActionRequired : Bool
    outgoingFullMultiplicityInertiaAttachmentRequired : Bool
    outgoingMultiplicityInertiaAttachmentPaid : Bool

    outgoingPureFin90MonsterRouteRefuted : Bool
    outgoingCanonicalTargetIsLinearHomSpace : Bool
    outgoingCanonicalTargetIsOneLinearAcquisition : Bool
    outgoingCanonicalTargetIsMinimalSelected3BLinearCore : Bool
    outgoingHistoricalAcquisitionCompatibilityBridgePaid : Bool
    outgoingSelected3BLinearCompletionCompilerPaid : Bool
    outgoingSelected3BSourceNativeCoreCompilerPaid : Bool
    outgoingSelected3BNormalizerCarrierBidiCompilerPaid : Bool
    outgoingSelected3BTwoFieldMinCutCompilerPaid : Bool
    outgoingSelected3BCoreMinCutCompilerPaid : Bool
    outgoingSelected3BLinearCompletionPaid : Bool
    outgoingFiniteNineEighteenRoutesAreOptionalBasisTools : Bool
    outgoingBasisSpecialisationPaid : Bool
    outgoingActualLinearAcquisitionPaid : Bool
    outgoingActualLinearHomSpacePaid : Bool
    outgoingActualLinearEvaluationPaid : Bool
    outgoingActualInverseCocycleActionPaid : Bool

    outgoingActualMonsterActionRecognitionPaid : Bool
    orderedRankIntrinsicModularInvariant : Bool
    residualDiscarded : Bool

canonicalTrialectic369SSP15RecognitionCapstoneBoundary :
  Trialectic369SSP15RecognitionCapstoneBoundary
canonicalTrialectic369SSP15RecognitionCapstoneBoundary =
  trialectic-369-ssp15-recognition-capstone-boundary
    true true true true true true true
    true true true true true false true
    true false true true false true false
    true false false false false true true
    false true true
    true true true true true false true false false false false false
    false false false

module DASHI.Analysis.RiemannG2HighestAlphaAfter369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralC3CovarianceSourceGateExact as SourceGate
import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as TargetNoGo
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as Current
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Assembly
import DASHI.Analysis.RiemannG2ExistingScalarHarmonicSameObjectAttachmentExact as Attachment
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Inventory
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- G2 HIGHEST-ALPHA FRONTIER AFTER 369 / LATER BIDI CORRECTION
--
-- The original post-369 scheduler assumed ordinary harmonic machinery existed
-- and therefore prioritized identifying a same-object scalar donor.  The later
-- repository donor inventory is stronger information: no concrete exact donor
-- on the literal target-centred G2 scalar problem is currently identified.
--
-- The live object has since been sharpened further.  DirectFinitePoleNearProducer
-- is required to carry an explicit realization of the canonical
-- LiteralTargetCenteredScalarProblem and an actual approximant/error receipt.
-- The literal delta-moment is already defined on that SAME scalar problem.
--
-- Therefore this owner is updated IN PLACE: do not schedule name-level donor
-- search or exact identity to an unidentified donor.  Recover the literal direct
-- finite producer instead.  A future exact donor remains admissible only if it
-- literally inhabits the existing same-object attachment interface.
------------------------------------------------------------------------

data Post369RHAction : Set where
  recoverLiteralConstructors
  recoverNontrivialScalarSymmetryLaw
  identifyExistingScalarDonor
  proveExactScalarProblemIdentity
  recoverLiteralDirectFiniteProducer
  : Post369RHAction

data Post369RHState : Set where
  provenanceOnly
  constructorsRecovered
  scalarLawRecovered
  donorIdentified
  sameObjectScalarAttachmentClosed
  literalDirectProducerRecovered
  : Post369RHState

nextState : Post369RHState -> Post369RHAction -> Post369RHState
nextState provenanceOnly recoverLiteralConstructors = constructorsRecovered
nextState provenanceOnly recoverNontrivialScalarSymmetryLaw = provenanceOnly
nextState provenanceOnly identifyExistingScalarDonor = provenanceOnly
nextState provenanceOnly proveExactScalarProblemIdentity = provenanceOnly
nextState provenanceOnly recoverLiteralDirectFiniteProducer = literalDirectProducerRecovered
nextState constructorsRecovered recoverLiteralConstructors = constructorsRecovered
nextState constructorsRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState constructorsRecovered identifyExistingScalarDonor = constructorsRecovered
nextState constructorsRecovered proveExactScalarProblemIdentity = constructorsRecovered
nextState constructorsRecovered recoverLiteralDirectFiniteProducer = literalDirectProducerRecovered
nextState scalarLawRecovered recoverLiteralConstructors = scalarLawRecovered
nextState scalarLawRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState scalarLawRecovered identifyExistingScalarDonor = scalarLawRecovered
nextState scalarLawRecovered proveExactScalarProblemIdentity = scalarLawRecovered
nextState scalarLawRecovered recoverLiteralDirectFiniteProducer = literalDirectProducerRecovered
nextState donorIdentified recoverLiteralConstructors = donorIdentified
nextState donorIdentified recoverNontrivialScalarSymmetryLaw = donorIdentified
nextState donorIdentified identifyExistingScalarDonor = donorIdentified
nextState donorIdentified proveExactScalarProblemIdentity = sameObjectScalarAttachmentClosed
nextState donorIdentified recoverLiteralDirectFiniteProducer = literalDirectProducerRecovered
nextState sameObjectScalarAttachmentClosed _ = sameObjectScalarAttachmentClosed
nextState literalDirectProducerRecovered _ = literalDirectProducerRecovered

currentState : Post369RHState
currentState = provenanceOnly

sourceDiagnosticAction : Post369RHAction
sourceDiagnosticAction = recoverLiteralConstructors

highestAlphaTheoremAction : Post369RHAction
highestAlphaTheoremAction = recoverLiteralDirectFiniteProducer

sourceRecoveryAloneDoesNotCloseDirectProducer :
  nextState provenanceOnly recoverLiteralConstructors
    ≡ literalDirectProducerRecovered -> ⊥
sourceRecoveryAloneDoesNotCloseDirectProducer ()

unidentifiedDonorSearchDoesNotAdvanceCurrentState :
  nextState provenanceOnly identifyExistingScalarDonor ≡ provenanceOnly
unidentifiedDonorSearchDoesNotAdvanceCurrentState = refl

legacyDonorIdentificationNeedsExactIdentity :
  nextState donorIdentified proveExactScalarProblemIdentity
    ≡ sameObjectScalarAttachmentClosed
legacyDonorIdentificationNeedsExactIdentity = refl

currentAgdaPayloadStillProvenanceOnly :
  SourceGate.currentLiteralC3SourceStage ≡ SourceGate.provenanceReturnOnly
currentAgdaPayloadStillProvenanceOnly = refl

symmetryOnlyRoutePruned :
  SourceGate.symmetryOnlyCancellationDisposition
    ≡ SourceGate.symmetryOnlyCancellationPruned
symmetryOnlyRoutePruned = refl

ordinaryHarmonicDonorInterfaceExists :
  Attachment.ordinaryHarmonicDonorAssumedAvailable
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary ≡ true
ordinaryHarmonicDonorInterfaceExists =
  Attachment.ordinaryHarmonicDonorAssumedAvailableIsTrue
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary

concreteExactDonorNotIdentified :
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventory ≡ false
concreteExactDonorNotIdentified =
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventoryIsFalse

exactProblemIdentityWouldStillBeRequiredForFutureDonor :
  Attachment.exactProblemIdentityRequired
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary ≡ true
exactProblemIdentityWouldStillBeRequiredForFutureDonor =
  Attachment.exactProblemIdentityRequiredIsTrue
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary

currentTargetCenteredSymmetryStillInsufficient :
  TargetNoGo.targetCenteredScalarCancellationClosed
    TargetNoGo.canonicalG2eTargetCenteredSymmetryNoGo ≡ false
currentTargetCenteredSymmetryStillInsufficient =
  TargetNoGo.targetCenteredScalarCancellationClosedIsFalse
    TargetNoGo.canonicalG2eTargetCenteredSymmetryNoGo

currentSignedScalarLeafStillOpen :
  G2d.signedScalarDeterminantSumBoundClosed
    G2d.canonicalG2dScalarDeterminantSumTarget ≡ false
currentSignedScalarLeafStillOpen =
  G2d.signedScalarDeterminantSumBoundClosedIsFalse
    G2d.canonicalG2dScalarDeterminantSumTarget

currentG2LeafStillOpen :
  Current.targetCenteredLocalZeroExponentialSumBoundClosed
    Current.canonicalAristotleG2CurrentCut ≡ false
currentG2LeafStillOpen =
  Current.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    Current.canonicalAristotleG2CurrentCut

literalMomentAlreadyDefinedOnCanonicalProblem :
  Assembly.literalTargetGapSecondMomentDefinedOnConsumerCarrier
    Assembly.canonicalTargetCenteredScalarCancellationBoundary ≡ true
literalMomentAlreadyDefinedOnCanonicalProblem =
  Assembly.literalTargetGapSecondMomentDefinedOnConsumerCarrierIsTrue
    Assembly.canonicalTargetCenteredScalarCancellationBoundary

post369SearchRelation : Relation.RelationKind
post369SearchRelation = Relation.provedSearchObstructionReuse

post369SearchReuse : Relation.ReuseCapability post369SearchRelation
post369SearchReuse = Relation.reuseProvedSearchObstruction

record Post369HighestAlphaBoundary : Set where
  constructor post369-highest-alpha-boundary
  field
    genericC3MachineryMissing : Bool
    genericC3MachineryMissingIsFalse : genericC3MachineryMissing ≡ false

    genericHarmonicMachineryMissing : Bool
    genericHarmonicMachineryMissingIsFalse : genericHarmonicMachineryMissing ≡ false

    currentAgdaReturnCanDecideLiteralCommonC3 : Bool
    currentAgdaReturnCanDecideLiteralCommonC3IsFalse :
      currentAgdaReturnCanDecideLiteralCommonC3 ≡ false

    sourceRecoveryIsUsefulDiagnostic : Bool
    sourceRecoveryIsUsefulDiagnosticIsTrue :
      sourceRecoveryIsUsefulDiagnostic ≡ true

    symmetryOnlyCancellationRoutePruned : Bool
    symmetryOnlyCancellationRoutePrunedIsTrue :
      symmetryOnlyCancellationRoutePruned ≡ true

    existingScalarDonorInterfaceMayBeReused : Bool
    existingScalarDonorInterfaceMayBeReusedIsTrue :
      existingScalarDonorInterfaceMayBeReused ≡ true

    concreteExactScalarDonorCurrentlyIdentified : Bool
    concreteExactScalarDonorCurrentlyIdentifiedIsFalse :
      concreteExactScalarDonorCurrentlyIdentified ≡ false

    donorNameOrPartialParameterMatchIsEnough : Bool
    donorNameOrPartialParameterMatchIsEnoughIsFalse :
      donorNameOrPartialParameterMatchIsEnough ≡ false

    exactScalarProblemIdentityIsDefaultHighestAlpha : Bool
    exactScalarProblemIdentityIsDefaultHighestAlphaIsFalse :
      exactScalarProblemIdentityIsDefaultHighestAlpha ≡ false

    literalDirectFiniteProducerIsDefaultHighestAlpha : Bool
    literalDirectFiniteProducerIsDefaultHighestAlphaIsTrue :
      literalDirectFiniteProducerIsDefaultHighestAlpha ≡ true

    literalTargetGapMomentAlreadyHasCanonicalDefinition : Bool
    literalTargetGapMomentAlreadyHasCanonicalDefinitionIsTrue :
      literalTargetGapMomentAlreadyHasCanonicalDefinition ≡ true

    symmetryRouteReopensOnlyWithExtraScalarLaw : Bool
    symmetryRouteReopensOnlyWithExtraScalarLawIsTrue :
      symmetryRouteReopensOnlyWithExtraScalarLaw ≡ true

    highestAlphaReading : String

canonicalPost369HighestAlphaBoundary : Post369HighestAlphaBoundary
canonicalPost369HighestAlphaBoundary =
  post369-highest-alpha-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    "Later BIDI evidence supersedes the old donor-search priority. The generic same-object harmonic attachment remains reusable, but the current donor inventory identifies no concrete exact donor on the literal G2 target-centred scalar problem. Therefore the default highest-alpha theorem is to recover the literal DirectFinitePoleNearProducer itself, which must realize that canonical scalar problem and carry a consumer-useful signed approximant/error. The exact delta moment M2_delta is already defined on the same scalar carrier. Donor-name search, generic phase-statistic reconstruction and second moment definitions are not live work; RH remains open."

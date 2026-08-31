module DASHI.Analysis.RiemannG2HighestAlphaAfter369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralC3CovarianceSourceGateExact as SourceGate
import DASHI.Analysis.RiemannG2C3ToScalarRouteCutExact as ScalarCut
import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as TargetNoGo
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as Current
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Assembly
import DASHI.Analysis.RiemannG2ExistingScalarHarmonicSameObjectAttachmentExact as Attachment
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- G2 HIGHEST-ALPHA FRONTIER AFTER 369/MONSTER CROSS-POLLINATION
--
-- User-directed invariant for this tranche: assume ordinary machinery already
-- exists.  That now applies both to C3/determinant algebra and to ordinary
-- Fourier/parity/moment/oscillatory machinery.
--
-- Therefore the live theorem-bearing payment is not "invent a new harmonic
-- method".  It is the exact same-object attachment between an existing scalar
-- harmonic donor and the literal G2 target-centred determinant problem.
--
-- Literal C3 constructor recovery remains diagnostic only.  It can reopen the
-- symmetry branch solely if it yields an additional scalar q/phase identity.
------------------------------------------------------------------------

data Post369RHAction : Set where
  recoverLiteralConstructors
  recoverNontrivialScalarSymmetryLaw
  identifyExistingScalarDonor
  proveExactScalarProblemIdentity
  : Post369RHAction

data Post369RHState : Set where
  provenanceOnly
  constructorsRecovered
  scalarLawRecovered
  donorIdentified
  sameObjectScalarAttachmentClosed
  : Post369RHState

nextState : Post369RHState -> Post369RHAction -> Post369RHState
nextState provenanceOnly recoverLiteralConstructors = constructorsRecovered
nextState provenanceOnly recoverNontrivialScalarSymmetryLaw = provenanceOnly
nextState provenanceOnly identifyExistingScalarDonor = donorIdentified
nextState provenanceOnly proveExactScalarProblemIdentity = provenanceOnly
nextState constructorsRecovered recoverLiteralConstructors = constructorsRecovered
nextState constructorsRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState constructorsRecovered identifyExistingScalarDonor = donorIdentified
nextState constructorsRecovered proveExactScalarProblemIdentity = constructorsRecovered
nextState scalarLawRecovered recoverLiteralConstructors = scalarLawRecovered
nextState scalarLawRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState scalarLawRecovered identifyExistingScalarDonor = donorIdentified
nextState scalarLawRecovered proveExactScalarProblemIdentity = scalarLawRecovered
nextState donorIdentified recoverLiteralConstructors = donorIdentified
nextState donorIdentified recoverNontrivialScalarSymmetryLaw = donorIdentified
nextState donorIdentified identifyExistingScalarDonor = donorIdentified
nextState donorIdentified proveExactScalarProblemIdentity = sameObjectScalarAttachmentClosed
nextState sameObjectScalarAttachmentClosed _ = sameObjectScalarAttachmentClosed

currentState : Post369RHState
currentState = provenanceOnly

sourceDiagnosticAction : Post369RHAction
sourceDiagnosticAction = recoverLiteralConstructors

highestAlphaTheoremAction : Post369RHAction
highestAlphaTheoremAction = proveExactScalarProblemIdentity

sourceRecoveryAloneDoesNotCloseSameObjectScalarAttachment :
  nextState provenanceOnly recoverLiteralConstructors
    ≡ sameObjectScalarAttachmentClosed -> ⊥
sourceRecoveryAloneDoesNotCloseSameObjectScalarAttachment ()

donorIdentificationNeedsExactIdentity :
  nextState donorIdentified proveExactScalarProblemIdentity
    ≡ sameObjectScalarAttachmentClosed
donorIdentificationNeedsExactIdentity = refl

currentAgdaPayloadStillProvenanceOnly :
  SourceGate.currentLiteralC3SourceStage ≡ SourceGate.provenanceReturnOnly
currentAgdaPayloadStillProvenanceOnly = refl

symmetryOnlyRoutePruned :
  SourceGate.symmetryOnlyCancellationDisposition
    ≡ SourceGate.symmetryOnlyCancellationPruned
symmetryOnlyRoutePruned = refl

ordinaryHarmonicDonorAssumedAvailable :
  Attachment.ordinaryHarmonicDonorAssumedAvailable
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary ≡ true
ordinaryHarmonicDonorAssumedAvailable =
  Attachment.ordinaryHarmonicDonorAssumedAvailableIsTrue
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary

exactProblemIdentityIsRequired :
  Attachment.exactProblemIdentityRequired
    Attachment.canonicalExistingScalarHarmonicAttachmentBoundary ≡ true
exactProblemIdentityIsRequired =
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

    existingScalarDonorMayBeReused : Bool
    existingScalarDonorMayBeReusedIsTrue : existingScalarDonorMayBeReused ≡ true

    donorNameOrPartialParameterMatchIsEnough : Bool
    donorNameOrPartialParameterMatchIsEnoughIsFalse :
      donorNameOrPartialParameterMatchIsEnough ≡ false

    exactScalarProblemIdentityIsDefaultHighestAlpha : Bool
    exactScalarProblemIdentityIsDefaultHighestAlphaIsTrue :
      exactScalarProblemIdentityIsDefaultHighestAlpha ≡ true

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
    true refl
    true refl
    "Assume all ordinary symmetry and harmonic-analysis machinery already exists. The post-369 RH payment is therefore an exact same-object attachment: identify an existing scalar harmonic donor's complete LiteralTargetCenteredScalarProblem with the literal G2 determinant-taper/near-zero/target/cutoff problem. Literal C3 source recovery remains diagnostic and only reopens if it yields a nontrivial scalar q/phase law. Name similarity, theorem labels, or partial parameter agreement do not close the attachment."

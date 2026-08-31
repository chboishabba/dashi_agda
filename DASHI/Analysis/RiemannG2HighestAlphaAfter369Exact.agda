module DASHI.Analysis.RiemannG2HighestAlphaAfter369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralC3CovarianceSourceGateExact as SourceGate
import DASHI.Analysis.RiemannG2C3ToScalarRouteCutExact as ScalarCut
import DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact as TargetNoGo
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as Current
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- G2 HIGHEST-ALPHA FRONTIER AFTER 369/MONSTER CROSS-POLLINATION
--
-- At this point all generic symmetry machinery is considered available.
-- The current Agda return is not constructor-rich enough to decide literal C3
-- covariance, and symmetry-only determinant invariance has already been shown
-- insufficient for signed scalar cancellation.  Therefore the active frontier
-- is a two-branch OR:
--
--   (A) source-recover the literal Lean constructors, but continue the symmetry
--       route only if they yield a nontrivial scalar q/phase law;
--   (B) attack the target-centred signed determinant-response cosine sum
--       directly.
--
-- Branch A is diagnostic; Branch B is theorem-bearing highest-alpha unless A
-- produces the additional scalar law.
------------------------------------------------------------------------

data Post369RHAction : Set where
  recoverLiteralConstructors
  recoverNontrivialScalarSymmetryLaw
  proveTargetCenteredScalarCancellation
  : Post369RHAction

data Post369RHState : Set where
  provenanceOnly
  constructorsRecovered
  scalarLawRecovered
  scalarCancellationClosed
  : Post369RHState

nextState : Post369RHState -> Post369RHAction -> Post369RHState
nextState provenanceOnly recoverLiteralConstructors = constructorsRecovered
nextState provenanceOnly recoverNontrivialScalarSymmetryLaw = provenanceOnly
nextState provenanceOnly proveTargetCenteredScalarCancellation = scalarCancellationClosed
nextState constructorsRecovered recoverLiteralConstructors = constructorsRecovered
nextState constructorsRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState constructorsRecovered proveTargetCenteredScalarCancellation = scalarCancellationClosed
nextState scalarLawRecovered recoverLiteralConstructors = scalarLawRecovered
nextState scalarLawRecovered recoverNontrivialScalarSymmetryLaw = scalarLawRecovered
nextState scalarLawRecovered proveTargetCenteredScalarCancellation = scalarCancellationClosed
nextState scalarCancellationClosed _ = scalarCancellationClosed

currentState : Post369RHState
currentState = provenanceOnly

sourceDiagnosticAction : Post369RHAction
sourceDiagnosticAction = recoverLiteralConstructors

highestAlphaTheoremAction : Post369RHAction
highestAlphaTheoremAction = proveTargetCenteredScalarCancellation

symmetryContinuationRequiresConstructorsAndScalarLaw :
  nextState constructorsRecovered recoverNontrivialScalarSymmetryLaw
    ≡ scalarLawRecovered
symmetryContinuationRequiresConstructorsAndScalarLaw = refl

sourceRecoveryAloneDoesNotCloseScalarTarget :
  nextState provenanceOnly recoverLiteralConstructors
    ≡ scalarCancellationClosed -> ⊥
sourceRecoveryAloneDoesNotCloseScalarTarget ()

currentAgdaPayloadStillProvenanceOnly :
  SourceGate.currentLiteralC3SourceStage ≡ SourceGate.provenanceReturnOnly
currentAgdaPayloadStillProvenanceOnly = refl

symmetryOnlyRoutePruned :
  SourceGate.symmetryOnlyCancellationDisposition
    ≡ SourceGate.symmetryOnlyCancellationPruned
symmetryOnlyRoutePruned = refl

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

    currentAgdaReturnCanDecideLiteralCommonC3 : Bool
    currentAgdaReturnCanDecideLiteralCommonC3IsFalse :
      currentAgdaReturnCanDecideLiteralCommonC3 ≡ false

    sourceRecoveryIsUsefulDiagnostic : Bool
    sourceRecoveryIsUsefulDiagnosticIsTrue :
      sourceRecoveryIsUsefulDiagnostic ≡ true

    sourceRecoveryAloneClosesG2d : Bool
    sourceRecoveryAloneClosesG2dIsFalse : sourceRecoveryAloneClosesG2d ≡ false

    symmetryOnlyCancellationRoutePruned : Bool
    symmetryOnlyCancellationRoutePrunedIsTrue :
      symmetryOnlyCancellationRoutePruned ≡ true

    directScalarSignedSumIsDefaultHighestAlpha : Bool
    directScalarSignedSumIsDefaultHighestAlphaIsTrue :
      directScalarSignedSumIsDefaultHighestAlpha ≡ true

    symmetryRouteReopensOnlyWithExtraScalarLaw : Bool
    symmetryRouteReopensOnlyWithExtraScalarLawIsTrue :
      symmetryRouteReopensOnlyWithExtraScalarLaw ≡ true

    highestAlphaReading : String

canonicalPost369HighestAlphaBoundary : Post369HighestAlphaBoundary
canonicalPost369HighestAlphaBoundary =
  post369-highest-alpha-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    "After exhausting generic 369/Monster symmetry transfer, the RH search tree has only two honest continuations. Recover the literal Lean nuisance/taper constructors as a diagnostic, reopening symmetry only if they imply a nontrivial scalar q/phase law; otherwise attack the target-centred signed determinant-response cosine sum directly. Existing zeta symmetries, local zero counts, and q-invariance alone are already known insufficient."

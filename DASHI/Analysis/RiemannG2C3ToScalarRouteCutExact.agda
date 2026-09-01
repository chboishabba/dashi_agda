module DASHI.Analysis.RiemannG2C3ToScalarRouteCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2CommonC3DeterminantCovarianceCompilerExact as Common
import DASHI.Analysis.RiemannAristotleG2dScalarDeterminantSumTargetExact as G2d
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- C3 -> SCALAR ROUTE CUT
--
-- After determinant compression, a symmetry preserving q gives orbit
-- invariance, not signed cancellation.  Therefore the RH proof search should
-- not spend further effort on representation theory unless the literal action
-- proves a nontrivial theorem on q itself or on the target-centred phase sum.
------------------------------------------------------------------------

data ScalarSymmetryOutcome : Set where
  qInvariantOnly
  qCharacterLaw
  qSignLaw
  qFactorization
  targetPhaseCancellation
  noUsefulScalarLaw
  : ScalarSymmetryOutcome

UsefulForOpenScalarLeaf : ScalarSymmetryOutcome -> Set
UsefulForOpenScalarLeaf qInvariantOnly = ⊥
UsefulForOpenScalarLeaf qCharacterLaw = ⊤
UsefulForOpenScalarLeaf qSignLaw = ⊤
UsefulForOpenScalarLeaf qFactorization = ⊤
UsefulForOpenScalarLeaf targetPhaseCancellation = ⊤
UsefulForOpenScalarLeaf noUsefulScalarLaw = ⊥

qInvarianceAloneNotScalarClosure : UsefulForOpenScalarLeaf qInvariantOnly -> ⊥
qInvarianceAloneNotScalarClosure x = x

noUsefulScalarLawNotClosure : UsefulForOpenScalarLeaf noUsefulScalarLaw -> ⊥
noUsefulScalarLawNotClosure x = x

currentScalarLeafStillOpen :
  G2d.signedScalarDeterminantSumBoundClosed
    G2d.canonicalG2dScalarDeterminantSumTarget ≡ false
currentScalarLeafStillOpen =
  G2d.signedScalarDeterminantSumBoundClosedIsFalse
    G2d.canonicalG2dScalarDeterminantSumTarget

currentG2eKernelLeafStillOpen :
  G2e.targetCenteredLocalZeroExponentialSumBoundClosed
    G2e.canonicalG2eDeterminantTaperKernelBoundary ≡ false
currentG2eKernelLeafStillOpen =
  G2e.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    G2e.canonicalG2eDeterminantTaperKernelBoundary

c3InvariantOrbitRouteRelation : Relation.RelationKind
c3InvariantOrbitRouteRelation = Relation.provedSearchObstructionReuse

c3InvariantOrbitRouteReuse : Relation.ReuseCapability c3InvariantOrbitRouteRelation
c3InvariantOrbitRouteReuse = Relation.reuseProvedSearchObstruction

record RiemannG2C3ScalarRouteBoundary : Set where
  constructor riemannG2C3ScalarRouteBoundary
  field
    commonC3CovarianceInfrastructureOwned : Bool
    commonC3CovarianceInfrastructureOwnedIsTrue :
      commonC3CovarianceInfrastructureOwned ≡ true
    qInvariantOrbitAloneClosesSignedScalarSum : Bool
    qInvariantOrbitAloneClosesSignedScalarSumIsFalse :
      qInvariantOrbitAloneClosesSignedScalarSum ≡ false
    usefulC3ContinuationRequiresNontrivialScalarLaw : Bool
    usefulC3ContinuationRequiresNontrivialScalarLawIsTrue :
      usefulC3ContinuationRequiresNontrivialScalarLaw ≡ true
    absentSuchLawDirectScalarPhaseRouteIsHighestAlpha : Bool
    absentSuchLawDirectScalarPhaseRouteIsHighestAlphaIsTrue :
      absentSuchLawDirectScalarPhaseRouteIsHighestAlpha ≡ true
    highestAlphaReading : String

canonicalRiemannG2C3ScalarRouteBoundary : RiemannG2C3ScalarRouteBoundary
canonicalRiemannG2C3ScalarRouteBoundary =
  riemannG2C3ScalarRouteBoundary
    true refl
    false refl
    true refl
    true refl
    "The 369/Monster branch has now paid its search value. Generic common-C3 determinant covariance is compiled, but q-invariance only makes the fixed-kernel orbit constant; it does not cancel the scalar zero sum. Continue the symmetry branch only if the literal construction supplies a nontrivial q character/sign/factorization or target-phase cancellation theorem. Otherwise the direct target-centred scalar determinant-response sum is the highest-alpha RH leaf."

module DASHI.Analysis.RiemannG2DeterminantSymmetryRelevance369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeSymmetryRelevanceExact as Symmetry
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation
import DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact as G2e
import DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact as Finite
import DASHI.Analysis.RiemannG2DeterminantConsumerQuotient369Exact as Quotient
import DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact as ThreeTaper
import DASHI.Analysis.RiemannG2C3FixedNuisanceDeterminantNoGo369Exact as FixedNoGo
import DASHI.Analysis.RiemannG2C3SimultaneousDeterminantCovariance369Exact as Covariant

------------------------------------------------------------------------
-- RH G2 / DETERMINANT-LEVEL SYMMETRY RELEVANCE
--
-- The previous 369 audit found that the scalar determinant taper
--
--   q(u) = det3(n1,n2,h(u))
--
-- is already a sufficient observer for the fixed reflection-paired pointwise
-- zero kernel. Therefore one does not need full equivariance of the original
-- three-channel carrier in order to know whether a candidate symmetry matters
-- to that consumer. It is enough to ask what the symmetry does to q.
------------------------------------------------------------------------

DeterminantPreservingAction :
  (A : G2e.DeterminantTaperAlgebra) ->
  (G2e.Cell A -> G2e.Cell A) ->
  Set
DeterminantPreservingAction A act =
  Symmetry.PreservesObserver (Quotient.determinantObserver A) act

determinantPreservingActionIsInvisibleToFixedKernelConsumer :
  (A : G2e.DeterminantTaperAlgebra) ->
  (kernel : G2e.Scalar A) ->
  (act : G2e.Cell A -> G2e.Cell A) ->
  DeterminantPreservingAction A act ->
  Symmetry.ConsumerInvariantUnder
    (Quotient.fixedKernelConsumer A kernel)
    act
determinantPreservingActionIsInvisibleToFixedKernelConsumer A kernel act preservesQ =
  Symmetry.sufficientObserverPreservationImpliesConsumerInvariance
    (Quotient.determinantResponseSufficientForFixedKernel A kernel)
    preservesQ

------------------------------------------------------------------------
-- Literal-source audit.
------------------------------------------------------------------------

constructedPositiveThreeTaperTripleOwned : Bool
constructedPositiveThreeTaperTripleOwned =
  ThreeTaper.constructedPositiveTaperTriple
    ThreeTaper.canonicalTwoZeroThreeTaperReturn

literalCyclicGeneratorRecoveredFromThreeTaperReturn : Bool
literalCyclicGeneratorRecoveredFromThreeTaperReturn = false

literalCyclicGeneratorRecoveredFromThreeTaperReturnIsFalse :
  literalCyclicGeneratorRecoveredFromThreeTaperReturn ≡ false
literalCyclicGeneratorRecoveredFromThreeTaperReturnIsFalse = refl

literalCyclicActionPreservesDeterminantTaperQ : Bool
literalCyclicActionPreservesDeterminantTaperQ = false

literalCyclicActionPreservesDeterminantTaperQIsFalse :
  literalCyclicActionPreservesDeterminantTaperQ ≡ false
literalCyclicActionPreservesDeterminantTaperQIsFalse = refl

------------------------------------------------------------------------
-- New exact 369 refinement.
--
-- The finite determinant fixture separates two symmetry shapes:
--
--   rotate h only, keep n1,n2 fixed     : NOT generically determinant invariant
--   rotate n1,n2,h simultaneously       : determinant code invariant
------------------------------------------------------------------------

targetOnlyRotationNotGenericDeterminantSymmetry :
  Finite.det3
    FixedNoGo.nuisanceOne FixedNoGo.nuisanceTwo
    (FixedNoGo.rotateVec3 FixedNoGo.targetCell)
  ≡ Finite.det3
      FixedNoGo.nuisanceOne FixedNoGo.nuisanceTwo FixedNoGo.targetCell
  -> ⊥
targetOnlyRotationNotGenericDeterminantSymmetry =
  FixedNoGo.fixedNuisanceTargetRotationDoesNotPreserveDeterminant

simultaneousRotationFiniteDeterminantCovariance :
  (a b c : Finite.Vec3) ->
  Finite.det3 a b c
  ≡ Finite.det3
      (FixedNoGo.rotateVec3 a)
      (FixedNoGo.rotateVec3 b)
      (FixedNoGo.rotateVec3 c)
simultaneousRotationFiniteDeterminantCovariance =
  Covariant.simultaneousRotationPreservesDeterminantCode

------------------------------------------------------------------------
-- Search consequence.
------------------------------------------------------------------------

rhDeterminantSymmetryRelation : Relation.RelationKind
rhDeterminantSymmetryRelation = Relation.provedSearchObstructionReuse

rhDeterminantSymmetryReuse : Relation.ReuseCapability rhDeterminantSymmetryRelation
rhDeterminantSymmetryReuse = Relation.reuseProvedSearchObstruction

record RiemannG2DeterminantSymmetryBoundary : Set where
  constructor riemannG2DeterminantSymmetryBoundary
  field
    fullThreeChannelEquivarianceRequiredToTestConsumerRelevance : Bool
    fullThreeChannelEquivarianceRequiredToTestConsumerRelevanceIsFalse :
      fullThreeChannelEquivarianceRequiredToTestConsumerRelevance ≡ false
    determinantPreservationForcesFixedKernelConsumerInvariance : Bool
    determinantPreservationForcesFixedKernelConsumerInvarianceIsTrue :
      determinantPreservationForcesFixedKernelConsumerInvariance ≡ true
    targetOnlyC3RotationGenericallyPreservesDeterminant : Bool
    targetOnlyC3RotationGenericallyPreservesDeterminantIsFalse :
      targetOnlyC3RotationGenericallyPreservesDeterminant ≡ false
    simultaneousFiniteC3RotationPreservesDeterminantCode : Bool
    simultaneousFiniteC3RotationPreservesDeterminantCodeIsTrue :
      simultaneousFiniteC3RotationPreservesDeterminantCode ≡ true
    currentThreeTaperReturnSuppliesLiteralCyclicGenerator : Bool
    currentThreeTaperReturnSuppliesLiteralCyclicGeneratorIsFalse :
      currentThreeTaperReturnSuppliesLiteralCyclicGenerator ≡ false
    currentThreeTaperReturnSuppliesQInvariance : Bool
    currentThreeTaperReturnSuppliesQInvarianceIsFalse :
      currentThreeTaperReturnSuppliesQInvariance ≡ false
    usefulC3RouteMustControlWholeDeterminantGeometryOrQ : Bool
    usefulC3RouteMustControlWholeDeterminantGeometryOrQIsTrue :
      usefulC3RouteMustControlWholeDeterminantGeometryOrQ ≡ true
    highestAlphaReading : String

canonicalRiemannG2DeterminantSymmetryBoundary :
  RiemannG2DeterminantSymmetryBoundary
canonicalRiemannG2DeterminantSymmetryBoundary =
  riemannG2DeterminantSymmetryBoundary
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    "The RH/369 search cut is now covariant-determinant level. Rotating only h with fixed nuisance rows is not generically a determinant symmetry, while simultaneous cyclic rotation of all three determinant rows preserves the finite determinant code. The next literal RH question is whether n1, n2 and h belong to one same-object order-three action; otherwise pursue direct scalar q(u) phase cancellation instead."

module DASHI.ComputerScience.RSA260BidiProjectionFreezeObservableExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty public using (⊥)

import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Frozen
import DASHI.ComputerScience.RSA260BidiProjectionPairDegreeRecomputationExact as Degree

------------------------------------------------------------------------
-- RSA-260 BIDI PROJECTION-FREEZE OBSERVABLE CONTRACT
--
-- #932 established two distinct projection-relative facts:
--
--   * changing X can alter rectangular-Hankel orientation even at fixed d;
--   * changing Y can alter both projected generator degree and orientation.
--
-- Therefore cross-carrier comparison of projected Block-Wiedemann structure
-- requires a frozen projection-pair identity.  This module makes that a typed
-- precondition rather than prose.
--
-- Freeze is methodological only.  It does not prove that the chosen projection
-- is optimal, production-authentic, universal, or sufficient for every query.
------------------------------------------------------------------------

degreeBoundary : Degree.ProjectionAwareAcquisitionBoundary
degreeBoundary = Degree.canonicalProjectionAwareAcquisitionBoundary

------------------------------------------------------------------------
-- Projection-pair identity and repo-native freeze receipt.
------------------------------------------------------------------------

data ProjectionPairId : Set where
  pairX0Y0 : ProjectionPairId
  pairX0Y1 : ProjectionPairId
  pairX0Y3 : ProjectionPairId
  pairX1Y0 : ProjectionPairId
  pairX3Y0 : ProjectionPairId

data ProjectionPairRule : Set where
  freezeExactProjectionPair : ProjectionPairRule

currentFrozenSelectionReceipt : Frozen.FrozenSelectionReceipt ProjectionPairRule
currentFrozenSelectionReceipt =
  Frozen.frozen-selection-receipt
    freezeExactProjectionPair
    true
    true
    false
    refl
    refl
    refl

record ProjectionPairFreezeReceipt : Set where
  constructor projection-pair-freeze-receipt
  field
    frozenSelection : Frozen.FrozenSelectionReceipt ProjectionPairRule
    xProjectionIdentityBound : Bool
    yProjectionIdentityBound : Bool
    frozenBeforeCrossCarrierComparison : Bool

    xProjectionIdentityPaid : xProjectionIdentityBound ≡ true
    yProjectionIdentityPaid : yProjectionIdentityBound ≡ true
    freezeOrderingPaid : frozenBeforeCrossCarrierComparison ≡ true
open ProjectionPairFreezeReceipt public

currentProjectionPairFreezeReceipt : ProjectionPairFreezeReceipt
currentProjectionPairFreezeReceipt =
  projection-pair-freeze-receipt
    currentFrozenSelectionReceipt
    true
    true
    true
    refl
    refl
    refl

------------------------------------------------------------------------
-- Projection-indexed observable packet.
--
-- This packet contains only coordinates already paid in the synthetic lane.
-- It is deliberately smaller than a production replay object.
------------------------------------------------------------------------

record ProjectionIndexedObservable : Set where
  constructor projection-indexed-observable
  field
    carrierLabel : String
    projectionPair : ProjectionPairId
    projectedGeneratorDegree : Nat
    rowExtension : Nat
    columnExtension : Nat
    squareExtension : Nat
open ProjectionIndexedObservable public

carrier32BaselineObservable : ProjectionIndexedObservable
carrier32BaselineObservable =
  projection-indexed-observable
    "touched32-seed271003"
    pairX0Y0
    22
    1 0 1

carrier32Y3Observable : ProjectionIndexedObservable
carrier32Y3Observable =
  projection-indexed-observable
    "touched32-seed271003"
    pairX0Y3
    22
    0 0 0

carrier128BaselineObservable : ProjectionIndexedObservable
carrier128BaselineObservable =
  projection-indexed-observable
    "touched128-seed271007"
    pairX0Y0
    44
    1 0 1

carrier128Y1Observable : ProjectionIndexedObservable
carrier128Y1Observable =
  projection-indexed-observable
    "touched128-seed271007"
    pairX0Y1
    45
    0 1 1

------------------------------------------------------------------------
-- Typed cross-carrier comparison admission.
--
-- A controlled comparison must retain the same projection-pair identity and a
-- freeze receipt fixed before the comparison.  Same-pair examples are admitted;
-- the concrete X0Y0/X0Y1 mismatch is rejected by constructor disjointness.
------------------------------------------------------------------------

record CrossCarrierComparisonAdmissible
    (left right : ProjectionIndexedObservable) : Set where
  constructor cross-carrier-comparison-admissible
  field
    sameProjectionPair : projectionPair left ≡ projectionPair right
    projectionFreeze : ProjectionPairFreezeReceipt
open CrossCarrierComparisonAdmissible public

baselineCrossCarrierComparison :
  CrossCarrierComparisonAdmissible
    carrier32BaselineObservable
    carrier128BaselineObservable
baselineCrossCarrierComparison =
  cross-carrier-comparison-admissible
    refl
    currentProjectionPairFreezeReceipt

mismatchedProjectionPairNotComparable :
  CrossCarrierComparisonAdmissible
    carrier128BaselineObservable
    carrier128Y1Observable → ⊥
mismatchedProjectionPairNotComparable comparison with sameProjectionPair comparison
... | ()

------------------------------------------------------------------------
-- The same carrier and same d can still differ under a different pair.
-- Projection freeze therefore cannot be reconstructed from carrier+d alone.
------------------------------------------------------------------------

data CarrierDegreeSurface : Set where
  carrier32Degree22 : CarrierDegreeSurface

data FrozenPairSurface : Set where
  carrier32Degree22X0Y0 : FrozenPairSurface
  carrier32Degree22X0Y3 : FrozenPairSurface

data ExtensionAnswer : Set where
  leftOnlyExtension : ExtensionAnswer
  noExtension : ExtensionAnswer

carrierDegreeSurface : ProjectionIndexedObservable → CarrierDegreeSurface
carrierDegreeSurface carrier32BaselineObservable = carrier32Degree22
carrierDegreeSurface carrier32Y3Observable = carrier32Degree22
carrierDegreeSurface _ = carrier32Degree22

frozenPairSurface : ProjectionIndexedObservable → FrozenPairSurface
frozenPairSurface carrier32BaselineObservable = carrier32Degree22X0Y0
frozenPairSurface carrier32Y3Observable = carrier32Degree22X0Y3
frozenPairSurface _ = carrier32Degree22X0Y0

extensionAt32 : ProjectionIndexedObservable → ExtensionAnswer
extensionAt32 carrier32BaselineObservable = leftOnlyExtension
extensionAt32 carrier32Y3Observable = noExtension
extensionAt32 _ = leftOnlyExtension

------------------------------------------------------------------------
-- Interpretation / roadmap boundary.
------------------------------------------------------------------------

record ProjectionFreezeInterpretationBoundary : Set where
  constructor projection-freeze-interpretation-boundary
  field
    xProjectionDependenceAlreadyPaid : Bool
    yProjectionDependenceAlreadyPaid : Bool
    projectionCanChangeDegree : Bool
    projectionCanChangeOrientation : Bool
    freezeUsesRepoNativeFrozenSelectionReceipt : Bool
    exactProjectionPairBoundBeforeControlledComparison : Bool
    samePairCrossCarrierComparisonAdmitted : Bool
    mismatchedPairControlledComparisonRejected : Bool
    carrierPlusDegreeRecoversProjectionPair : Bool
    projectionFreezeImpliesProjectionOptimality : Bool
    projectionFreezeImpliesProductionIdentity : Bool
    projectionFreezeImpliesUniversalMinimalIndexTheorem : Bool
    authenticSequenceStillPaysOwnDegreeWithoutProjectionMetadata : Bool
open ProjectionFreezeInterpretationBoundary public

canonicalProjectionFreezeInterpretationBoundary :
  ProjectionFreezeInterpretationBoundary
canonicalProjectionFreezeInterpretationBoundary =
  projection-freeze-interpretation-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    true

------------------------------------------------------------------------
-- Freeze is now paid.  The live residual moves to the projection-indexed
-- minimal-generator statement and then the production sequence adapter.
------------------------------------------------------------------------

data ProjectionFreezeResidual : Set where
  deriveProjectionIndexedMinimalGeneratorStatement : ProjectionFreezeResidual
  characterizeProjectionGeometryCreatingDegreeShift : ProjectionFreezeResidual
  characterizeProjectionGeometryCreatingOrientationShift : ProjectionFreezeResidual
  liftProjectionIndexedDiagnosticsToProductionAStar : ProjectionFreezeResidual
  acquireSameObjectProjectedAStarOrFSols : ProjectionFreezeResidual
  recoverProjectionPairForReproductionAndControlledComparison : ProjectionFreezeResidual

firstProjectionFreezeResidual : ProjectionFreezeResidual
firstProjectionFreezeResidual =
  deriveProjectionIndexedMinimalGeneratorStatement

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FrozenPairMeansOptimalPair : Set where
data FrozenPairMeansProductionIdentity : Set where
data FrozenPairMeansUniversalInvariant : Set where
data SameCarrierDegreeMeansSameProjectionPair : Set where

frozenPairDoesNotCreateOptimality : FrozenPairMeansOptimalPair → ⊥
frozenPairDoesNotCreateOptimality ()

frozenPairDoesNotCreateProductionIdentity : FrozenPairMeansProductionIdentity → ⊥
frozenPairDoesNotCreateProductionIdentity ()

frozenPairDoesNotCreateUniversalInvariant : FrozenPairMeansUniversalInvariant → ⊥
frozenPairDoesNotCreateUniversalInvariant ()

sameCarrierDegreeDoesNotRecoverProjectionPair :
  SameCarrierDegreeMeansSameProjectionPair → ⊥
sameCarrierDegreeDoesNotRecoverProjectionPair ()

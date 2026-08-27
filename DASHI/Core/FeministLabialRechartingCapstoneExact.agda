module DASHI.Core.FeministLabialRechartingCapstoneExact where

------------------------------------------------------------------------
-- FEMINIST RECHARTING / IRIGARAY LABIAL CAPSTONE
--
-- This module connects the new source-specific labial role chart back to the
-- existing generic PositiveRecharting theorem.  The point is to avoid a second
-- feminist recharting calculus: the inherited chart still collapses two states;
-- the labial residual distinguishes them; the existing observer lattice proves
-- strict refinement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.DifferenceWithoutHierarchyExact as Difference
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject

------------------------------------------------------------------------
-- Inherited one-coordinate chart.
------------------------------------------------------------------------

data LabialSituated : Set where
  firstSituated secondSituated : LabialSituated

data InheritedUnitaryChart : Set where
  inheritedUnit : InheritedUnitaryChart

inheritedUnitaryChart : LabialSituated → InheritedUnitaryChart
inheritedUnitaryChart firstSituated = inheritedUnit
inheritedUnitaryChart secondSituated = inheritedUnit

labialResidual : LabialSituated → Ternary.TernaryRoleCode
labialResidual firstSituated = Ternary.code1
labialResidual secondSituated = Ternary.code2

labialResidualSeparation :
  labialResidual firstSituated ≡ labialResidual secondSituated → ⊥
labialResidualSeparation ()

canonicalLabialPositiveRecharting :
  Feminist.PositiveRecharting inheritedUnitaryChart
canonicalLabialPositiveRecharting =
  Feminist.positive-recharting
    labialResidual
    firstSituated
    secondSituated
    refl
    labialResidualSeparation

labialChartStrictlyRefinesInheritedUnitaryChart :
  Observer.StrictRefinement
    inheritedUnitaryChart
    (Observer.pairObserver inheritedUnitaryChart labialResidual)
labialChartStrictlyRefinesInheritedUnitaryChart =
  Feminist.positiveRechartingStrictlyRefinesInheritedChart
    canonicalLabialPositiveRecharting

------------------------------------------------------------------------
-- The residual codes are interpreted by the Irigaray role chart, not treated
-- as Nat cardinalities.
------------------------------------------------------------------------

firstResidualRoleIsFirstLip :
  Irigaray.irigarayLabialRole (labialResidual firstSituated)
  ≡ Irigaray.firstLocalLipAspect
firstResidualRoleIsFirstLip = refl

secondResidualRoleIsSecondLip :
  Irigaray.irigarayLabialRole (labialResidual secondSituated)
  ≡ Irigaray.secondLocalLipAspect
secondResidualRoleIsSecondLip = refl

------------------------------------------------------------------------
-- Cross-owner regressions kept live in one place.
------------------------------------------------------------------------

differenceNeedNotCreateHierarchy :
  Difference.DifferenceWithEqualStanding
    Difference.modeObserver Difference.modeStanding
differenceNeedNotCreateHierarchy =
  Difference.canonicalDifferenceWithEqualStanding

representabilityDoesNotRecoverSubjectPosition :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
representabilityDoesNotRecoverSubjectPosition =
  Subject.categoryVisibilityCannotRecoverSubjectPosition

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FeministLabialCapstoneBoundary : Set where
  constructor feminist-labial-capstone-boundary
  field
    positiveRechartIsJustSignFlip : Bool
    positiveRechartIsJustSignFlipIsFalse :
      positiveRechartIsJustSignFlip ≡ false
    labialResidualCodesAreCardinalities : Bool
    labialResidualCodesAreCardinalitiesIsFalse :
      labialResidualCodesAreCardinalities ≡ false
    strictRefinementCreatesNormativeHierarchy : Bool
    strictRefinementCreatesNormativeHierarchyIsFalse :
      strictRefinementCreatesNormativeHierarchy ≡ false
    visibilityEqualsOriginatingSubjecthood : Bool
    visibilityEqualsOriginatingSubjecthoodIsFalse :
      visibilityEqualsOriginatingSubjecthood ≡ false

canonicalFeministLabialCapstoneBoundary : FeministLabialCapstoneBoundary
canonicalFeministLabialCapstoneBoundary =
  feminist-labial-capstone-boundary
    false refl
    false refl
    false refl
    false refl

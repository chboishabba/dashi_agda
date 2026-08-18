module DASHI.Governance.SituatedInverseJusticeRegression where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Governance.InverseJusticeThroughputExact as Throughput
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice

------------------------------------------------------------------------
-- Regression surface for the situated inverse-justice tranche.
------------------------------------------------------------------------

forceAloneCannotEstablishJustice :
  Justice.ForceAloneEstablishesJustice → ⊥
forceAloneCannotEstablishJustice = Justice.forceDoesNotEstablishJustice

sameInstitutionHasOppositeJusticeWitness :
  Justice.SameInstitutionOppositeJusticeWitness
sameInstitutionHasOppositeJusticeWitness =
  Justice.institutionalRoleDoesNotDetermineJusticeSign

rightsNegativeTransitionIsInverseJustice :
  Justice.InverseJusticeOperator Justice.violatingAction
rightsNegativeTransitionIsInverseJustice =
  Justice.violatingActionIsInverseJustice

rightsPreservingTransitionIsNotInverseJustice :
  Justice.InverseJusticeOperator Justice.preservingAction → ⊥
rightsPreservingTransitionIsNotInverseJustice =
  Justice.preservingActionIsNotInverseJustice

intersectionalFlatteningCannotRecoverRelationalJusticeSign :
  Intersectional.FactorsThrough
    Intersectional.flatProjection
    Intersectional.relationalOutcome →
  ⊥
intersectionalFlatteningCannotRecoverRelationalJusticeSign =
  Justice.intersectionalFlatteningCannotDetermineJusticeSign

canonicalRepeatedNegativeRun : Justice.InverseJusticeRun
canonicalRepeatedNegativeRun = Justice.canonicalTwoStepInverseJusticeRun

worsenedViolationIsInverseJustice :
  Throughput.ExtendedInverseJusticeOperator Throughput.worseningAction
worsenedViolationIsInverseJustice =
  Throughput.worsenedPositiveViolationIsInverseJustice

sloganThroughputWitness : Throughput.CoerciveJusticeThroughput
sloganThroughputWitness = Throughput.tooManyCoppersNotEnoughJusticeWitness

forcePromotionBoundaryIsClosed :
  Justice.SituatedInverseJusticeBoundary.possessionOfForceCreatesJustice
    Justice.canonicalSituatedInverseJusticeBoundary
  ≡ false
forcePromotionBoundaryIsClosed = Justice.possessionOfForceDoesNotCreateJustice

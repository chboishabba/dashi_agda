module DASHI.Governance.SituatedInverseJusticeRegression where

open import DASHI.Core.Prelude

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
  Justice.Intersectional.FactorsThrough
    Justice.Intersectional.flatProjection
    Justice.Intersectional.relationalOutcome →
  ⊥
intersectionalFlatteningCannotRecoverRelationalJusticeSign =
  Justice.intersectionalFlatteningCannotDetermineJusticeSign

canonicalRepeatedNegativeRun : Justice.InverseJusticeRun
canonicalRepeatedNegativeRun = Justice.canonicalTwoStepInverseJusticeRun

forcePromotionBoundaryIsClosed :
  Justice.SituatedInverseJusticeBoundary.possessionOfForceCreatesJustice
    Justice.canonicalSituatedInverseJusticeBoundary
  ≡ false
forcePromotionBoundaryIsClosed = Justice.possessionOfForceDoesNotCreateJustice

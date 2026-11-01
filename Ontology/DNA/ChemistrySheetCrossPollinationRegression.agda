module Ontology.DNA.ChemistrySheetCrossPollinationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.DNA.ChemistrySheetCrossPollination

open SheetCrossPollinationBoundary sheetCrossPollinationBoundary

uvFeedsQuotient-receipt : exactUVFeedsQuotient ≡ true
uvFeedsQuotient-receipt = refl

uvFeedsSignedEnergy-receipt : exactUVFeedsSignedEnergy ≡ true
uvFeedsSignedEnergy-receipt = refl

signedIsNotYetDetailTower-receipt :
  signedEnergyIsAlreadyDetailTower ≡ false
signedIsNotYetDetailTower-receipt = refl

nestingDoesNotDetermineTetration-receipt :
  fixedCarrierNestingDeterminesTetration ≡ false
nestingDoesNotDetermineTetration-receipt = refl

ternaryRequiresBound-receipt : ternaryQuantizationNeedsErrorBound ≡ true
ternaryRequiresBound-receipt = refl

phaseRequiresOperator-receipt : phaseEigenspaceNeedsOperator ≡ true
phaseRequiresOperator-receipt = refl

nonquadraticChemistryAllowed-receipt :
  chemistryTermsNeedNotAllBeQuadratic ≡ true
nonquadraticChemistryAllowed-receipt = refl

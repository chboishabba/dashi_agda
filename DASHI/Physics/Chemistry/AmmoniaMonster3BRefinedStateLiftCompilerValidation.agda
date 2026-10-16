module DASHI.Physics.Chemistry.AmmoniaMonster3BRefinedStateLiftCompilerValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BRefinedStateLiftCompilerExact as R

modelRefinementRoundTripPaid :
  (c : R.ZetaRefinedCoordinate) →
  R.modelToRefined (R.refinedToModel c) ≡ c
modelRefinementRoundTripPaid = R.refinedModelRoundTrip

modelRoundTripPaid :
  (b : R.ModelBasis) →
  R.refinedToModel (R.modelToRefined b) ≡ b
modelRoundTripPaid = R.modelRefinedRoundTrip

compilerPaid :
  R.RefinedStateLiftBoundary.refinedCoordinateToMonsterModelCompilerPaid
    R.canonicalRefinedStateLiftBoundary ≡ true
compilerPaid = refl

actualRecognitionAdapterPaid :
  R.RefinedStateLiftBoundary.actualRecognitionLiftCompilerPaid
    R.canonicalRefinedStateLiftBoundary ≡ true
actualRecognitionAdapterPaid = refl

physicalWeightAssignmentStillOpen :
  R.RefinedStateLiftBoundary.physicalNH3Base369WeightIdentificationPaid
    R.canonicalRefinedStateLiftBoundary ≡ false
physicalWeightAssignmentStillOpen = refl

physicalMultiplicityAssignmentStillOpen :
  R.RefinedStateLiftBoundary.physicalNH3MultiplicityIdentificationPaid
    R.canonicalRefinedStateLiftBoundary ≡ false
physicalMultiplicityAssignmentStillOpen = refl

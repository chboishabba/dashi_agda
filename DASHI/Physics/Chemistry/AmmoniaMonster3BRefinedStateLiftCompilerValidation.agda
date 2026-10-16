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

modelBasisCompilerPaid :
  R.RefinedStateLiftBoundary.refinedCoordinateToMonsterModelBasisCompilerPaid
    R.canonicalRefinedStateLiftBoundary ≡ true
modelBasisCompilerPaid = refl

actualBasisRecognitionAdapterPaid :
  R.RefinedStateLiftBoundary.actualBasisRecognitionLiftCompilerPaid
    R.canonicalRefinedStateLiftBoundary ≡ true
actualBasisRecognitionAdapterPaid = refl

wholeLiteralSectorFiniteLiftBlocked :
  R.RefinedStateLiftBoundary.wholeLiteralSectorFiniteLiftCompilerPaid
    R.canonicalRefinedStateLiftBoundary ≡ false
wholeLiteralSectorFiniteLiftBlocked = refl

physicalWeightAssignmentStillOpen :
  R.RefinedStateLiftBoundary.physicalNH3Base369WeightIdentificationPaid
    R.canonicalRefinedStateLiftBoundary ≡ false
physicalWeightAssignmentStillOpen = refl

physicalMultiplicityAssignmentStillOpen :
  R.RefinedStateLiftBoundary.physicalNH3MultiplicityIdentificationPaid
    R.canonicalRefinedStateLiftBoundary ≡ false
physicalMultiplicityAssignmentStillOpen = refl

literalBasisAttachmentStillOpen :
  R.RefinedStateLiftBoundary.literalMonsterBasisAttachmentInhabitedHere
    R.canonicalRefinedStateLiftBoundary ≡ false
literalBasisAttachmentStillOpen = refl

linearWZetaRecognitionStillOpen :
  R.RefinedStateLiftBoundary.linearWZetaSameObjectRecognitionPaidHere
    R.canonicalRefinedStateLiftBoundary ≡ false
linearWZetaRecognitionStillOpen = refl

dimensionOrPhaseAloneCannotCreateRefinement :
  R.RefinedStateLiftBoundary.dimensionOrPhaseAloneCreatesRefinement
    R.canonicalRefinedStateLiftBoundary ≡ false
dimensionOrPhaseAloneCannotCreateRefinement = refl

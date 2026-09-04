module DASHI.Physics.Plasma.MHDElsasserPDEProjectedFourierWeldBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE -> REPOSITORY WELD FOR INCOMPRESSIBLE ELSASSER MHD
--
-- Source-side ideal incompressible structure:
--
--   d_t z^alpha + (z^{-alpha} . grad) z^alpha = - grad P,
--   div z^alpha = 0,
--
-- with Fourier convolution p+q=k.  The repository-side exact producer is the
-- projected C3 ordered interaction
--
--   -i P_k [ (z^{-alpha}_p . q) z^alpha_q ].
--
-- This module does not identify those objects by name or resemblance.  It
-- records the exact convention/normalisation receipts required for the
-- same-object promotion.
------------------------------------------------------------------------

data ElsasserSpecies : Set where
  plusSpecies minusSpecies : ElsasserSpecies

oppositeSpecies : ElsasserSpecies → ElsasserSpecies
oppositeSpecies plusSpecies = minusSpecies
oppositeSpecies minusSpecies = plusSpecies

record SourceElsasserFourierEquation : Set₁ where
  constructor source-elsasser-fourier-equation
  field
    Mode Vector Scalar : Set
    species : ElsasserSpecies
    targetField : Mode → Vector
    transportField : Mode → Vector
    wavevectorIncidence : Mode → Mode → Mode → Set
    nonlinearFourierContribution : Mode → Mode → Mode → Vector
    divergenceFreeTarget : Set
    divergenceFreeTransport : Set
    oppositeSpeciesReceipt : Set
    convolutionReceipt : Set
    sourceReference : String

open SourceElsasserFourierEquation public

record RepositoryProjectedElsasserEquation : Set₁ where
  constructor repository-projected-elsasser-equation
  field
    Mode Vector Scalar : Set
    species : ElsasserSpecies
    targetField : Mode → Vector
    transportField : Mode → Vector
    projectedOrderedContribution : Mode → Mode → Mode → Vector
    testedTransfer : Mode → Mode → Mode → Scalar
    repositoryReference : String

open RepositoryProjectedElsasserEquation public

record PDEProjectedFourierSameObjectWeld
    (source : SourceElsasserFourierEquation)
    (repository : RepositoryProjectedElsasserEquation) : Set₁ where
  constructor pde-projected-fourier-same-object-weld
  field
    speciesIdentification : species source ≡ species repository
    targetFieldIdentification : Set
    transportFieldIdentification : Set
    oppositeSpeciesIdentification : Set

    fourierPhaseConventionReceipt : Set
    derivativeWavevectorConventionReceipt : Set
    convolutionIncidenceIdentification : Set
    pressureGradientKilledByLerayReceipt : Set
    transverseProjectorIdentification : Set
    scalarNormalizationReceipt : Set

    nonlinearContributionIdentification : Set
    testedTransferIdentification : Set
    sameObjectWeldReference : String

open PDEProjectedFourierSameObjectWeld public

record PDEProjectedFourierBidiBoundary : Set where
  constructor pde-projected-fourier-bidi-boundary
  field
    sourceFourierFormulaAutomaticallyIsRepositoryObject : Bool
    sourceFourierFormulaAutomaticallyIsRepositoryObjectIsFalse :
      sourceFourierFormulaAutomaticallyIsRepositoryObject ≡ false

    matchingPPlusQEqualsKAloneClosesWeld : Bool
    matchingPPlusQEqualsKAloneClosesWeldIsFalse :
      matchingPPlusQEqualsKAloneClosesWeld ≡ false

    pressureDisappearsWithoutProjectionReceipt : Bool
    pressureDisappearsWithoutProjectionReceiptIsFalse :
      pressureDisappearsWithoutProjectionReceipt ≡ false

    exactProjectedCancellationCanConsumeCompletedWeld : Bool
    exactProjectedCancellationCanConsumeCompletedWeldIsTrue :
      exactProjectedCancellationCanConsumeCompletedWeld ≡ true

canonicalPDEProjectedFourierBidiBoundary : PDEProjectedFourierBidiBoundary
canonicalPDEProjectedFourierBidiBoundary =
  pde-projected-fourier-bidi-boundary
    false refl false refl false refl true refl

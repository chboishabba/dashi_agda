module DASHI.Moonshine.P11BrandtHeckeHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact as Weight
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Prime
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact as Joint
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact as Power

------------------------------------------------------------------------
-- Focused regression over the current highest-alpha arithmetic producer.
------------------------------------------------------------------------

laplacianFiveIsNotAdjacencyGap :
  Spectral.p11NonzeroLaplacianEigenvalue ≡ 5
  × Spectral.p11AdjacencySpectralGap ≡ 1
laplacianFiveIsNotAdjacencyGap = refl , refl

ramanujanEll2 : Spectral.p11NontrivialEigenvalueSquare < Spectral.p11FourEll
ramanujanEll2 = Spectral.p11RamanujanSquareCertificate

geometricP11CarrierIsSourceCertified :
  Geo.sourceCertifiedSupersingularCarrierConstructed
    Geo.canonicalP11GeometricSupersingularBoundary
  ≡ true
geometricP11CarrierIsSourceCertified =
  Geo.sourceCertifiedSupersingularCarrierConstructedIsTrue
    Geo.canonicalP11GeometricSupersingularBoundary

automorphismWeightsAreDerived :
  Weight.reciprocalWeightsDerived
    Weight.canonicalP11BrandtAutomorphismWeightBoundary
  ≡ true
automorphismWeightsAreDerived =
  Weight.reciprocalWeightsDerivedIsTrue
    Weight.canonicalP11BrandtAutomorphismWeightBoundary

threePrimeBrandtGeneratorsConstructed :
  Prime.ell2IndependentPhi2GeneratorConstructed
    Prime.canonicalP11BrandtPrimeGeneratorBoundary
  ≡ true
  × Prime.ell3SourceForcedBrandtGeneratorConstructed
      Prime.canonicalP11BrandtPrimeGeneratorBoundary
    ≡ true
  × Prime.ell5SourceForcedBrandtGeneratorConstructed
      Prime.canonicalP11BrandtPrimeGeneratorBoundary
    ≡ true
threePrimeBrandtGeneratorsConstructed = refl , refl , refl

allThreeRamanujanSquares :
  Prime.allThreeRamanujanSquaresCertified
    Prime.canonicalP11BrandtPrimeGeneratorBoundary
  ≡ true
allThreeRamanujanSquares =
  Prime.allThreeRamanujanSquaresCertifiedIsTrue
    Prime.canonicalP11BrandtPrimeGeneratorBoundary

coprimeBrandtGeneratorsCommute :
  Joint.pairwiseCoprimeGeneratorCommutationConstructed
    Joint.canonicalP11BrandtJointHeckeBoundary
  ≡ true
coprimeBrandtGeneratorsCommute =
  Joint.pairwiseCoprimeGeneratorCommutationConstructedIsTrue
    Joint.canonicalP11BrandtJointHeckeBoundary

primeSquareHeckeRelationsConstructed :
  Joint.ell2PrimeSquareRelationConstructed
    Joint.canonicalP11BrandtJointHeckeBoundary
  ≡ true
  × Power.operatorLevelPrimeSquareRecurrenceConstructed
      Power.canonicalP11BrandtPrimePowerBoundary
    ≡ true
primeSquareHeckeRelationsConstructed = refl , refl

sameProjectedMatrixDoesNotPromoteGeometry :
  Joint.sameTwoStateMatrixPromotedToSameGeometricCorrespondence
    Joint.canonicalP11BrandtJointHeckeBoundary
  ≡ false
sameProjectedMatrixDoesNotPromoteGeometry =
  Joint.sameTwoStateMatrixPromotedToSameGeometricCorrespondenceIsFalse
    Joint.canonicalP11BrandtJointHeckeBoundary

internalEllipticCurveDerivationStillOpen :
  Geo.supersingularityDerivedFromInternalEllipticCurveArithmetic
    Geo.canonicalP11GeometricSupersingularBoundary
  ≡ false
internalEllipticCurveDerivationStillOpen =
  Geo.supersingularityDerivedFromInternalEllipticCurveArithmeticIsFalse
    Geo.canonicalP11GeometricSupersingularBoundary

representationJointHeckeIntertwinerStillOpen :
  Joint.representationSideJointHeckeIntertwinerConstructedHere
    Joint.canonicalP11BrandtJointHeckeBoundary
  ≡ false
representationJointHeckeIntertwinerStillOpen =
  Joint.representationSideJointHeckeIntertwinerConstructedHereIsFalse
    Joint.canonicalP11BrandtJointHeckeBoundary

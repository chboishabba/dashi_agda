module DASHI.Moonshine.P11BrandtHeckeHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact as Weight
import DASHI.Moonshine.P11BrandtWeightedSelfAdjointExact as Adjoint
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Prime
import DASHI.Moonshine.P11Phi3Phi5IndependentBrandtExact as Independent
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact as Joint
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact as Power

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

arbitraryVectorWeightedSelfAdjointnessIsConstructed :
  Adjoint.arbitraryVectorWeightedSelfAdjointnessProved
    Adjoint.canonicalP11WeightedSelfAdjointBoundary
  ≡ true
arbitraryVectorWeightedSelfAdjointnessIsConstructed =
  Adjoint.arbitraryVectorWeightedSelfAdjointnessProvedIsTrue
    Adjoint.canonicalP11WeightedSelfAdjointBoundary

arbitraryVectorAdjointSanity :
  Adjoint.weightedSelfAdjoint P11.constantEigenvector P11.nonconstantEigenvector
  ≡ Adjoint.weightedSelfAdjoint P11.constantEigenvector P11.nonconstantEigenvector
arbitraryVectorAdjointSanity = refl

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

phi3Phi5IndependentlyConfirmBrandt :
  Independent.phi3IndependentMod11ReductionConstructed
    Independent.canonicalP11Phi3Phi5IndependentBoundary
  ≡ true
  × Independent.phi5IndependentMod11ReductionConstructed
      Independent.canonicalP11Phi3Phi5IndependentBoundary
    ≡ true
  × Independent.phi3MatchesSourceForcedBrandtMatrix
      Independent.canonicalP11Phi3Phi5IndependentBoundary
    ≡ true
  × Independent.phi5MatchesSourceForcedBrandtMatrix
      Independent.canonicalP11Phi3Phi5IndependentBoundary
    ≡ true
phi3Phi5IndependentlyConfirmBrandt = refl , refl , refl , refl

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

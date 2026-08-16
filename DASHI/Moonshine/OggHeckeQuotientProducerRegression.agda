module DASHI.Moonshine.OggHeckeQuotientProducerRegression where

open import DASHI.Core.Prelude
open import Data.List.Base using (length)

import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Descent
import DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact as FiniteModel
import DASHI.Moonshine.SupportMaskCountHeckeCompressionNoGoExact as CountNoGo
import DASHI.Moonshine.OggCyclicFixedSpaceFourProbeNoGoExact as FourProbe
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact as Indexed
import DASHI.Moonshine.CandidateReductionSectorFamilyExact as Sector
import DASHI.Moonshine.SO3WeightMatchedDihedralQuotientExact as Weight
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.ClassicalHeckeQuotientDescentExact as ClassicalDescent
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as P11Spectral
import DASHI.Moonshine.P11TwoIsogenyFrobeniusNormalFormBridgeExact as P11Frobenius
import DASHI.Moonshine.P11ClassicalHeckeObservationQuotientExact as P11Observation
import DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact as Boundary

------------------------------------------------------------------------
-- Focused status checks for the current highest-alpha producer chain.
------------------------------------------------------------------------

genericPrimeCorrespondenceQuotientDescentIsConstructed :
  Descent.quotientCorrespondenceConstructedFromCongruence
    Descent.canonicalHeckeCorrespondenceQuotientBoundary
  ≡ true
genericPrimeCorrespondenceQuotientDescentIsConstructed =
  Descent.quotientCorrespondenceConstructedFromCongruenceIsTrue
    Descent.canonicalHeckeCorrespondenceQuotientBoundary

factorVecSupportMaskObservableIntertwinerIsConstructed :
  FiniteModel.observableHeckeIntertwiningProved
    FiniteModel.canonicalFactorVecSupportMaskHeckeBoundary
  ≡ true
factorVecSupportMaskObservableIntertwinerIsConstructed =
  FiniteModel.observableHeckeIntertwiningProvedIsTrue
    FiniteModel.canonicalFactorVecSupportMaskHeckeBoundary

supportCountCompressionIsRejected :
  CountNoGo.supportCountAloneDefinesHeckeQuotient
    CountNoGo.canonicalSupportCountCompressionBoundary
  ≡ false
supportCountCompressionIsRejected =
  CountNoGo.supportCountAloneDefinesHeckeQuotientIsFalse
    CountNoGo.canonicalSupportCountCompressionBoundary

fourCyclicFixedDimensionsAreRejectedAsSelector :
  FourProbe.fourProbeSignatureAloneSelectsOgg
    FourProbe.canonicalFourProbeNoGoBoundary
  ≡ false
fourCyclicFixedDimensionsAreRejectedAsSelector =
  FourProbe.fourProbeSignatureAloneSelectsOggIsFalse
    FourProbe.canonicalFourProbeNoGoBoundary

indexedFineAndCoarseFamiliesAreRepresentable :
  Indexed.levelDependentFineCarrierRepresentable
    Indexed.canonicalIndexedLevelHeckeQuotientBoundary
  ≡ true
indexedFineAndCoarseFamiliesAreRepresentable =
  Indexed.levelDependentFineCarrierRepresentableIsTrue
    Indexed.canonicalIndexedLevelHeckeQuotientBoundary

candidateReductionSectorFamilyIsConstructed :
  Sector.levelDependentReductionCarrierConstructed
    Sector.canonicalCandidateReductionSectorFamilyBoundary
  ≡ true
candidateReductionSectorFamilyIsConstructed =
  Sector.levelDependentReductionCarrierConstructedIsTrue
    Sector.canonicalCandidateReductionSectorFamilyBoundary

explicitWeightToSectorQuotientIsConstructed :
  Weight.matchedDihedralSectorQuotientConstructed
    Weight.canonicalSO3WeightMatchedDihedralBoundary
  ≡ true
explicitWeightToSectorQuotientIsConstructed =
  Weight.matchedDihedralSectorQuotientConstructedIsTrue
    Weight.canonicalSO3WeightMatchedDihedralBoundary

nineFineWeightsRemainNine : length (Weight.allSO3WeightStates 4) ≡ 9
nineFineWeightsRemainNine = Weight.j4FineWeightCountIsNine

fiveSectorTargetRemainsFive : length Sector.j4FiveSectorFamily ≡ 5
fiveSectorTargetRemainsFive = Sector.j4FiveSectorFamilyHasFiveEntries

classicalVariableDegreeCarrierIsConstructed :
  Classical.variablePrimeDegreeCarrierConstructed
    Classical.canonicalClassicalCorrespondenceBoundary
  ≡ true
classicalVariableDegreeCarrierIsConstructed =
  Classical.variablePrimeDegreeCarrierConstructedIsTrue
    Classical.canonicalClassicalCorrespondenceBoundary

classicalQuotientDescentIsConstructed :
  ClassicalDescent.classicalVariableDegreeQuotientDescentConstructed
    ClassicalDescent.canonicalClassicalHeckeQuotientBoundary
  ≡ true
classicalQuotientDescentIsConstructed =
  ClassicalDescent.classicalVariableDegreeQuotientDescentConstructedIsTrue
    ClassicalDescent.canonicalClassicalHeckeQuotientBoundary

p11DegreeThreeCorrespondenceIsConstructed :
  P11.degreeThreeCorrespondenceConstructed
    P11.canonicalP11TwoIsogenyBoundary
  ≡ true
p11DegreeThreeCorrespondenceIsConstructed =
  P11.degreeThreeCorrespondenceConstructedIsTrue
    P11.canonicalP11TwoIsogenyBoundary

p11ArithmeticGapIsFive : P11Spectral.p11ArithmeticSpectralGap ≡ 5
p11ArithmeticGapIsFive = P11Spectral.p11ArithmeticSpectralGapIsFive

p11FrobeniusNormalFormEquivarianceIsConstructed :
  P11Frobenius.correspondenceNormalFormFrobeniusEquivariant
    P11Frobenius.canonicalP11FrobeniusNormalFormBoundary
  ≡ true
p11FrobeniusNormalFormEquivarianceIsConstructed =
  P11Frobenius.correspondenceNormalFormFrobeniusEquivariantIsTrue
    P11Frobenius.canonicalP11FrobeniusNormalFormBoundary

p11CoarseObservationIsHeckeStableButNotLossless :
  P11Observation.coarseQuotientHeckeStable
    P11Observation.canonicalP11ObservationQuotientBoundary
  ≡ true
p11CoarseObservationIsHeckeStableButNotLossless =
  P11Observation.coarseQuotientHeckeStableIsTrue
    P11Observation.canonicalP11ObservationQuotientBoundary

p11CoarseObservationDropsNonconstantMode :
  P11Observation.nonconstantSpectralModeRetained
    P11Observation.canonicalP11ObservationQuotientBoundary
  ≡ false
p11CoarseObservationDropsNonconstantMode =
  P11Observation.nonconstantSpectralModeRetainedIsFalse
    P11Observation.canonicalP11ObservationQuotientBoundary

fineWeightHeckeCorrespondenceStillOpen :
  Weight.fineWeightHeckeCorrespondenceConstructedHere
    Weight.canonicalSO3WeightMatchedDihedralBoundary
  ≡ false
fineWeightHeckeCorrespondenceStillOpen =
  Weight.fineWeightHeckeCorrespondenceConstructedHereIsFalse
    Weight.canonicalSO3WeightMatchedDihedralBoundary

classicalSO3ArithmeticHeckeIntertwinerStillOpen :
  Boundary.classicalSO3ToArithmeticHeckeIntertwinerConstructed
    Boundary.canonicalSSPRepresentationHeckeBoundary
  ≡ false
classicalSO3ArithmeticHeckeIntertwinerStillOpen =
  Boundary.classicalSO3ToArithmeticHeckeIntertwinerConstructedIsFalse
    Boundary.canonicalSSPRepresentationHeckeBoundary

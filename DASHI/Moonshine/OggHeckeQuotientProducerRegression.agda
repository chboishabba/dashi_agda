module DASHI.Moonshine.OggHeckeQuotientProducerRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Descent
import DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact as FiniteModel
import DASHI.Moonshine.SupportMaskCountHeckeCompressionNoGoExact as CountNoGo
import DASHI.Moonshine.OggCyclicFixedSpaceFourProbeNoGoExact as FourProbe
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact as Indexed
import DASHI.Moonshine.CandidateReductionSectorFamilyExact as Sector
import DASHI.Moonshine.SO3WeightMatchedDihedralQuotientExact as Weight
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

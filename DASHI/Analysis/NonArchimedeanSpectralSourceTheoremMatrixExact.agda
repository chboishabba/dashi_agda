module DASHI.Analysis.NonArchimedeanSpectralSourceTheoremMatrixExact where

------------------------------------------------------------------------
-- SOURCE THEOREM / ADVERTISED CLAIM MATRIX
--
-- External Lean theorem strength remains separate from DASHI compiler output.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record SourceTheoremMatrix : Set where
  constructor sourceTheoremMatrix
  field
    functionLevelDnChiOwned : Bool
    DnPreservesTauOddOwned : Bool
    orderThreeOwned : Bool
    strongThreePowerOddCoefficientOwned : Bool
    cyclotomicOddProductOwned : Bool
    intermediateOddTraceVanishesOwned : Bool

    concreteDFTReindexOwned : Bool
    concreteDFTBasisOwned : Bool
    concreteDFTUnitarityOwned : Bool
    sourceDFTDefinitionallyEqualsOddCharacterTransform : Bool

    twistedBlockDefinedAsSheetDifference : Bool
    diagonalTauSymmetryOwned : Bool
    offDiagonalTauSymmetryOwned : Bool
    binaryZModTwoCaseSplitUsedInSource : Bool

    twistedBlockHypothesisStoresFinalMagnitude : Bool
    twistedBlockHypothesisStoresFourierMonomialWeld : Bool
    finalSpectralCircleUsesFinalMagnitudeHypothesis : Bool
    finalSpectralCircleDerivesMagnitudeFromOrbitKernel : Bool

    hadamardBlockDiagonalizationOwned : Bool
    determinantCoverFactorizationOwned : Bool
    namedSpectralTowerConclusionIsSpectrumUnion : Bool
    namedSpectralTowerConclusionIsTrueOnly : Bool

    continuousTransferDefined : Bool
    normalizedContinuousTransferDefined : Bool
    unnormalizedConstantEigenvalueTwoOwned : Bool
    normalizedConstantEigenvalueOneOwned : Bool
    twistedCircleRadiusSequenceOwned : Bool
    twistedCircleRadiusAtTwoSqrtTwoOwned : Bool
    twistedCircleRadiusConvergesOneOwned : Bool
    fullContinuousOperatorRadiusSqrtTwoOwned : Bool

    gibbsMarkovEquivalenceOwned : Bool
    branchInvariantImpliesGibbsOwned : Bool
    measureGibbsIdentityConditionalOwned : Bool
    uniqueHaarGibbsTheoremLocated : Bool

    lipschitzSupNormNonexpansionOwned : Bool
    lipschitzSemiNormNonexpansionOwned : Bool
    lipschitzTotalNormNonexpansionOwned : Bool
    essentialSpectralRadiusOneTheoremLocated : Bool

    l2MeanZeroContractionStoredAsAssumption : Bool
    l2MeanZeroInvariantTheoremLocated : Bool
    unconditionalL2MixingTheoremLocated : Bool
    correlationDecayTheoremLocated : Bool

    prolateCriticalSigmaHalfTheoremBearing : Bool
    cyclotomicProlateSameObjectWeldLocated : Bool

    undirectedGapExponentAlphaLeanOwned : Bool
    directedRadiusCriticalSigmaHalfAdvertised : Bool
    directedRadiusCriticalSigmaHalfLeanTheoremLocated : Bool

canonicalSourceTheoremMatrix : SourceTheoremMatrix
canonicalSourceTheoremMatrix =
  sourceTheoremMatrix
    true true true true true true
    true true true false
    true true true true
    true false true false
    true true false true
    true true true true true true true false
    true true true false
    true true true false
    true false false false
    true false
    true true false

record DashICompilationMatrix : Set where
  constructor dashICompilationMatrix
  field
    oddCharacterIffTauOddCompiled : Bool
    correctedOddCharacterDFTReusesExistingTheory : Bool
    binarySheetTauOddEquivalenceOwned : Bool
    concreteSourceSheetAdapterCompiledFromCheckedDefinitions : Bool
    twistedRestrictionCoreIntertwinerCompiled : Bool
    canonicalOddOrbitPackageCompiled : Bool
    signedReturnCompiled : Bool
    literalMatrixEqualityCompilesFromBasisAction : Bool
    characteristicFactorizationCompiled : Bool
    characteristicRootUnionCompiled : Bool
    spatialSpectralConsumerCompilerClosed : Bool
    literalSpectrumTowerRepoCompiled : Bool

    cyclotomicSigmaHalfCompiled : Bool
    primitiveTwistedAnchorRepairCompiled : Bool
    semilocalTwoAdicToSigmaNonDescentOwned : Bool
    cyclotomicProlateSameObjectWeldOwned : Bool
    directedSigmaHalfFromRadiusFormulaRejected : Bool

    continuousGibbsUniquenessCompiled : Bool
    continuousUnconditionalMixingCompiled : Bool

canonicalDashICompilationMatrix : DashICompilationMatrix
canonicalDashICompilationMatrix =
  dashICompilationMatrix
    true true true true true true true true true true true true
    true true true false true
    false false

finiteCoreCompilerClosed :
  DashICompilationMatrix.spatialSpectralConsumerCompilerClosed
    canonicalDashICompilationMatrix
  ≡ true
finiteCoreCompilerClosed = refl

sourceNamedTowerStillPlaceholder :
  SourceTheoremMatrix.namedSpectralTowerConclusionIsTrueOnly
    canonicalSourceTheoremMatrix
  ≡ true
sourceNamedTowerStillPlaceholder = refl

repoCompilerClosesTowerStatement :
  DashICompilationMatrix.literalSpectrumTowerRepoCompiled
    canonicalDashICompilationMatrix
  ≡ true
repoCompilerClosesTowerStatement = refl

sourceProductDFTNotOddCharacterTransform :
  SourceTheoremMatrix.sourceDFTDefinitionallyEqualsOddCharacterTransform
    canonicalSourceTheoremMatrix
  ≡ false
sourceProductDFTNotOddCharacterTransform = refl

fullContinuousRadiusSqrtTwoNotOwned :
  SourceTheoremMatrix.fullContinuousOperatorRadiusSqrtTwoOwned
    canonicalSourceTheoremMatrix
  ≡ false
fullContinuousRadiusSqrtTwoNotOwned = refl

gibbsUniquenessNotLocated :
  SourceTheoremMatrix.uniqueHaarGibbsTheoremLocated
    canonicalSourceTheoremMatrix
  ≡ false
gibbsUniquenessNotLocated = refl

l2OneStepBoundIsAssumptionBacked :
  SourceTheoremMatrix.l2MeanZeroContractionStoredAsAssumption
    canonicalSourceTheoremMatrix
  ≡ true
l2OneStepBoundIsAssumptionBacked = refl

unconditionalMixingNotLocated :
  SourceTheoremMatrix.unconditionalL2MixingTheoremLocated
    canonicalSourceTheoremMatrix
  ≡ false
unconditionalMixingNotLocated = refl

prolateHalfIsSourceTheoremBearing :
  SourceTheoremMatrix.prolateCriticalSigmaHalfTheoremBearing
    canonicalSourceTheoremMatrix
  ≡ true
prolateHalfIsSourceTheoremBearing = refl

cyclotomicProlateWeldNotLocated :
  SourceTheoremMatrix.cyclotomicProlateSameObjectWeldLocated
    canonicalSourceTheoremMatrix
  ≡ false
cyclotomicProlateWeldNotLocated = refl

undirectedAlphaIsLeanOwned :
  SourceTheoremMatrix.undirectedGapExponentAlphaLeanOwned
    canonicalSourceTheoremMatrix
  ≡ true
undirectedAlphaIsLeanOwned = refl

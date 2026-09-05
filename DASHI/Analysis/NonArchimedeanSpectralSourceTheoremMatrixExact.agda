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
    directedSigmaHalfFromRadiusFormulaRejected : Bool

canonicalDashICompilationMatrix : DashICompilationMatrix
canonicalDashICompilationMatrix =
  dashICompilationMatrix
    true true true true true true true true true true true true true

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

directedSigmaHalfNotLocatedAsLeanTheorem :
  SourceTheoremMatrix.directedRadiusCriticalSigmaHalfLeanTheoremLocated
    canonicalSourceTheoremMatrix
  ≡ false
directedSigmaHalfNotLocatedAsLeanTheorem = refl

undirectedAlphaIsLeanOwned :
  SourceTheoremMatrix.undirectedGapExponentAlphaLeanOwned
    canonicalSourceTheoremMatrix
  ≡ true
undirectedAlphaIsLeanOwned = refl

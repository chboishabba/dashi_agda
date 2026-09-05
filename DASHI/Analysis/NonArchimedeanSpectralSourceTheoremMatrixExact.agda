module DASHI.Analysis.NonArchimedeanSpectralSourceTheoremMatrixExact where

------------------------------------------------------------------------
-- SOURCE THEOREM / ADVERTISED CLAIM MATRIX
--
-- The matrix is source-strength exact.  Generic DASHI compiler output is kept
-- distinct from theorem strength in the external Lean repository.
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

canonicalSourceTheoremMatrix : SourceTheoremMatrix
canonicalSourceTheoremMatrix =
  sourceTheoremMatrix
    true true true true true true
    true true true false
    true true true true
    true false true false
    true true false true

record DashICompilationMatrix : Set where
  constructor dashICompilationMatrix
  field
    oddCharacterIffTauOddCompiled : Bool
    correctedOddCharacterDFTReusesExistingTheory : Bool
    binarySheetTauOddEquivalenceOwned : Bool
    twistedRestrictionCoreIntertwinerCompiled : Bool
    canonicalOddOrbitPackageCompiled : Bool
    orbitSumHalfPeriodCompiled : Bool
    signedReturnCompiled : Bool
    doubledReturnMinusTwoCompiled : Bool
    literalMatrixEqualityCompilesFromBasisAction : Bool
    concreteSourceSheetAdapterOwned : Bool
    spatialSpectralConsumerPromoted : Bool
    literalSpectrumTowerPromoted : Bool

canonicalDashICompilationMatrix : DashICompilationMatrix
canonicalDashICompilationMatrix =
  dashICompilationMatrix
    true true true true true true true true true false false false

singleFiniteCoreBlocker :
  DashICompilationMatrix.concreteSourceSheetAdapterOwned
    canonicalDashICompilationMatrix
  ≡ false
singleFiniteCoreBlocker = refl

spatialRemainsBlockedOnlyAtAdapter :
  DashICompilationMatrix.spatialSpectralConsumerPromoted
    canonicalDashICompilationMatrix
  ≡ false
spatialRemainsBlockedOnlyAtAdapter = refl

sourceProductDFTNotOddCharacterTransform :
  SourceTheoremMatrix.sourceDFTDefinitionallyEqualsOddCharacterTransform
    canonicalSourceTheoremMatrix
  ≡ false
sourceProductDFTNotOddCharacterTransform = refl

sourceFinalMagnitudeStillConditional :
  SourceTheoremMatrix.finalSpectralCircleDerivesMagnitudeFromOrbitKernel
    canonicalSourceTheoremMatrix
  ≡ false
sourceFinalMagnitudeStillConditional = refl

literalSpectrumTowerStillBlocked :
  DashICompilationMatrix.literalSpectrumTowerPromoted
    canonicalDashICompilationMatrix
  ≡ false
literalSpectrumTowerStillBlocked = refl

module DASHI.Analysis.NonArchimedeanSpectralSourceTheoremMatrixExact where

------------------------------------------------------------------------
-- Source theorem / advertised claim matrix.
--
-- The point is not to judge names, but to force every promoted claim to carry
-- exactly the source strength actually present in the external Lean repo, while
-- separately recording consequences that DASHI can compile from those checked
-- ingredients plus existing generic machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record SourceTheoremMatrix : Set where
  constructor sourceTheoremMatrix
  field
    characterMonomialActionOwned : Bool
    functionLevelDnChiOwned : Bool
    DnPreservesTauOddOwned : Bool
    oddCharacterIffTauOddOwned : Bool
    orderThreeOwned : Bool
    strongThreePowerOddCoefficientOwned : Bool
    cyclotomicOddProductOwned : Bool
    orbitPartitionNeedsSeparateReceipt : Bool
    intermediateOddTraceVanishesOwned : Bool

    concreteDFTReindexOwned : Bool
    concreteDFTBasisOwned : Bool
    concreteDFTUnitarityOwned : Bool
    concreteFourierConjugatedTwistedMatrixOwned : Bool
    concreteFourierConjugatedEqualsMonomialOwned : Bool

    sourceDFTRootOrderIsTwoPowNMinusTwo : Bool
    sourceDFTHasIdentityTwoFactor : Bool
    sourceDFTReindexIsCardinalityProduct : Bool
    sourceDFTDefinitionallyEqualsOddCharacterTransform : Bool

    twistedBlockHypothesisStoresFinalMagnitude : Bool
    twistedBlockHypothesisStoresFourierMonomialWeld : Bool
    finalSpectralCircleUsesFinalMagnitudeHypothesis : Bool
    finalSpectralCircleDerivesMagnitudeFromOrbitKernel : Bool

    hadamardBlockDiagonalizationOwned : Bool
    determinantCoverFactorizationOwned : Bool
    namedSpectralTowerConclusionIsSpectrumUnion : Bool
    namedSpectralTowerConclusionIsTrueOnly : Bool

    dyadicDirectLimitInjectiveOwned : Bool
    ropeRelativeInvarianceOwned : Bool
    ropeModelOptimalityOwned : Bool
    dagCoverConsumesEdgeCoveredReceipt : Bool
    depthDecaySparsityOwned : Bool
    existentialEntropyScalarOwned : Bool
    contractedBoundaryEntropySameObjectOwned : Bool

canonicalSourceTheoremMatrix : SourceTheoremMatrix
canonicalSourceTheoremMatrix =
  sourceTheoremMatrix
    true true true false true true true true true
    true true true true false
    true true true false
    true false true false
    true true false true
    true true false true false true false

record PromotionMatrix : Set where
  constructor promotionMatrix
  field
    finiteCharacterOrbitKernel : Bool
    sourceTauOddCharacterSemantics : Bool
    dashiCompiledTauOddCharacterSemantics : Bool
    intermediateSignedTraceKernel : Bool
    strongThreePowerPhaseArithmetic : Bool
    dashiCompiledFullReturnCancellation : Bool
    concreteDFTInfrastructure : Bool
    currentProductDFTOddCharacterSemantics : Bool
    correctedOddCharacterRechartRequired : Bool
    correctedOddCharacterRechartUsesExistingDFTTheory : Bool
    concreteDFTMonomialSameObject : Bool
    spatialSpectralConsumer : Bool
    determinantTowerFactorization : Bool
    literalSpectrumTower : Bool
    directLimitArchitecture : Bool
    ropeGeometry : Bool
    transformerCompressionOptimality : Bool
    arbitraryDagAdelicUniversality : Bool
    advertisedDepthSparsity : Bool
    boundaryStateAreaLaw : Bool

canonicalPromotionMatrix : PromotionMatrix
canonicalPromotionMatrix =
  promotionMatrix
    true false true true true true
    true false true true false false true false
    true true false false false false

currentProductDFTDoesNotPromoteOddCharacterSemantics :
  PromotionMatrix.currentProductDFTOddCharacterSemantics canonicalPromotionMatrix
  ≡ false
currentProductDFTDoesNotPromoteOddCharacterSemantics = refl

correctedOddCharacterRechartIsRequired :
  PromotionMatrix.correctedOddCharacterRechartRequired canonicalPromotionMatrix
  ≡ true
correctedOddCharacterRechartIsRequired = refl

correctedRechartReusesExistingDFTTheory :
  PromotionMatrix.correctedOddCharacterRechartUsesExistingDFTTheory
    canonicalPromotionMatrix
  ≡ true
correctedRechartReusesExistingDFTTheory = refl

strongThreePowerArithmeticPromotes :
  PromotionMatrix.strongThreePowerPhaseArithmetic canonicalPromotionMatrix
  ≡ true
strongThreePowerArithmeticPromotes = refl

fullReturnCancellationNowCompiles :
  PromotionMatrix.dashiCompiledFullReturnCancellation canonicalPromotionMatrix
  ≡ true
fullReturnCancellationNowCompiles = refl

spatialRemainsBlocked :
  PromotionMatrix.spatialSpectralConsumer canonicalPromotionMatrix ≡ false
spatialRemainsBlocked = refl

finiteKernelPromotes :
  PromotionMatrix.finiteCharacterOrbitKernel canonicalPromotionMatrix ≡ true
finiteKernelPromotes = refl

sourceDFTInfrastructurePromotes :
  PromotionMatrix.concreteDFTInfrastructure canonicalPromotionMatrix ≡ true
sourceDFTInfrastructurePromotes = refl

sourceOddCharacterTauOddStillNotExported :
  PromotionMatrix.sourceTauOddCharacterSemantics canonicalPromotionMatrix ≡ false
sourceOddCharacterTauOddStillNotExported = refl

dashiTauOddSemanticsCompile :
  PromotionMatrix.dashiCompiledTauOddCharacterSemantics canonicalPromotionMatrix ≡ true
dashiTauOddSemanticsCompile = refl

literalSpectrumTowerStillBlocked :
  PromotionMatrix.literalSpectrumTower canonicalPromotionMatrix ≡ false
literalSpectrumTowerStillBlocked = refl
